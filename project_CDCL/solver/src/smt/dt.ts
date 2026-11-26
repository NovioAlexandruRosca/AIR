//! Algebraic datatypes (SMT-LIB `declare-datatypes`, non-parametric).
//!
//! Decision procedure: congruence closure over the DT terms of the
//! asserted literals, rebuilt from scratch at every check (so backtracking
//! is free), saturated with the datatype rules:
//! - clash:        C(..) = D(..) with C ≠ D is a conflict;
//! - injectivity:  C(a₁..aₙ) = C(b₁..bₙ) implies aᵢ = bᵢ;
//! - selectors:    t = C(a₁..aₙ) implies selᵢ(t) = aᵢ;
//! - testers:      is-C(t) makes t = C(sel₁(t), …, selₙ(t)); ¬is-C(t)
//!   excludes C, and if one constructor is left it is used;
//! - acyclicity:   no term may (transitively) contain itself, e.g. l = cons(x, l);
//! - disequalities a ≠ b must keep a and b in different classes.
//!
//! Every merge records why (input literal, congruence, injectivity, …) so a
//! conflict or propagation can be explained by input literals only.
//!
//! Final check: a class without a constructor is split on its testers when
//! its sort is finite or a selector is applied to it (splitting on demand).

import { err, Sexp } from "./sexp";
import { Op, SortId, TermId, Terms, TheoryId, Value, BOOL } from "./term";
import { Check, Ctx, Implied, Inconsistent, Theory } from "./theory";
import { Lit, lit_new, lit_var, lit_is_positive, lit_to_dimacs } from "../lit";
import { json_string } from "../trace";
import { RustErr } from "../util";

const SNAPSHOT_CLASSES = 120;
const SNAPSHOT_NODES = 80;

/** (constructor name, [(selector, sort name)]) */
type CtorDecl = [string, [string, string][]];
/** (datatype name, constructors) */
type DtDecl = [string, CtorDecl[]];

class Ctor {
  constructor(public name: string, public fields: [string, SortId][]) {}
}

class Datatype {
  constructor(public name: string, public sort: SortId, public ctors: Ctor[], public finite: boolean) {}
}

type DtFun =
  | { kind: "Ctor"; _0: number; _1: number }
  | { kind: "Sel"; _0: number; _1: number; _2: number }
  | { kind: "Tester"; _0: number; _1: number };

type DtAtom =
  | { kind: "Eq"; var: number; a: TermId; b: TermId }
  | { kind: "Tester"; var: number; dt: number; ctor: number; t: TermId };

function DtAtom_var(a: DtAtom): number {
  return a.var;
}

type NKind =
  | { kind: "Leaf" }
  | { kind: "Ctor"; _0: number; _1: number }
  | { kind: "Sel"; _0: number; _1: number; _2: number };

/** `NKind == NKind` (derived PartialEq). */
function NKind_eq(x: NKind, y: NKind): boolean {
  if (x.kind !== y.kind) return false;
  switch (x.kind) {
    case "Leaf":
      return true;
    case "Ctor": {
      const yy = y as { kind: "Ctor"; _0: number; _1: number };
      return x._0 === yy._0 && x._1 === yy._1;
    }
    case "Sel": {
      const yy = y as { kind: "Sel"; _0: number; _1: number; _2: number };
      return x._0 === yy._0 && x._1 === yy._1 && x._2 === yy._2;
    }
  }
}

/** String key of an NKind (for the hashed congruence signature). */
function NKind_key(x: NKind): string {
  switch (x.kind) {
    case "Leaf":
      return "L";
    case "Ctor":
      return `C${x._0},${x._1}`;
    case "Sel":
      return `S${x._0},${x._1},${x._2}`;
  }
}

const LEAF: NKind = { kind: "Leaf" };
const nk_ctor = (d: number, c: number): NKind => ({ kind: "Ctor", _0: d, _1: c });

class CNode {
  constructor(public term: TermId, public kind: NKind, public children: number[]) {}
}

/** A merge and its justification: input literals plus earlier equalities. */
class Edge {
  constructor(
    public a: number,
    public b: number,
    public lits: Lit[],
    public eqs: [number, number][],
    /** rule that made the merge (asserted, congruence, injectivity, ...) */
    public rule: string,
  ) {}
}

/** Key of a `Value` for hashed sets (`HashSet<Value>`). */
function value_key(v: Value): string {
  switch (v.kind) {
    case "Bool":
      return `b${v._0}`;
    case "Int":
      return `i${v._0.toString()}`;
    case "Dt":
      return `d${v._0.length}:${v._0}(${v._1.map(value_key).join(",")})`;
  }
}

/** `format!("{sexp}")` */
function sexp_display(s: Sexp): string {
  if (s.kind === "Atom") return s._0;
  return "(" + s._0.map(sexp_display).join(" ") + ")";
}

function sexp_line(s: Sexp): number {
  return s._1;
}
function sexp_atom(s: Sexp | undefined): string | null {
  return s !== undefined && s.kind === "Atom" ? s._0 : null;
}
function sexp_list(s: Sexp | undefined): Sexp[] | null {
  return s !== undefined && s.kind === "List" ? s._0 : null;
}
function sexp_head(s: Sexp): string | null {
  const l = sexp_list(s);
  return l === null ? null : sexp_atom(l[0]);
}

/** Append a JSON string literal (trace.rs `json_string`). */
function jstr(s: string): string {
  const out = { v: "" };
  json_string(out, s);
  return out.v;
}

function mk_inconsistent(lits: Lit[], why: string): Inconsistent {
  return new Inconsistent({ lits, why });
}

function mk_implied(implied: Lit, because: Lit[], why: string): Implied {
  return new Implied({ implied, because, why });
}

/** Congruence closure with explanations. */
class Cc {
  nodes: CNode[] = [];
  node_of: Map<TermId, number> = new Map();
  root: number[] = [];
  members: number[][] = [];
  edges: Edge[] = [];
  /** root -> constructor node of the class */
  ctor_of: Map<number, number> = new Map();
  /** root -> excluded constructors (ctor index, literal, tester argument) */
  excluded: Map<number, [number, Lit, number][]> = new Map();
  diseqs: [number, number, Lit][] = [];

  static default(): Cc {
    return new Cc();
  }

  /** `*cc = Cc::default()` */
  reset(): void {
    this.nodes = [];
    this.node_of = new Map();
    this.root = [];
    this.members = [];
    this.edges = [];
    this.ctor_of = new Map();
    this.excluded = new Map();
    this.diseqs = [];
  }

  find(n: number): number {
    return this.root[n];
  }

  node(dt: Dt, terms: Terms, t: TermId): number {
    const got = this.node_of.get(t);
    if (got !== undefined) {
      return got;
    }
    const s = terms.sym(t);
    const f = s === null ? undefined : dt.funs.get(s);
    let kind: NKind;
    if (f !== undefined && f.kind === "Ctor") kind = { kind: "Ctor", _0: f._0, _1: f._1 };
    else if (f !== undefined && f.kind === "Sel") kind = { kind: "Sel", _0: f._0, _1: f._1, _2: f._2 };
    else kind = LEAF;
    const children: number[] =
      kind.kind === "Leaf" ? [] : terms.args(t).slice().map((a) => this.node(dt, terms, a));
    const n = this.nodes.length;
    this.nodes.push(new CNode(t, kind, children));
    this.node_of.set(t, n);
    this.root.push(n);
    this.members.push([n]);
    return n;
  }

  /** Merge the classes of a and b; false if already equal. */
  union(a: number, b: number, lits: Lit[], eqs: [number, number][], rule: string): boolean {
    const ra = this.find(a);
    const rb = this.find(b);
    if (ra === rb) {
      return false;
    }
    this.edges.push(new Edge(a, b, lits, eqs, rule));
    const [big, small] = this.members[ra].length >= this.members[rb].length ? [ra, rb] : [rb, ra];
    const moved = this.members[small];
    this.members[small] = [];
    for (const m of moved) {
      this.root[m] = big;
    }
    for (const m of moved) this.members[big].push(m);
    return true;
  }

  /** Input literals that justify a = b, using only edges before `limit`. */
  explain_into(a: number, b: number, limit: number, out: Lit[], done: Set<string>): void {
    if (a === b) {
      return;
    }
    const key = `${Math.min(a, b)},${Math.max(a, b)},${limit}`;
    if (done.has(key)) {
      return;
    }
    done.add(key);
    // BFS over the undirected edge graph restricted to edges[..limit].
    const adj: Map<number, [number, number][]> = new Map();
    const push = (x: number, y: [number, number]) => {
      let v = adj.get(x);
      if (v === undefined) {
        v = [];
        adj.set(x, v);
      }
      v.push(y);
    };
    for (let i = 0; i < limit; i++) {
      const e = this.edges[i];
      push(e.a, [e.b, i]);
      push(e.b, [e.a, i]);
    }
    const prev: Map<number, [number, number]> = new Map();
    const queue: number[] = [a];
    let qh = 0;
    const seen = new Set<number>([a]);
    while (qh < queue.length) {
      const x = queue[qh++];
      if (x === b) {
        break;
      }
      for (const [y, ei] of adj.get(x) ?? []) {
        if (!seen.has(y)) {
          seen.add(y);
          prev.set(y, [x, ei]);
          queue.push(y);
        }
      }
    }
    let x = b;
    while (x !== a) {
      const pe = prev.get(x);
      if (pe === undefined) {
        // debug_assert!(false, "no explanation path");
        return;
      }
      const [p, ei] = pe;
      const e = this.edges[ei];
      for (const l of e.lits) {
        if (!out.includes(l)) {
          out.push(l);
        }
      }
      for (const [u, v] of e.eqs) {
        this.explain_into(u, v, ei, out, done);
      }
      x = p;
    }
  }

  explain(pairs: [number, number][], extra: Lit[]): Lit[] {
    const out: Lit[] = extra.slice();
    const done = new Set<string>();
    for (const [a, b] of pairs) {
      this.explain_into(a, b, this.edges.length, out, done);
    }
    return out;
  }
}

type Merge = [number, number, Lit[], [number, number][], string];

export class Dt extends Theory {
  me: TheoryId = 0;
  dts: Datatype[] = [];
  funs: Map<string, DtFun> = new Map();
  sort_dt: Map<SortId, number> = new Map();
  atoms: DtAtom[] = [];
  atom_of_var: Map<number, number> = new Map();
  term_of_var: Map<number, TermId> = new Map();
  assigned: (boolean | null)[] = [];
  /** (atom, value, level) in assertion order */
  trail: [number, boolean, number][] = [];
  changed = true;
  last: Cc | null = null;
  last_event: string | null = null;

  static new(): Dt {
    return new Dt();
  }

  static default(): Dt {
    return Dt.new();
  }

  lit_label(terms: Terms, l: Lit): string {
    const t = this.term_of_var.get(lit_var(l));
    if (t !== undefined && lit_is_positive(l)) return terms.display(t);
    if (t !== undefined) return terms.display_neg(t);
    return `literal ${lit_to_dimacs(l)}`;
  }

  labels(terms: Terms, lits: Lit[]): string {
    if (lits.length === 0) {
      return "(no assumptions)";
    }
    return lits.map((l) => this.lit_label(terms, l)).join(", ");
  }

  ctor_name(d: number, c: number): string {
    return this.dts[d].ctors[c].name;
  }

  /**
   * Declare datatypes: `decls` is [(name, constructors)] where a
   * constructor is (name, [(selector, sort name)]).
   */
  declare(decls: DtDecl[], terms: Terms, line: number): void {
    const first = this.dts.length;
    for (const [name] of decls) {
      if (terms.sort_named(name) !== null) {
        return err(line, `sort '${name}' is already declared`);
      }
      const sort = terms.add_sort(name, this.me);
      this.sort_dt.set(sort, this.dts.length);
      this.dts.push(new Datatype(name, sort, [], false));
    }
    for (let k = 0; k < decls.length; k++) {
      const [name, ctors] = decls[k];
      const d = first + k;
      if (ctors.length === 0) {
        return err(line, `datatype '${name}' has no constructors`);
      }
      for (const [cname, fields] of ctors) {
        const fs: [string, SortId][] = [];
        for (const [sel, sort_name] of fields) {
          const s = terms.sort_named(sort_name);
          if (s === null) {
            return err(line, `field '${sel}': unknown sort '${sort_name}'`);
          }
          if (s === BOOL) {
            return err(line, `field '${sel}': Bool fields are not supported`);
          }
          fs.push([sel, s]);
        }
        const c = this.dts[d].ctors.length;
        for (const n of [cname, ...fs.map(([s]) => s), `is-${cname}`]) {
          if (terms.is_declared(n) || this.funs.has(n)) {
            return err(line, `'${n}' is already declared`);
          }
        }
        this.funs.set(cname, { kind: "Ctor", _0: d, _1: c });
        terms.add_fun(cname, this.me);
        for (let f = 0; f < fs.length; f++) {
          const sel = fs[f][0];
          this.funs.set(sel, { kind: "Sel", _0: d, _1: c, _2: f });
          terms.add_fun(sel, this.me);
        }
        this.funs.set(`is-${cname}`, { kind: "Tester", _0: d, _1: c });
        terms.add_fun(`is-${cname}`, this.me);
        this.dts[d].ctors.push(new Ctor(cname, fs));
      }
    }
    // A datatype is finite when it reaches neither Int nor itself.
    for (let d = 0; d < this.dts.length; d++) {
      let finite = true;
      const stack: number[] = [d];
      const seen = new Set<number>();
      outer: while (stack.length > 0) {
        const x = stack.pop()!;
        for (const c of this.dts[x].ctors) {
          for (const [, s] of c.fields) {
            const y = this.sort_dt.get(s);
            if (y === undefined) {
              finite = false;
              break outer;
            } else if (y === d) {
              finite = false;
              break outer;
            } else {
              if (!seen.has(y)) {
                seen.add(y);
                stack.push(y);
              }
            }
          }
        }
      }
      this.dts[d].finite = finite;
    }
  }

  /** Build and saturate the congruence closure for the asserted literals. */
  build(terms: Terms, cc: Cc): void {
    cc.reset();
    for (const a of this.atoms) {
      switch (a.kind) {
        case "Eq":
          cc.node(this, terms, a.a);
          cc.node(this, terms, a.b);
          break;
        case "Tester":
          cc.node(this, terms, a.t);
          break;
      }
    }
    let queue: Merge[] = [];
    const testers: [number, number, number, Lit, boolean][] = [];
    for (const [idx, val] of this.trail) {
      const lit = lit_new(DtAtom_var(this.atoms[idx]), val);
      const atom = this.atoms[idx];
      switch (atom.kind) {
        case "Eq": {
          const na = cc.node_of.get(atom.a)!;
          const nb = cc.node_of.get(atom.b)!;
          if (val) {
            queue.push([na, nb, [lit], [], "asserted"]);
          } else {
            cc.diseqs.push([na, nb, lit]);
          }
          break;
        }
        case "Tester":
          testers.push([cc.node_of.get(atom.t)!, atom.dt, atom.ctor, lit, val]);
          break;
      }
    }
    const instantiated = new Set<number>();

    for (;;) {
      let changed = false;
      const drained = queue;
      queue = [];
      for (const [a, b, lits, eqs, rule] of drained) {
        changed = cc.union(a, b, lits, eqs, rule) || changed;
      }
      // congruence
      const sig: Map<string, number> = new Map();
      for (let n = 0; n < cc.nodes.length; n++) {
        if (cc.nodes[n].kind.kind === "Leaf") {
          continue;
        }
        const key = NKind_key(cc.nodes[n].kind) + "|" + cc.nodes[n].children.map((c) => cc.find(c)).join(",");
        const m = sig.get(key);
        if (m !== undefined) {
          if (cc.find(m) !== cc.find(n)) {
            const cn = cc.nodes[n].children;
            const cm = cc.nodes[m].children;
            const eqs: [number, number][] = [];
            for (let i = 0; i < Math.min(cn.length, cm.length); i++) eqs.push([cn[i], cm[i]]);
            queue.push([n, m, [], eqs, "congruence"]);
          }
        } else {
          sig.set(key, n);
        }
      }
      // clash and injectivity
      cc.ctor_of.clear();
      for (let n = 0; n < cc.nodes.length; n++) {
        const kn = cc.nodes[n].kind;
        if (kn.kind !== "Ctor") {
          continue;
        }
        const d = kn._0;
        const c = kn._1;
        const r = cc.find(n);
        const m = cc.ctor_of.get(r);
        if (m === undefined) {
          cc.ctor_of.set(r, n);
        } else {
          const km = cc.nodes[m].kind;
          if (km.kind !== "Ctor") throw new Error("unreachable");
          const c2 = km._1;
          if (c2 !== c) {
            const lits = cc.explain([[m, n]], []);
            throw new RustErr(
              mk_inconsistent(
                lits,
                `constructor clash: ${terms.display(cc.nodes[m].term)} = ${terms.display(cc.nodes[n].term)} but ${this.ctor_name(d, c2)} and ${this.ctor_name(d, c)} are different constructors (because ${this.labels(terms, lits)})`,
              ),
            );
          }
          for (let i = 0; i < cc.nodes[n].children.length; i++) {
            const x = cc.nodes[m].children[i];
            const y = cc.nodes[n].children[i];
            if (cc.find(x) !== cc.find(y)) {
              queue.push([x, y, [], [[m, n]], "injectivity"]);
            }
          }
        }
      }
      // selectors applied to a constructor term
      for (let n = 0; n < cc.nodes.length; n++) {
        const kn = cc.nodes[n].kind;
        if (kn.kind !== "Sel") {
          continue;
        }
        const d = kn._0;
        const c = kn._1;
        const f = kn._2;
        const arg = cc.nodes[n].children[0];
        const k = cc.ctor_of.get(cc.find(arg));
        if (k !== undefined) {
          if (NKind_eq(cc.nodes[k].kind, nk_ctor(d, c))) {
            const field = cc.nodes[k].children[f];
            if (cc.find(field) !== cc.find(n)) {
              queue.push([n, field, [], [[arg, k]], "selector"]);
            }
          }
        }
      }
      // testers
      cc.excluded.clear();
      for (const [t, d, c, lit, val] of testers) {
        const r = cc.find(t);
        const kk = cc.ctor_of.get(r);
        const k = kk === undefined ? null : kk;
        if (val) {
          if (k !== null) {
            if (!NKind_eq(cc.nodes[k].kind, nk_ctor(d, c))) {
              const lits = cc.explain([[t, k]], [lit]);
              throw new RustErr(
                mk_inconsistent(
                  lits,
                  `tester clash: ${this.lit_label(terms, lit)} but ${terms.display(cc.nodes[t].term)} = ${terms.display(cc.nodes[k].term)} (because ${this.labels(terms, lits)})`,
                ),
              );
            }
          } else {
            if (!instantiated.has(r)) {
              instantiated.add(r);
              const k2 = this.instantiate(cc, terms, t, d, c);
              queue.push([t, k2, [lit], [], "tester"]);
            }
          }
        } else {
          if (k !== null && NKind_eq(cc.nodes[k].kind, nk_ctor(d, c))) {
            const lits = cc.explain([[t, k]], [lit]);
            throw new RustErr(
              mk_inconsistent(
                lits,
                `tester clash: ${this.lit_label(terms, lit)} but ${terms.display(cc.nodes[t].term)} = ${terms.display(cc.nodes[k].term)} (because ${this.labels(terms, lits)})`,
              ),
            );
          }
          let ex = cc.excluded.get(r);
          if (ex === undefined) {
            ex = [];
            cc.excluded.set(r, ex);
          }
          ex.push([c, lit, t]);
        }
      }
      // a class with every constructor but one excluded must use that one
      // NOTE: Rust iterates a HashMap here (arbitrary order); we use the
      // insertion order of the excluded map.
      const roots: number[] = [...cc.excluded.keys()];
      for (const r of roots) {
        if (cc.ctor_of.has(r) || instantiated.has(r)) {
          continue;
        }
        const excl = cc.excluded.get(r)!.slice();
        const t0 = excl[0][2];
        const d = this.sort_dt.get(terms.sort(cc.nodes[t0].term))!;
        const left: number[] = [];
        for (let c = 0; c < this.dts[d].ctors.length; c++) {
          if (!excl.some((e) => e[0] === c)) left.push(c);
        }
        const pairs: [number, number][] = excl.map((e) => [e[2], t0]);
        const lits_ex: Lit[] = excl.map((e) => e[1]);
        if (left.length === 0) {
          const lits = cc.explain(pairs, lits_ex);
          throw new RustErr(
            mk_inconsistent(
              lits,
              `${terms.display(cc.nodes[t0].term)} has no constructor left: ${this.labels(terms, lits)}`,
            ),
          );
        }
        if (left.length === 1) {
          instantiated.add(r);
          const k = this.instantiate(cc, terms, t0, d, left[0]);
          const lits = cc.explain(pairs, lits_ex);
          queue.push([t0, k, lits, [], "last constructor"]);
        }
      }
      if (!changed && queue.length === 0) {
        break;
      }
    }

    for (const [a, b, lit] of cc.diseqs) {
      if (cc.find(a) === cc.find(b)) {
        const lits = cc.explain([[a, b]], [lit]);
        throw new RustErr(
          mk_inconsistent(
            lits,
            `${this.lit_label(terms, lit)} but congruence closure derives ${terms.display(cc.nodes[a].term)} = ${terms.display(cc.nodes[b].term)} (because ${this.labels(terms, lits)})`,
          ),
        );
      }
    }
    const cycle = this.find_cycle(cc, terms);
    if (cycle !== null) {
      throw new RustErr(cycle);
    }
  }

  /** Add the term C(sel₁(t), …, selₙ(t)) and return its node. */
  instantiate(cc: Cc, terms: Terms, t: number, d: number, c: number): number {
    const tt = cc.nodes[t].term;
    const ctor = this.dts[d].ctors[c];
    const sels: TermId[] = ctor.fields.map(([sel, s]) => terms.app(sel, [tt], s));
    const term = terms.app(ctor.name, sels, this.dts[d].sort);
    return cc.node(this, terms, term);
  }

  /**
   * Occurs check: a class reachable from itself through constructor
   * arguments is a cycle such as l = cons(x, l).
   */
  find_cycle(cc: Cc, terms: Terms): Inconsistent | null {
    // root -> [(ctor node, child node)] for datatype-sorted children
    const out: Map<number, [number, number][]> = new Map();
    for (const [r, k] of cc.ctor_of) {
      for (const ch of cc.nodes[k].children) {
        if (this.sort_dt.has(terms.sort(cc.nodes[ch].term))) {
          let v = out.get(r);
          if (v === undefined) {
            v = [];
            out.set(r, v);
          }
          v.push([k, ch]);
        }
      }
    }
    // iterative DFS with colours; path keeps (root, ctor node, child node)
    const colour: Map<number, number> = new Map();
    const roots: number[] = [...out.keys()];
    roots.sort((x, y) => x - y);
    for (const start of roots) {
      if ((colour.get(start) ?? 0) !== 0) {
        continue;
      }
      const stack: [number, number][] = [[start, 0]];
      const path: [number, number, number][] = [];
      colour.set(start, 1);
      while (stack.length > 0) {
        const top = stack[stack.length - 1];
        const r = top[0];
        const edges = out.get(r) ?? [];
        if (top[1] >= edges.length) {
          colour.set(r, 2);
          stack.pop();
          path.pop();
          continue;
        }
        const [k, ch] = edges[top[1]];
        top[1] += 1;
        const next = cc.find(ch);
        const col = colour.get(next) ?? 0;
        if (col === 0) {
          colour.set(next, 1);
          path.push([r, k, ch]);
          stack.push([next, 0]);
        } else if (col === 1) {
          // cycle: from `next` along the path back to r, then r -> next
          const steps: [number, number][] = [];
          let pos = path.findIndex((p) => p[0] === next);
          if (pos < 0) pos = path.length;
          for (const p of path.slice(pos)) {
            steps.push([p[1], p[2]]);
          }
          steps.push([k, ch]);
          // step j: ctor k_j and child ch_j; ch_j ~ k_{j+1}
          const pairs: [number, number][] = [];
          for (let j = 0; j < steps.length; j++) {
            const ch_j = steps[j][1];
            const k_next = steps[(j + 1) % steps.length][0];
            pairs.push([ch_j, k_next]);
          }
          const lits = cc.explain(pairs, []);
          const chain: string[] = steps.map(([k2]) => terms.display(cc.nodes[k2].term));
          return mk_inconsistent(
            lits,
            `acyclicity: ${chain.join(" ⊃ ")} would contain itself (a datatype value cannot be its own subterm; because ${this.labels(terms, lits)})`,
          );
        }
      }
    }
    return null;
  }

  propagations(cc: Cc, terms: Terms): Implied[] {
    const out: Implied[] = [];
    for (let idx = 0; idx < this.atoms.length; idx++) {
      const atom = this.atoms[idx];
      if (this.assigned[idx] !== null) {
        continue;
      }
      switch (atom.kind) {
        case "Eq": {
          const { var: v, a, b } = atom;
          const na = cc.node_of.get(a)!;
          const nb = cc.node_of.get(b)!;
          const ra = cc.find(na);
          const rb = cc.find(nb);
          if (ra === rb) {
            const because = cc.explain([[na, nb]], []);
            out.push(
              mk_implied(
                lit_new(v, true),
                because,
                `congruence closure: ${terms.display(this.term_of_var.get(v)!)} (because ${this.labels(terms, because)})`,
              ),
            );
            continue;
          }
          const ka = cc.ctor_of.get(ra);
          const kb = cc.ctor_of.get(rb);
          if (ka !== undefined && kb !== undefined) {
            if (!NKind_eq(cc.nodes[ka].kind, cc.nodes[kb].kind)) {
              const because = cc.explain(
                [
                  [na, ka],
                  [nb, kb],
                ],
                [],
              );
              out.push(
                mk_implied(
                  lit_new(v, false),
                  because,
                  `different constructors: ${terms.display(a)} is ${terms.display(cc.nodes[ka].term)} and ${terms.display(b)} is ${terms.display(cc.nodes[kb].term)}, so ${terms.display_neg(this.term_of_var.get(v)!)}`,
                ),
              );
              continue;
            }
          }
          for (const [u, w, lit] of cc.diseqs) {
            const ru = cc.find(u);
            const rv = cc.find(w);
            let pairs: [number, number][] | null;
            if (ru === ra && rv === rb) {
              pairs = [
                [na, u],
                [nb, w],
              ];
            } else if (ru === rb && rv === ra) {
              pairs = [
                [na, w],
                [nb, u],
              ];
            } else {
              pairs = null;
            }
            if (pairs !== null) {
              const because = cc.explain(pairs, [lit]);
              out.push(
                mk_implied(
                  lit_new(v, false),
                  because,
                  `${terms.display_neg(this.term_of_var.get(v)!)} follows from ${this.lit_label(terms, lit)} (because ${this.labels(terms, because)})`,
                ),
              );
              break;
            }
          }
          break;
        }
        case "Tester": {
          const { var: v, dt, ctor, t } = atom;
          const nt = cc.node_of.get(t)!;
          const r = cc.find(nt);
          const k = cc.ctor_of.get(r);
          if (k !== undefined) {
            const yes = NKind_eq(cc.nodes[k].kind, nk_ctor(dt, ctor));
            const because = cc.explain([[nt, k]], []);
            out.push(
              mk_implied(
                lit_new(v, yes),
                because,
                `${terms.display(t)} = ${terms.display(cc.nodes[k].term)}, so ${this.lit_label(terms, lit_new(v, yes))}`,
              ),
            );
          } else {
            const ex = cc.excluded.get(r);
            const e = ex === undefined ? undefined : ex.find((e) => e[0] === ctor);
            if (e !== undefined) {
              const [, lit, t2] = e;
              const because = cc.explain([[nt, t2]], [lit]);
              out.push(
                mk_implied(
                  lit_new(v, false),
                  because,
                  `${terms.display_neg(this.term_of_var.get(v)!)} because ${this.labels(terms, because)}`,
                ),
              );
            }
          }
          break;
        }
      }
    }
    return out;
  }

  /**
   * Final check: a class that must be built by a constructor but has
   * none yet gets a tester split.
   */
  split(cc: Cc, ctx: Ctx): [Lit, string] | null {
    const has_sel = new Set<number>();
    for (const n of cc.nodes) {
      if (n.kind.kind === "Sel") {
        has_sel.add(cc.find(n.children[0]));
      }
    }
    const roots: number[] = [];
    for (let n = 0; n < cc.nodes.length; n++) if (cc.find(n) === n) roots.push(n);
    const minTerm = (r: number) => Math.min(...cc.members[r].map((m) => cc.nodes[m].term));
    const keys = new Map<number, number>(roots.map((r) => [r, minTerm(r)]));
    roots.sort((x, y) => keys.get(x)! - keys.get(y)!);
    for (const r of roots) {
      if (cc.ctor_of.has(r)) {
        continue;
      }
      // min_by_key returns the first minimum
      let rep = cc.members[r][0];
      for (const m of cc.members[r]) {
        if (cc.nodes[m].term < cc.nodes[rep].term) rep = m;
      }
      const t = cc.nodes[rep].term;
      const d = this.sort_dt.get(ctx.terms.sort(t));
      if (d === undefined) {
        continue;
      }
      const finite = this.dts[d].finite;
      if (!finite && !has_sel.has(r)) {
        continue;
      }
      const exv = cc.excluded.get(r);
      const excluded: number[] = exv === undefined ? [] : exv.map((e) => e[0]);
      // Prefer constructors that do not recurse into the same sort.
      const sort = this.dts[d].sort;
      const order: number[] = [];
      for (let c = 0; c < this.dts[d].ctors.length; c++) if (!excluded.includes(c)) order.push(c);
      const rec = (c: number) => (this.dts[d].ctors[c].fields.some((f) => f[1] === sort) ? 1 : 0);
      order.sort((x, y) => rec(x) - rec(y));
      if (order.length === 0) continue;
      const c = order[0];
      const tester = ctx.terms.app(`is-${this.ctor_name(d, c)}`, [t], BOOL);
      const lit = ctx.lit(tester, true);
      const reason = finite
        ? `${this.dts[d].name} is a finite datatype`
        : `a selector is applied to ${ctx.terms.display(t)}`;
      const why = `datatype split: ${ctx.terms.display(t)} must be built by one of the constructors of ${this.dts[d].name} (${reason}); try ${this.ctor_name(d, c)} first`;
      return [lit, why];
    }
    return null;
  }

  /** A value of sort `d` that differs from every value in `used`. */
  fresh_value(d: number, excluded: number[], fresh_int: { v: bigint }, used: Set<string>, depth: number): Value {
    const sort = this.dts[d].sort;
    let order: number[] = [];
    for (let c = 0; c < this.dts[d].ctors.length; c++) if (!excluded.includes(c)) order.push(c);
    if (order.length === 0) {
      order = [];
      for (let c = 0; c < this.dts[d].ctors.length; c++) order.push(c);
    }
    // Non-recursive constructors first, unless we need depth to be fresh.
    const rec = (c: number) => (this.dts[d].ctors[c].fields.some((f) => f[1] === sort) ? 1 : 0);
    order.sort((x, y) => rec(x) - rec(y));
    for (const c of order) {
      const v = this.build_value(d, c, fresh_int, depth);
      if (!used.has(value_key(v))) {
        return v;
      }
    }
    // Go deeper through a recursive constructor.
    if (depth < 64) {
      return this.fresh_value(d, excluded, fresh_int, used, depth + 1);
    }
    return this.build_value(d, order[0], fresh_int, 0);
  }

  build_value(d: number, c: number, fresh_int: { v: bigint }, depth: number): Value {
    const ctor = this.dts[d].ctors[c];
    const args: Value[] = [];
    for (const [, s] of ctor.fields) {
      const d2 = this.sort_dt.get(s);
      if (d2 === undefined) {
        fresh_int.v += 1n;
        args.push({ kind: "Int", _0: fresh_int.v });
      } else {
        const sort2 = this.dts[d2].sort;
        const order: number[] = [];
        for (let k = 0; k < this.dts[d2].ctors.length; k++) order.push(k);
        const rec = (k: number) => (this.dts[d2].ctors[k].fields.some((f) => f[1] === sort2) ? 1 : 0);
        order.sort((x, y) => rec(x) - rec(y));
        const k = depth > 0 ? order[order.length - 1] : order[0];
        args.push(this.build_value(d2, k, fresh_int, Math.max(depth - 1, 0)));
      }
    }
    return { kind: "Dt", _0: ctor.name, _1: args };
  }

  // ------------------------------------------------------------ Theory

  name(): string {
    return "DT";
  }

  init(_terms: Terms, me: TheoryId): void {
    this.me = me;
  }

  command(cmd: Sexp, terms: Terms, me: TheoryId): boolean {
    this.me = me;
    const line = sexp_line(cmd);
    const items = sexp_list(cmd) ?? [];
    const head = sexp_head(cmd) ?? "";
    const parse_ctor = (c: Sexp): CtorDecl => {
      if (c.kind === "Atom") {
        return [c._0, []];
      }
      const parts = c._0;
      const l = c._1;
      const name = sexp_atom(parts[0]);
      if (name === null) {
        return err(l, "constructor name expected");
      }
      const fields: [string, string][] = [];
      for (const f of parts.slice(1)) {
        const fl = sexp_list(f);
        if (fl !== null && fl.length === 2 && fl[0].kind === "Atom" && fl[1].kind === "Atom") {
          fields.push([fl[0]._0, fl[1]._0]);
        } else {
          return err(sexp_line(f), `field must be (selector Sort), got ${sexp_display(f)}`);
        }
      }
      return [name, fields];
    };
    switch (head) {
      case "declare-datatype": {
        const name = sexp_atom(items[1]);
        const ctors = sexp_list(items[2]);
        if (name === null || ctors === null) {
          return err(line, "usage: (declare-datatype Name ((ctor (sel Sort) ...) ...))");
        }
        const cs = ctors.map(parse_ctor);
        this.declare([[name, cs]], terms, line);
        return true;
      }
      case "declare-datatypes": {
        const sorts = sexp_list(items[1]);
        const bodies = sexp_list(items[2]);
        if (sorts === null || bodies === null) {
          return err(line, "usage: (declare-datatypes ((Name 0) ...) (((ctor (sel Sort) ...) ...) ...))");
        }
        const decls: DtDecl[] = [];
        if (sorts.length === 0) {
          // SMT-LIB 2.5 style: (declare-datatypes () ((Name ctor ...) ...))
          for (const b of bodies) {
            const parts = sexp_list(b) ?? [];
            const name = sexp_atom(parts[0]);
            if (name === null) {
              return err(sexp_line(b), "datatype name expected");
            }
            const cs = parts.slice(1).map(parse_ctor);
            decls.push([name, cs]);
          }
        } else {
          if (sorts.length !== bodies.length) {
            return err(line, "declare-datatypes: number of sorts and bodies differ");
          }
          for (let i = 0; i < sorts.length; i++) {
            const s = sorts[i];
            const b = bodies[i];
            const sl = sexp_list(s);
            let name: string;
            let arity: string;
            if (sl !== null && sl.length === 2 && sl[0].kind === "Atom" && sl[1].kind === "Atom") {
              name = sl[0]._0;
              arity = sl[1]._0;
            } else {
              return err(sexp_line(s), `expected (Name 0), got ${sexp_display(s)}`);
            }
            if (arity !== "0") {
              return err(sexp_line(s), `parametric datatype '${name}' is not supported`);
            }
            if (sexp_head(b) === "par") {
              return err(sexp_line(b), "parametric datatypes (par ...) are not supported");
            }
            const ctors = sexp_list(b) ?? [];
            const cs = ctors.map(parse_ctor);
            decls.push([name, cs]);
          }
        }
        this.declare(decls, terms, line);
        return true;
      }
      default:
        return false;
    }
  }

  mk_app(sym: string, args: TermId[], terms: Terms): TermId {
    const f = this.funs.get(sym);
    if (f === undefined) {
      throw new RustErr(`unknown datatype symbol '${sym}'`);
    }
    const check_arg = (terms: Terms, args: TermId[], d: number): void => {
      if (args.length !== 1) {
        throw new RustErr(`'${sym}' takes one argument`);
      }
      if (terms.sort(args[0]) !== this.dts[d].sort) {
        throw new RustErr(
          `'${sym}' expects a ${this.dts[d].name}, got ${terms.display(args[0])} : ${terms.sort_name(terms.sort(args[0]))}`,
        );
      }
    };
    switch (f.kind) {
      case "Ctor": {
        const d = f._0;
        const ctor = this.dts[d].ctors[f._1];
        if (args.length !== ctor.fields.length) {
          throw new RustErr(`constructor '${sym}' takes ${ctor.fields.length} argument(s), got ${args.length}`);
        }
        for (let i = 0; i < args.length; i++) {
          const a = args[i];
          const [sel, s] = ctor.fields[i];
          if (terms.sort(a) !== s) {
            throw new RustErr(
              `'${sym}': field '${sel}' needs ${terms.sort_name(s)}, got ${terms.display(a)} : ${terms.sort_name(terms.sort(a))}`,
            );
          }
        }
        return terms.app(sym, args, this.dts[d].sort);
      }
      case "Sel": {
        check_arg(terms, args, f._0);
        return terms.app(sym, args, this.dts[f._0].ctors[f._1].fields[f._2][1]);
      }
      case "Tester": {
        check_arg(terms, args, f._0);
        return terms.app(sym, args, BOOL);
      }
    }
  }

  register_atom(v: number, atom: TermId, ctx: Ctx): void {
    const node = ctx.terms.node(atom);
    const op: Op = node.op;
    const args = node.args.slice();
    let a: DtAtom;
    if (op.kind === "App" && op._0 === "=" && args.length === 2) {
      a = { kind: "Eq", var: v, a: args[0], b: args[1] };
    } else if (op.kind === "App" && args.length === 1) {
      const f = this.funs.get(op._0);
      if (f !== undefined && f.kind === "Tester") {
        a = { kind: "Tester", var: v, dt: f._0, ctor: f._1, t: args[0] };
      } else {
        throw new RustErr(`DT cannot interpret ${ctx.terms.display(atom)}`);
      }
    } else {
      throw new RustErr(`DT cannot interpret ${ctx.terms.display(atom)}`);
    }
    this.atom_of_var.set(v, this.atoms.length);
    this.term_of_var.set(v, atom);
    this.atoms.push(a);
    this.assigned.push(null);
    this.changed = true;
  }

  assert_lit(v: number, value: boolean, level: number): void {
    const idx = this.atom_of_var.get(v);
    if (idx === undefined) {
      return;
    }
    if (this.assigned[idx] !== null) {
      return;
    }
    this.assigned[idx] = value;
    this.trail.push([idx, value, level]);
    this.changed = true;
  }

  backtrack(level: number): void {
    while (this.trail.length > 0) {
      const [idx, , l] = this.trail[this.trail.length - 1];
      if (l <= level) {
        break;
      }
      this.trail.pop();
      this.assigned[idx] = null;
      this.changed = true;
    }
  }

  check(ctx: Ctx, final_check: boolean): Check {
    const out = new Check();
    if (this.atoms.length === 0) {
      return out;
    }
    const cc = Cc.default();
    let conflict: Inconsistent | null = null;
    try {
      this.build(ctx.terms, cc);
    } catch (x) {
      if (!(x instanceof RustErr)) throw x;
      conflict = x.value as Inconsistent;
    }
    if (conflict !== null) {
      this.last_event = conflict.why;
      // Keep the closure: the UI shows the classes behind the conflict.
      this.last = cc;
      out.conflict = conflict;
    } else {
      out.propagations = this.propagations(cc, ctx.terms);
      if (final_check && out.propagations.length === 0) {
        const sp = this.split(cc, ctx);
        if (sp !== null) {
          const [lit, why] = sp;
          this.last_event = why;
          out.split = [lit, why];
        }
      }
      this.last = cc;
    }
    return out;
  }

  model(terms: Terms, known: Map<TermId, Value>): void {
    const cc = Cc.default();
    try {
      this.build(terms, cc);
    } catch (x) {
      if (!(x instanceof RustErr)) throw x;
      return;
    }
    let mx: bigint | null = null;
    for (const v of known.values()) {
      if (v.kind === "Int" && (mx === null || v._0 > mx)) mx = v._0;
    }
    let base = mx === null ? 0n : mx;
    if (base < 0n) base = 0n;
    const fresh_int = { v: base + 100n };
    const used = new Set<string>();
    const val: Map<number, Value> = new Map();

    // Int classes: the value LIA chose for a member, else a fresh one.
    const roots: number[] = [];
    for (let n = 0; n < cc.nodes.length; n++) if (cc.find(n) === n) roots.push(n);
    for (const r of roots) {
      const t = cc.nodes[r].term;
      if (this.sort_dt.has(terms.sort(t))) {
        continue;
      }
      let v: Value | undefined;
      for (const m of cc.members[r]) {
        v = known.get(cc.nodes[m].term);
        if (v !== undefined) break;
      }
      if (v === undefined) {
        fresh_int.v += 1n;
        v = { kind: "Int", _0: fresh_int.v };
      }
      val.set(r, v);
    }
    // Datatype classes: constructor classes bottom-up (acyclic), the
    // rest get fresh values distinct from everything else.
    const evalr = (dt: Dt, cc: Cc, r: number, val: Map<number, Value>, pending: number[]): Value | null => {
      const got = val.get(r);
      if (got !== undefined) {
        return got;
      }
      const k = cc.ctor_of.get(r);
      if (k === undefined) return null;
      const kn = cc.nodes[k].kind;
      if (kn.kind !== "Ctor") {
        return null;
      }
      const args: Value[] = [];
      for (const ch of cc.nodes[k].children) {
        const v = evalr(dt, cc, cc.find(ch), val, pending);
        if (v !== null) {
          args.push(v);
        } else {
          pending.push(cc.find(ch));
          return null;
        }
      }
      const v: Value = { kind: "Dt", _0: dt.ctor_name(kn._0, kn._1), _1: args };
      val.set(r, v);
      return v;
    };
    const pending: number[] = [];
    for (const r of roots) {
      evalr(this, cc, r, val, pending);
    }
    for (const v of val.values()) {
      used.add(value_key(v));
    }
    const free: number[] = roots.filter((r) => !val.has(r) && !cc.ctor_of.has(r));
    free.sort((x, y) => x - y);
    for (const r of free) {
      const d = this.sort_dt.get(terms.sort(cc.nodes[r].term))!;
      const exv = cc.excluded.get(r);
      const excluded: number[] = exv === undefined ? [] : exv.map((e) => e[0]);
      const v = this.fresh_value(d, excluded, fresh_int, used, 0);
      used.add(value_key(v));
      val.set(r, v);
    }
    for (const r of roots) {
      const p: number[] = [];
      evalr(this, cc, r, val, p);
    }
    for (let n = 0; n < cc.nodes.length; n++) {
      const node = cc.nodes[n];
      const v = val.get(cc.find(n));
      if (v !== undefined) {
        if (!known.has(node.term)) known.set(node.term, v);
      }
    }
  }

  snapshot(terms: Terms): string {
    let s = '{"classes":[';
    const cc = this.last;
    if (cc !== null) {
      const roots: number[] = [];
      for (let n = 0; n < cc.nodes.length; n++) if (cc.find(n) === n) roots.push(n);
      const keys = new Map<number, number>(
        roots.map((r) => [r, Math.min(...cc.members[r].map((m) => cc.nodes[m].term))]),
      );
      roots.sort((x, y) => keys.get(x)! - keys.get(y)!);
      const shownRoots = roots.slice(0, SNAPSHOT_CLASSES);
      for (let i = 0; i < shownRoots.length; i++) {
        const r = shownRoots[i];
        if (i > 0) {
          s += ",";
        }
        const members: number[] = cc.members[r].slice();
        members.sort((x, y) => cc.nodes[x].term - cc.nodes[y].term);
        s += '{"members":[';
        for (let j = 0; j < members.length; j++) {
          if (j > 0) {
            s += ",";
          }
          s += jstr(terms.display(cc.nodes[members[j]].term));
        }
        s += '],"sort":';
        s += jstr(terms.sort_name(terms.sort(cc.nodes[r].term)));
        s += ',"ctor":';
        const k = cc.ctor_of.get(r);
        if (k !== undefined) s += jstr(terms.display(cc.nodes[k].term));
        else s += "null";
        s += ',"excluded":[';
        const ex = cc.excluded.get(r);
        if (ex !== undefined) {
          const t = cc.nodes[r].term;
          const d = this.sort_dt.get(terms.sort(t));
          for (let j = 0; j < ex.length; j++) {
            if (j > 0) {
              s += ",";
            }
            const name = d === undefined ? "" : this.ctor_name(d, ex[j][0]);
            s += jstr(name);
          }
        }
        s += "]}";
      }
      s += '],"diseqs":[';
      for (let i = 0; i < cc.diseqs.length; i++) {
        const [a, b] = cc.diseqs[i];
        if (i > 0) {
          s += ",";
        }
        s += "[";
        s += jstr(terms.display(cc.nodes[a].term));
        s += ",";
        s += jstr(terms.display(cc.nodes[b].term));
        s += "]";
      }
      s += `],"merges":${cc.edges.length}`;
      // The whole closure, for the playground's step-by-step graph.
      s += ',"nodes":[';
      const nn = Math.min(cc.nodes.length, SNAPSHOT_NODES);
      for (let i = 0; i < nn; i++) {
        const n = cc.nodes[i];
        if (i > 0) {
          s += ",";
        }
        s += '{"term":';
        s += jstr(terms.display(n.term));
        const kind = n.kind.kind === "Leaf" ? "leaf" : n.kind.kind === "Ctor" ? "ctor" : "sel";
        s += `,"kind":"${kind}","children":[`;
        s += n.children.join(",");
        s += "]}";
      }
      s += '],"history":[';
      const shown = (x: number) => x < SNAPSHOT_NODES;
      let first = true;
      for (const e of cc.edges.filter((e) => shown(e.a) && shown(e.b))) {
        if (!first) {
          s += ",";
        }
        first = false;
        s += `{"a":${e.a},"b":${e.b},"rule":"${e.rule}","lits":[`;
        s += e.lits.map((l) => String(lit_to_dimacs(l))).join(",");
        s += "]}";
      }
      s += '],"diseqNodes":[';
      first = true;
      for (const [a, b, l] of cc.diseqs.filter((d) => shown(d[0]) && shown(d[1]))) {
        if (!first) {
          s += ",";
        }
        first = false;
        s += `[${a},${b},${lit_to_dimacs(l)}]`;
      }
      s += "]";
    } else {
      s += '],"diseqs":[],"merges":0';
    }
    s += ',"datatypes":[';
    for (let i = 0; i < this.dts.length; i++) {
      const d = this.dts[i];
      if (i > 0) {
        s += ",";
      }
      const ctors: string[] = d.ctors.map((c) => {
        if (c.fields.length === 0) {
          return c.name;
        }
        const fs: string[] = c.fields.map(([n, srt]) => `${n}: ${terms.sort_name(srt)}`);
        return `${c.name}(${fs.join(", ")})`;
      });
      s += '{"name":';
      s += jstr(d.name);
      s += ',"ctors":';
      s += jstr(ctors.join(" | "));
      s += `,"finite":${d.finite}}`;
    }
    s += '],"last":';
    if (this.last_event !== null) s += jstr(this.last_event);
    else s += "null";
    s += "}";
    return s;
  }

  eval_app(sym: string, args: Value[], _terms: Terms): Value | null {
    const f = this.funs.get(sym);
    if (f === undefined) return null;
    switch (f.kind) {
      case "Ctor":
        return { kind: "Dt", _0: this.ctor_name(f._0, f._1), _1: args.slice() };
      case "Tester": {
        const a = args[0];
        if (a === undefined) return null;
        if (a.kind === "Dt") return { kind: "Bool", _0: a._0 === this.ctor_name(f._0, f._1) };
        return null;
      }
      // A selector applied to another constructor is unspecified.
      case "Sel": {
        const a = args[0];
        if (a === undefined) return null;
        if (a.kind === "Dt" && a._0 === this.ctor_name(f._0, f._1)) return a._1[f._2] ?? null;
        return null;
      }
    }
  }

  default_value(sort: number, _terms: Terms): Value | null {
    const d = this.sort_dt.get(sort);
    if (d === undefined) return null;
    const fresh = { v: 0n };
    return this.fresh_value(d, [], fresh, new Set(), 0);
  }

  take_changed(): boolean {
    const c = this.changed;
    this.changed = false;
    return c;
  }
}

