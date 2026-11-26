//! From assertions to CNF:
//! 1. **Purification** (Nelson–Oppen input separation): every atom must
//!    belong to a single theory. An "alien" subterm, owned by another
//!    theory than its context, is replaced by a fresh constant `kᵢ`, and
//!    the definition `kᵢ = t` is asserted. `head(l) = x + 1` becomes
//!    `k1 = x + 1` (LIA) with `k1 = head(l)` (DT).
//! 2. **Shared constants**: constants used by two theories; every pair of
//!    shared constants of the same sort gets an interface equality atom.
//! 3. **Tseitin** encoding of the Boolean structure; atoms become Boolean
//!    variables.
//! 4. **Registration**: each atom is handed to its theories, which may add
//!    definitional axioms (e.g. LIA's `a = b ⇔ a ≤ b ∧ a ≥ b`).
// (port of src/smt/preprocess.rs)

import { Combination, VarInfo, VarKind } from "./combine";
import { Problem } from "./parser";
import { SmtError } from "./sexp";
import { TermId, Terms, TheoryId, BOOL } from "./term";
import { Cnf } from "../dimacs";
import { Lit, lit_new, lit_not } from "../lit";
import { RustErr } from "../util";

const CONNECTIVES: string[] = ["and", "or", "not", "=>", "xor", "ite"];

export class Prep {
  cnf: Cnf;
  /** Why each original clause exists. */
  clause_origin: string[];
  assertions: string[];
  purified: string[];
  /** Purification definitions `k = t` (atom terms). */
  definitions: TermId[];
  fresh: TermId[];
  /** Bool constant -> SAT variable. */
  bool_vars: Map<TermId, number>;
  /** Input atom -> its purified atom (for showing the formula as written). */
  atom_map: Map<TermId, TermId>;

  constructor(init?: Partial<Prep>) {
    this.cnf = init?.cnf ?? new Cnf();
    this.clause_origin = init?.clause_origin ?? [];
    this.assertions = init?.assertions ?? [];
    this.purified = init?.purified ?? [];
    this.definitions = init?.definitions ?? [];
    this.fresh = init?.fresh ?? [];
    this.bool_vars = init?.bool_vars ?? new Map();
    this.atom_map = init?.atom_map ?? new Map();
  }
}

class Purifier {
  terms: Terms;
  alien: Map<TermId, TermId> = new Map();
  atom_map: Map<TermId, TermId> = new Map();
  defs: TermId[] = [];
  fresh: TermId[] = [];

  constructor(terms: Terms) {
    this.terms = terms;
  }

  formula(t: TermId): TermId {
    const node = this.terms.node(t).clone();
    switch (node.op.kind) {
      case "True":
      case "False":
      case "Var":
      case "Num":
        return t;
      case "App":
        if (is_connective(this.terms, t)) {
          const args: TermId[] = node.args.map((a) => this.formula(a));
          return this.terms.mk(node.op, args, BOOL);
        } else {
          const p = this.atom(t);
          this.atom_map.set(t, p);
          return p;
        }
    }
  }

  atom(t: TermId): TermId {
    const node = this.terms.node(t).clone();
    if (this.terms.sym(t) === "=") {
      const [a, b] = [node.args[0], node.args[1]];
      const th = this.terms.owner(a) ?? this.terms.owner(b);
      const a2 = this.term(a, th);
      const b2 = this.term(b, th);
      return mk_eq(this.terms, a2, b2);
    }
    const th = this.terms.owner(t);
    const args: TermId[] = node.args.map((a) => this.term(a, th));
    return this.terms.mk(node.op, args, BOOL);
  }

  /** Purify `t` occurring in a context owned by theory `ctx`. */
  term(t: TermId, ctx: TheoryId | null): TermId {
    if (this.terms.is_var(t)) {
      return t;
    }
    const own = this.terms.owner(t);
    const node = this.terms.node(t).clone();
    const args: TermId[] = node.args.map((a) => this.term(a, own));
    const t2 = this.terms.mk(node.op, args, node.sort);
    if (ctx !== null && own !== ctx) {
      return this.alien_(t2);
    }
    return t2;
  }

  /** Rust method `alien` (renamed: the field of the same name exists). */
  alien_(t: TermId): TermId {
    const found = this.alien.get(t);
    if (found !== undefined) {
      return found;
    }
    const v = this.terms.fresh_var("k", this.terms.sort(t));
    const def = this.terms.app("=", [v, t], BOOL);
    this.alien.set(t, v);
    this.defs.push(def);
    this.fresh.push(v);
    return v;
  }
}

function mk_eq(terms: Terms, a: TermId, b: TermId): TermId {
  if (terms.is_var(a) && terms.is_var(b) && b < a) {
    [a, b] = [b, a];
  }
  return terms.app("=", [a, b], BOOL);
}

function is_connective(terms: Terms, t: TermId): boolean {
  const s = terms.sym(t);
  if (s !== null && CONNECTIVES.includes(s)) return true;
  if (s === "=") return terms.sort(terms.args(t)[0]) === BOOL;
  return false;
}

function collect_atoms(terms: Terms, t: TermId, out: TermId[]): void {
  switch (terms.node(t).op.kind) {
    case "True":
    case "False":
    case "Var":
    case "Num":
      return;
    case "App":
      if (is_connective(terms, t)) {
        for (const a of terms.args(t)) {
          collect_atoms(terms, a, out);
        }
      } else if (!out.includes(t)) {
        out.push(t);
      }
  }
}

class Cnfer {
  comb: Combination;
  clauses: Lit[][] = [];
  origin: string[] = [];
  memo: Map<TermId, Lit> = new Map();
  num_vars = 0;
  pending: [number, TermId, VarKind][] = [];
  /** Rust field `true_lit` (renamed: the method of the same name exists). */
  true_lit_: Lit | null = null;
  bool_vars: Map<TermId, number> = new Map();

  constructor(comb: Combination) {
    this.comb = comb;
  }

  new_var(info: VarInfo): number {
    const v = this.num_vars;
    this.num_vars += 1;
    this.comb.set_var(v, info);
    return v;
  }

  clause(lits: Lit[], origin: string): void {
    this.clauses.push(lits);
    this.origin.push(origin);
  }

  atom_var(t: TermId, kind: VarKind): number {
    const found = this.comb.atom_of.get(t);
    if (found !== undefined) {
      return found;
    }
    const info = new VarInfo({
      label: this.comb.terms.display(t),
      neg: this.comb.terms.display_neg(t),
      kind,
      theories: [],
      def: null,
      term: t,
    });
    const v = this.new_var(info);
    this.comb.atom_of.set(t, v);
    this.pending.push([v, t, kind]);
    return v;
  }

  true_lit(): Lit {
    if (this.true_lit_ !== null) {
      return this.true_lit_;
    }
    const v = this.new_var(
      new VarInfo({
        label: "true",
        neg: "false",
        kind: "True",
        theories: [],
        def: null,
        term: null,
      }),
    );
    const l = lit_new(v, true);
    this.clause([l], "the constant true");
    this.true_lit_ = l;
    return l;
  }

  lit(t: TermId): Lit {
    const found = this.memo.get(t);
    if (found !== undefined) {
      return found;
    }
    const terms = this.comb.terms;
    const node = terms.node(t).clone();
    let l: Lit;
    const op = node.op;
    switch (op.kind) {
      case "True":
        l = this.true_lit();
        break;
      case "False":
        l = lit_not(this.true_lit());
        break;
      case "Var": {
        const name = op._0;
        const v = this.new_var(
          new VarInfo({
            label: name,
            neg: `¬${name}`,
            kind: "Bool",
            theories: [],
            def: null,
            term: t,
          }),
        );
        this.bool_vars.set(t, v);
        l = lit_new(v, true);
        break;
      }
      case "Num":
        throw new Error("internal error: entered unreachable code: numeral in Boolean position");
      case "App": {
        const sym = op._0;
        if (!is_connective(terms, t)) {
          l = lit_new(this.atom_var(t, "Atom"), true);
          break;
        }
        if (sym === "not") {
          const a = this.lit(node.args[0]);
          this.memo.set(t, lit_not(a));
          return lit_not(a);
        }
        const args: Lit[] = node.args.map((a) => this.lit(a));
        const def = this.comb.terms.display(t);
        const v = this.num_vars;
        const label = `t${v + 1}`;
        this.new_var(
          new VarInfo({
            label: label,
            neg: `¬${label}`,
            kind: "Aux",
            theories: [],
            def: def,
            term: t,
          }),
        );
        const x = lit_new(v, true);
        const why = `Tseitin: ${label} ⇔ ${def}`;
        switch (sym) {
          case "and": {
            for (const a of args) {
              this.clause([lit_not(x), a], why);
            }
            const c = [x];
            c.push(...args.map((a) => lit_not(a)));
            this.clause(c, why);
            break;
          }
          case "or":
          case "=>": {
            const args2: Lit[] = sym === "=>" ? [lit_not(args[0]), args[1]] : args;
            const c = [lit_not(x)];
            c.push(...args2);
            this.clause(c, why);
            for (const a of args2) {
              this.clause([x, lit_not(a)], why);
            }
            break;
          }
          case "xor": {
            const [a, b] = [args[0], args[1]];
            this.clause([lit_not(x), a, b], why);
            this.clause([lit_not(x), lit_not(a), lit_not(b)], why);
            this.clause([x, lit_not(a), b], why);
            this.clause([x, a, lit_not(b)], why);
            break;
          }
          case "=": {
            const [a, b] = [args[0], args[1]];
            this.clause([lit_not(x), lit_not(a), b], why);
            this.clause([lit_not(x), a, lit_not(b)], why);
            this.clause([x, a, b], why);
            this.clause([x, lit_not(a), lit_not(b)], why);
            break;
          }
          case "ite": {
            const [c, a, b] = [args[0], args[1], args[2]];
            this.clause([lit_not(x), lit_not(c), a], why);
            this.clause([lit_not(x), c, b], why);
            this.clause([x, lit_not(c), lit_not(a)], why);
            this.clause([x, c, lit_not(b)], why);
            break;
          }
          default:
            throw new Error("internal error: entered unreachable code");
        }
        l = x;
        break;
      }
    }
    this.memo.set(t, l);
    return l;
  }

  /** Clauses for a top-level assertion, avoiding Tseitin variables for the
   * outermost conjunctions and disjunctions. */
  assert_top(t: TermId, origin: string): void {
    const terms = this.comb.terms;
    const node = terms.node(t).clone();
    const sym = terms.sym(t);
    if (node.op.kind === "True") {
      // nothing
    } else if (node.op.kind === "False") {
      this.clause([], `${origin} (false)`);
    } else if (sym === "and") {
      for (const a of node.args) {
        this.assert_top(a, origin);
      }
    } else if (sym === "not") {
      const inner = node.args[0];
      const inode = this.comb.terms.node(inner).clone();
      const isym = this.comb.terms.sym(inner);
      if (isym === "not") {
        this.assert_top(inode.args[0], origin);
      } else if (isym === "or") {
        for (const a of inode.args) {
          const na = this.comb.terms.app("not", [a], BOOL);
          this.assert_top(na, origin);
        }
      } else {
        const l = this.lit(t);
        this.clause([l], origin);
      }
    } else if (sym === "or") {
      const lits: Lit[] = node.args.map((a) => this.lit(a));
      this.clause(lits, origin);
    } else if (sym === "=>") {
      const a = this.lit(node.args[0]);
      const b = this.lit(node.args[1]);
      this.clause([lit_not(a), b], origin);
    } else {
      const l = this.lit(t);
      this.clause([l], origin);
    }
  }
}

export function preprocess(problem: Problem, comb: Combination): Prep {
  const assertions: string[] = problem.assertions.map((a) => comb.terms.display(a));

  // 1. purification
  const p = new Purifier(comb.terms);
  const pure: TermId[] = problem.assertions.map((a) => p.formula(a));
  const [defs, fresh, atom_map] = [p.defs, p.fresh, p.atom_map];
  const purified: string[] = pure.map((a) => comb.terms.display(a));

  // 2. which theory uses which constant; shared constants
  const atoms: TermId[] = [];
  for (const a of [...pure, ...defs]) {
    collect_atoms(comb.terms, a, atoms);
  }
  const var_var = (terms: Terms, t: TermId) => terms.sym(t) === "=" && terms.args(t).every((x) => terms.is_var(x));
  for (let pass = 0; pass < 2; pass++) {
    for (const a of atoms) {
      if (var_var(comb.terms, a) !== (pass === 1)) {
        continue;
      }
      const ths = comb.theories_for_atom(a);
      const vars: TermId[] = [];
      comb.terms.vars_in(a, vars);
      for (const v of vars) {
        let e = comb.uses.get(v);
        if (e === undefined) {
          e = [];
          comb.uses.set(v, e);
        }
        for (const th of ths) {
          if (!e.includes(th)) {
            e.push(th);
          }
        }
      }
    }
  }
  const shared: TermId[] = [];
  for (const [v, u] of comb.uses) {
    if (u.length >= 2) shared.push(v);
  }
  shared.sort((a, b) => a - b);
  comb.shared = shared.slice();

  // 3. Tseitin
  const c = new Cnfer(comb);
  pure.forEach((a, i) => {
    const origin = `assert #${i + 1}: ${assertions[i]}`;
    c.assert_top(a, origin);
  });
  for (const d of defs) {
    const v = c.atom_var(d, "Definition");
    const origin = `purification: ${c.comb.terms.display(d)}`;
    c.clause([lit_new(v, true)], origin);
  }
  const iface: [TermId, TermId, number][] = [];
  for (let i = 0; i < shared.length; i++) {
    for (let j = i + 1; j < shared.length; j++) {
      const [x, y] = [shared[i], shared[j]];
      if (c.comb.terms.sort(x) !== c.comb.terms.sort(y)) {
        continue;
      }
      const eq = mk_eq(c.comb.terms, x, y);
      const v = c.atom_var(eq, "Interface");
      iface.push([x, y, v]);
    }
  }
  c.comb.interface = iface;

  // 4. registration with the theories
  const pending = c.pending;
  c.pending = [];
  let next = c.num_vars;
  let axioms;
  {
    const alloc = () => {
      next += 1;
      return next - 1;
    };
    try {
      axioms = c.comb.register_all(pending, alloc);
    } catch (x) {
      if (!(x instanceof RustErr)) throw x;
      throw new RustErr(new SmtError(0, x.value as string));
    }
  }
  c.num_vars = next;
  for (const ax of axioms) {
    const origin = `axiom (${ax.theory}): ${ax.why}`;
    c.clause(ax.lits, origin);
  }

  const { clauses, origin, num_vars, bool_vars } = c;
  return new Prep({
    cnf: new Cnf({
      num_vars,
      clauses,
      warnings: [],
    }),
    clause_origin: origin,
    assertions,
    purified,
    definitions: defs,
    fresh,
    bool_vars,
    atom_map,
  });
}
