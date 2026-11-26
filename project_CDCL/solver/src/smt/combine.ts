//! Nelson–Oppen combination of the registered theories, exposed to the SAT
//! solver as a single [`TheoryHook`].
//!
//! After purification every atom belongs to one theory, except equalities
//! between two shared constants, which every interested theory receives.
//! For every pair of shared constants of the same sort an *interface
//! equality* atom `x = y` exists. The combination then works as follows:
//! - deterministic exchange: a theory that derives `x = y` (or `x ≠ y`)
//!   propagates the interface atom, the SAT solver assigns it, and every
//!   other theory sees it as an ordinary literal;
//! - non-convex case: on the final check, any interface atom still
//!   unassigned is decided by a split (guessing the arrangement), guided by
//!   the theories' candidate models (`eq_hint`);
//! - when all theories accept a complete arrangement, the combined
//!   assignment is satisfiable (the theories are stably infinite on Int and
//!   share no function symbols).
// (port of src/smt/combine.rs)

import { BOOL, TermId, Terms, TheoryId, Value, Value_eq } from "./term";
import { Event, json_string } from "../trace";
import { Check, Ctx, Theory } from "./theory";
import { Lit, lit_is_positive, lit_new, lit_not, lit_to_dimacs, lit_var } from "../lit";
import { Solver, TheoryClause, TheoryHook, TheoryResponse } from "../solver";
import { RustErr } from "../util";

export type VarKind =
  /** Theory atom from the input. */
  | "Atom"
  /** Purification definition `k = t`. */
  | "Definition"
  /** Interface equality between shared constants (Nelson–Oppen). */
  | "Interface"
  /** Atom created by a theory (definitions, branch and bound, splits). */
  | "TheoryAtom"
  /** Declared Bool constant. */
  | "Bool"
  /** Tseitin auxiliary variable. */
  | "Aux"
  /** The constant `true`. */
  | "True";

export function VarKind_as_str(k: VarKind): string {
  switch (k) {
    case "Atom":
      return "atom";
    case "Definition":
      return "definition";
    case "Interface":
      return "interface";
    case "TheoryAtom":
      return "theory";
    case "Bool":
      return "bool";
    case "Aux":
      return "aux";
    case "True":
      return "true";
  }
}

export class VarInfo {
  label: string = "";
  neg: string = "";
  kind: VarKind = "Aux";
  theories: string[] = [];
  /** For Tseitin variables: the subformula they stand for. */
  def: string | null = null;
  term: TermId | null = null;

  constructor(init?: Partial<VarInfo>) {
    if (init) Object.assign(this, init);
  }

  write_json(v: number, out: { v: string }): void {
    out.v += `{"var":${v + 1},"label":`;
    json_string(out, this.label);
    out.v += ',"neg":';
    json_string(out, this.neg);
    out.v += `,"kind":"${VarKind_as_str(this.kind)}","theories":[`;
    this.theories.forEach((t, i) => {
      if (i > 0) out.v += ",";
      json_string(out, t);
    });
    out.v += '],"def":';
    if (this.def !== null) json_string(out, this.def);
    else out.v += "null";
    out.v += "}";
  }
}

export class Combination {
  terms: Terms;
  theories: Theory[];
  atom_of: Map<TermId, number> = new Map();
  atom_theories: Map<number, TheoryId[]> = new Map();
  vars: VarInfo[] = [];
  /** Theories using each constant after purification. */
  uses: Map<TermId, TheoryId[]> = new Map();
  shared: TermId[] = [];
  /** (x, y, var of `x = y`) */
  interface: [TermId, TermId, number][] = [];
  fed: number = 0;
  model: Map<TermId, Value> = new Map();
  model_ready: boolean = false;
  /** Pass theory propagations to the SAT solver. When off, theories only
   * check (conflicts and splits) and only interface equalities are still
   * propagated; this is the plain DPLL(T) of textbooks, used by the playground. */
  theory_propagation: boolean = true;

  private constructor(terms: Terms, theories: Theory[]) {
    this.terms = terms;
    this.theories = theories;
  }

  static new(theories: Theory[]): Combination {
    const c = new Combination(Terms.new(), theories);
    c.theories.forEach((t, i) => t.init(c.terms, i));
    return c;
  }

  theory_name(t: TheoryId): string {
    return this.theories[t].name();
  }

  /** Theories that must interpret an atom term. */
  theories_for_atom(t: TermId): TheoryId[] {
    const terms = this.terms;
    const args = terms.args(t);
    if (terms.sym(t) === "=" && args.length === 2) {
      const a = args[0];
      const b = args[1];
      const owners: TheoryId[] = [];
      for (const o of [terms.owner(a), terms.owner(b)]) {
        // flatten + dedup (consecutive duplicates)
        if (o !== null && (owners.length === 0 || owners[owners.length - 1] !== o)) owners.push(o);
      }
      if (owners.length > 0) return owners;
      // constant = constant: the sort's theory and every user
      const so = terms.sort_owner(terms.sort(a));
      const out: TheoryId[] = so !== null ? [so] : [];
      for (const x of [a, b]) {
        for (const u of this.uses.get(x) ?? []) {
          if (!out.includes(u)) out.push(u);
        }
      }
      out.sort((p, q) => p - q);
      return out;
    }
    const o = terms.owner(t);
    return o !== null ? [o] : [];
  }

  set_var(v: number, info: VarInfo): void {
    while (this.vars.length <= v) {
      this.vars.push(new VarInfo({ label: "", neg: "", kind: "Aux", theories: [], def: null, term: null }));
    }
    this.vars[v] = info;
  }

  private atom_info(term: TermId, kind: VarKind, theories: TheoryId[]): VarInfo {
    return new VarInfo({
      label: this.terms.display(term),
      neg: this.terms.display_neg(term),
      kind,
      theories: theories.map((t) => this.theory_name(t)),
      def: null,
      term,
    });
  }

  /** Register atoms with their theories. Theories may create further
   * atoms (registered in turn) and definitional axioms (returned).
   * Throws `RustErr<string>`. */
  register_all(pending: [number, TermId, VarKind][], alloc: () => number): TheoryClause[] {
    const queue: [number, TermId, VarKind][] = pending.slice();
    let head = 0;
    const axioms: TheoryClause[] = [];
    while (head < queue.length) {
      const [v, term, kind] = queue[head++];
      const ths = this.theories_for_atom(term);
      if (ths.length === 0) {
        throw new RustErr(`no theory can interpret ${this.terms.display(term)}`);
      }
      const info = this.atom_info(term, kind, ths);
      this.set_var(v, info);
      this.atom_of.set(term, v);
      this.atom_theories.set(v, ths.slice());
      for (const tid of ths) {
        const ctx = Ctx.new(this.terms, this.atom_of, alloc);
        this.theories[tid].register_atom(v, term, ctx);
        for (const [nv, t] of ctx.new_atoms) {
          queue.push([nv, t, "TheoryAtom"]);
        }
        axioms.push(...ctx.axioms);
      }
    }
    return axioms;
  }

  /** Run one theory check with on-demand atom creation; new variables are
   * announced in the trace before anything refers to them.
   * Throws `RustErr<string>`. */
  private run_theory(tid: TheoryId, sat: Solver, final_check: boolean, axioms: TheoryClause[]): Check {
    const before = sat.num_vars();
    const recording = sat.tracer.enabled;
    const alloc = () => sat.new_var();
    const ctx = Ctx.new(this.terms, this.atom_of, alloc);
    this.theories[tid].set_recording(recording);
    const check = this.theories[tid].check(ctx, final_check);
    const new_atoms = ctx.new_atoms;
    axioms.push(...ctx.axioms);
    if (new_atoms.length > 0) {
      const pending: [number, TermId, VarKind][] = new_atoms.map(([v, t]) => [v, t, "TheoryAtom"]);
      const more = this.register_all(pending, () => sat.new_var());
      axioms.push(...more);
    }
    const after = sat.num_vars();
    for (let v = before; v < after; v++) {
      const info = this.vars[v];
      sat.tracer.push(() => ({
        kind: "NewVar",
        var: v + 1,
        label: info.label,
        neg: info.neg,
        kind_: VarKind_as_str(info.kind),
        theories: info.theories.join(","),
      }));
    }
    return check;
  }

  private label(l: Lit): string {
    const v = this.vars[lit_var(l)];
    if (v === undefined) return `${lit_to_dimacs(l)}`;
    return lit_is_positive(l) ? v.label : v.neg;
  }

  private is_interface(v: number): boolean {
    const x = this.vars[v];
    return x !== undefined && x.kind === "Interface";
  }

  /** Translate a theory's answer into clauses for the SAT solver. */
  private absorb(tid: TheoryId, check: Check, sat: Solver, resp: TheoryResponse): void {
    const name = this.theory_name(tid);
    for (const [kind, message, lits] of check.notes) {
      sat.tracer.push(() => theory_event(name, kind, message, lits.map((l) => lit_to_dimacs(l)), ""));
    }
    if (check.conflict !== null) {
      const c = check.conflict;
      const data = sat.tracer.enabled ? this.theories[tid].snapshot(this.terms) : "";
      const lits = c.lits.map((l) => lit_to_dimacs(l));
      const why = c.why;
      sat.tracer.push(() => theory_event(name, "conflict", why, lits, data));
      resp.conflict = mk_clause(
        c.lits.map((l) => lit_not(l)),
        name,
        c.why,
      );
      return;
    }
    for (const p of check.propagations) {
      if (!this.theory_propagation && !this.is_interface(lit_var(p.implied))) {
        continue;
      }
      let why = p.why;
      if (this.is_interface(lit_var(p.implied))) {
        const others: string[] = this.atom_theories
          .get(lit_var(p.implied))!
          .filter((t) => t !== tid)
          .map((t) => this.theory_name(t));
        const msg = `Nelson–Oppen: ${name} derives ${this.label(p.implied)} between shared constants and passes it to ${
          others.length === 0 ? "the other theories" : others.join(", ")
        }`;
        const because = p.because.map((l) => lit_to_dimacs(l));
        const lits = [lit_to_dimacs(p.implied), ...because];
        const m = msg;
        sat.tracer.push(() => theory_event(name, "nelson-oppen", m, lits, ""));
        why = `${msg}. ${why}`;
      }
      const lits: Lit[] = [p.implied];
      for (const l of p.because) lits.push(lit_not(l));
      resp.propagations.push(mk_clause(lits, name, why));
    }
    if (resp.split === null) {
      if (check.split !== null) {
        const [lit, why] = check.split;
        resp.split = [lit, name, why];
      }
    }
    if (resp.unknown === null) {
      resp.unknown = check.unknown !== null ? `${name}: ${check.unknown}` : null;
    }
  }

  private snapshots(sat: Solver): void {
    if (!sat.tracer.enabled) {
      return;
    }
    for (let tid = 0; tid < this.theories.length; tid++) {
      if (this.theories[tid].take_changed()) {
        const data = this.theories[tid].snapshot(this.terms);
        const name = this.theory_name(tid);
        sat.tracer.push(() => theory_event(name, "state", "", [], data));
      }
    }
  }

  snapshot_all(): string {
    const s = { v: "{" };
    this.theories.forEach((t, i) => {
      if (i > 0) s.v += ",";
      json_string(s, t.name());
      s.v += ":";
      s.v += t.snapshot(this.terms);
    });
    s.v += "}";
    return s.v;
  }

  check(sat: Solver, final_check: boolean): TheoryResponse {
    // Feed newly assigned atoms to their theories.
    const trail = sat.trail();
    const trail_len = trail.length;
    for (let i = this.fed; i < trail_len; i++) {
      const lit = sat.trail()[i];
      const ths = this.atom_theories.get(lit_var(lit));
      if (ths !== undefined) {
        const level = sat.var_level(lit_var(lit));
        for (const tid of ths) {
          this.theories[tid].assert_lit(lit_var(lit), lit_is_positive(lit), level);
        }
      }
    }
    this.fed = trail_len;
    this.model_ready = false;

    const resp = new TheoryResponse();
    let axioms: TheoryClause[] = [];
    // Partial check of every theory.
    for (let tid = 0; tid < this.theories.length; tid++) {
      try {
        const check = this.run_theory(tid, sat, false, axioms);
        this.absorb(tid, check, sat, resp);
      } catch (e) {
        if (!(e instanceof RustErr)) throw e;
        resp.unknown = e.value as string;
      }
      if (resp.conflict !== null || resp.unknown !== null) {
        break;
      }
    }
    resp.axioms = axioms;
    if (
      !final_check ||
      resp.conflict !== null ||
      resp.propagations.length > 0 ||
      resp.axioms.length > 0 ||
      resp.unknown !== null
    ) {
      this.snapshots(sat);
      return resp;
    }

    // Final check: theory-specific completeness work (splits).
    axioms = [];
    for (let tid = 0; tid < this.theories.length; tid++) {
      try {
        const check = this.run_theory(tid, sat, true, axioms);
        this.absorb(tid, check, sat, resp);
      } catch (e) {
        if (!(e instanceof RustErr)) throw e;
        resp.unknown = e.value as string;
      }
      if (resp.conflict !== null || resp.propagations.length > 0 || resp.split !== null || resp.unknown !== null) {
        break;
      }
    }
    resp.axioms = axioms;
    if (
      resp.conflict !== null ||
      resp.propagations.length > 0 ||
      resp.split !== null ||
      resp.unknown !== null ||
      resp.axioms.length > 0
    ) {
      this.snapshots(sat);
      return resp;
    }

    // Nelson–Oppen: every pair of shared constants must be arranged.
    for (const [x, y, v] of this.interface) {
      if (sat.value(lit_new(v, true)) !== null) {
        continue;
      }
      let hint: boolean | null = null;
      for (const t of this.theories) {
        const h = t.eq_hint(x, y);
        if (h !== null) {
          hint = h;
          break;
        }
      }
      const eq = hint ?? false;
      const users: string[] = this.atom_theories.get(v)!.map((t) => this.theory_name(t));
      const xs = this.terms.display(x);
      const ys = this.terms.display(y);
      const why = `Nelson–Oppen arrangement: ${xs} and ${ys} are shared by ${users.join(
        " and ",
      )}, which must agree on whether ${xs} = ${ys}; no theory implies either, so guess it (${
        hint === true
          ? "they are equal in the current LIA model"
          : hint === false
            ? "they differ in the current LIA model"
            : "no model hint"
      }): try ${eq ? `${xs} = ${ys}` : `${xs} ≠ ${ys}`}`;
      resp.split = [lit_new(v, eq), "Nelson–Oppen", why];
      this.snapshots(sat);
      return resp;
    }

    // Consistent and complete: record the model.
    const known: Map<TermId, Value> = new Map();
    for (let tid = 0; tid < this.theories.length; tid++) {
      this.theories[tid].model(this.terms, known);
    }
    this.model = known;
    this.model_ready = true;
    this.snapshots(sat);
    return resp;
  }

  backjump(level: number, trail_len: number): void {
    for (const t of this.theories) {
      t.backtrack(level);
    }
    this.fed = Math.min(this.fed, trail_len);
  }

  /** Evaluate a term under the model (for verification). `bools` gives
   * the values of Bool constants. */
  eval(t: TermId, bools: (t: TermId) => boolean | null): Value | null {
    const terms = this.terms;
    const node = terms.node(t);
    const b = (t: TermId): boolean | null => {
      const v = this.eval(t, bools);
      if (v === null) return null;
      return v.kind === "Bool" ? v._0 : null;
    };
    const op = node.op;
    switch (op.kind) {
      case "True":
        return { kind: "Bool", _0: true };
      case "False":
        return { kind: "Bool", _0: false };
      case "Num":
        return { kind: "Int", _0: op._0 };
      case "Var": {
        if (node.sort === BOOL) {
          const x = bools(t);
          return x === null ? null : { kind: "Bool", _0: x };
        }
        const m = this.model.get(t);
        return m !== undefined ? m : this.default_value(node.sort);
      }
      case "App": {
        const sym = op._0;
        switch (sym) {
          case "not": {
            const x = b(node.args[0]);
            if (x === null) return null;
            return { kind: "Bool", _0: !x };
          }
          case "and": {
            let r = true;
            for (const a of node.args) {
              const x = b(a);
              if (x === null) return null;
              r = r && x;
            }
            return { kind: "Bool", _0: r };
          }
          case "or": {
            let r = false;
            for (const a of node.args) {
              const x = b(a);
              if (x === null) return null;
              r = r || x;
            }
            return { kind: "Bool", _0: r };
          }
          case "=>": {
            const p = b(node.args[0]);
            if (p === null) return null;
            if (!p) return { kind: "Bool", _0: true };
            const q = b(node.args[1]);
            if (q === null) return null;
            return { kind: "Bool", _0: q };
          }
          case "xor": {
            const p = b(node.args[0]);
            if (p === null) return null;
            const q = b(node.args[1]);
            if (q === null) return null;
            return { kind: "Bool", _0: p !== q };
          }
          case "ite": {
            const c = b(node.args[0]);
            if (c === null) return null;
            return c ? this.eval(node.args[1], bools) : this.eval(node.args[2], bools);
          }
          case "=": {
            const p = this.eval(node.args[0], bools);
            if (p === null) return null;
            const q = this.eval(node.args[1], bools);
            if (q === null) return null;
            return { kind: "Bool", _0: Value_eq(p, q) };
          }
          default: {
            const owner = terms.fun_owner(sym);
            if (owner === null) return null;
            const args: Value[] = [];
            for (const a of node.args) {
              const x = this.eval(a, bools);
              if (x === null) return null;
              args.push(x);
            }
            const r = this.theories[owner].eval_app(sym, args, terms);
            if (r !== null) return r;
            const m = this.model.get(t);
            if (m !== undefined) return m;
            return this.default_value(node.sort);
          }
        }
      }
    }
  }

  private default_value(sort: number): Value | null {
    if (sort === BOOL) {
      return { kind: "Bool", _0: false };
    }
    const owner = this.terms.sort_owner(sort);
    if (owner === null) return null;
    return this.theories[owner].default_value(sort, this.terms);
  }
}

function mk_clause(lits: Lit[], theory: string, why: string): TheoryClause {
  return { lits, theory, why } as TheoryClause;
}

function theory_event(theory: string, kind: string, message: string, lits: number[], data: string): Event {
  return { kind: "Theory", theory, kind_: kind, message, lits, data };
}

/** The SAT solver owns the hook; the SMT driver keeps a handle to the same
 * combination to read the model and the variable table afterwards. */
export class HookAdapter extends TheoryHook {
  constructor(public _0: Combination) {
    super();
  }

  check(sat: Solver, final_check: boolean): TheoryResponse {
    return this._0.check(sat, final_check);
  }

  backjump(level: number, trail_len: number): void {
    this._0.backjump(level, trail_len);
  }
}
