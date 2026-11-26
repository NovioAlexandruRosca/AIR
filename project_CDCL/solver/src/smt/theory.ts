//! The theory interface. A theory plugs into the solver by implementing
//! [`Theory`] and being listed in `smt::default_theories()`; nothing else in
//! the solver, the parser or the combination needs to change.
//!
//! A theory
//! 1. contributes sorts and symbols to the signature (`init`, `command`,
//!    `type_app`), which also tells purification who owns which term;
//! 2. receives the atoms it owns (`register_atom`) and the truth values the
//!    SAT solver assigns to them (`assert_lit` / `backtrack`);
//! 3. answers `check`: conflict (with an explanation), propagations (with
//!    explanations), or, on a final check, a case split;
//! 4. produces model values and a JSON snapshot of its state for the UI.
// (port of src/smt/theory.rs)

import { Sexp } from "./sexp";
import { TermId, Terms, TheoryId, Value } from "./term";
import { Lit, lit_new } from "../lit";
import { TheoryClause } from "../solver";

/** What a theory sees while it runs: the term bank and a way to create new
 * atoms (Boolean variables) on demand. */
export class Ctx {
  terms: Terms;
  private atom_of: Map<TermId, number>;
  private alloc: () => number;
  /** Atoms created during this call; the combination registers them with
   * their theories right after the call returns. */
  new_atoms: [number, TermId][] = [];
  /** Permanent clauses (e.g. definitions of new atoms). */
  axioms: TheoryClause[] = [];

  constructor(terms: Terms, atom_of: Map<TermId, number>, alloc: () => number) {
    this.terms = terms;
    this.atom_of = atom_of;
    this.alloc = alloc;
  }

  static new(terms: Terms, atom_of: Map<TermId, number>, alloc: () => number): Ctx {
    return new Ctx(terms, atom_of, alloc);
  }

  /** Boolean variable of an atom term, created if it does not exist yet. */
  atom(term: TermId): number {
    const found = this.atom_of.get(term);
    if (found !== undefined) {
      return found;
    }
    const v = this.alloc();
    this.atom_of.set(term, v);
    this.new_atoms.push([v, term]);
    return v;
  }

  /** Literal "atom term is `value`". */
  lit(term: TermId, value: boolean): Lit {
    return lit_new(this.atom(term), value);
  }

  existing_atom(term: TermId): number | null {
    return this.atom_of.get(term) ?? null;
  }

  axiom(lits: Lit[], theory: string, why: string): void {
    this.axioms.push({
      lits,
      theory: theory,
      why,
    } as TheoryClause);
  }
}

/** `implied` holds because all of `because` (currently true literals) do. */
export class Implied {
  implied: Lit;
  because: Lit[];
  why: string;
  constructor(init?: Partial<Implied>) {
    this.implied = init?.implied ?? 0;
    this.because = init?.because ?? [];
    this.why = init?.why ?? "";
  }
}

/** The currently true literals `lits` cannot hold together. */
export class Inconsistent {
  lits: Lit[];
  why: string;
  constructor(init?: Partial<Inconsistent>) {
    this.lits = init?.lits ?? [];
    this.why = init?.why ?? "";
  }
}

export class Check {
  conflict: Inconsistent | null;
  propagations: Implied[];
  /** Final checks only: decide this literal next, and why. */
  split: [Lit, string] | null;
  unknown: string | null;
  /** Explanatory notes for the playground: (kind, message, literals). */
  notes: [string, string, Lit[]][];

  constructor(init?: Partial<Check>) {
    this.conflict = init?.conflict ?? null;
    this.propagations = init?.propagations ?? [];
    this.split = init?.split ?? null;
    this.unknown = init?.unknown ?? null;
    this.notes = init?.notes ?? [];
  }

  is_empty(): boolean {
    return this.conflict === null && this.propagations.length === 0 && this.split === null && this.unknown === null;
  }
}

export abstract class Theory {
  abstract name(): string;

  // ---------------------------------------------------------- signature

  /** Add built-in sorts and symbols. `me` is this theory's id. */
  abstract init(terms: Terms, me: TheoryId): void;

  /** Handle a theory-specific command such as `declare-datatypes`.
   * Returns Ok(false) when the command is not this theory's.
   * (Errors: throws `RustErr<SmtError>`.) */
  command(_cmd: Sexp, _terms: Terms, _me: TheoryId): boolean {
    return false;
  }

  /** Build (and type-check) an application of a symbol this theory owns.
   * (Errors: throws `RustErr<string>`.) */
  abstract mk_app(sym: string, args: TermId[], terms: Terms): TermId;

  // ---------------------------------------------------------- solving

  /** A Boolean variable now stands for `atom`, which this theory must
   * interpret. New atoms and definitional axioms go through `ctx`.
   * (Errors: throws `RustErr<string>`.) */
  abstract register_atom(v: number, atom: TermId, ctx: Ctx): void;

  /** The SAT solver assigned `value` to the atom variable `var` at `level`. */
  abstract assert_lit(v: number, value: boolean, level: number): void;

  /** Undo everything asserted above decision level `level`. */
  abstract backtrack(level: number): void;

  /** Consistency check. On a final check every relevant atom is assigned
   * and the theory must either accept, report a conflict, or ask for a
   * split. */
  abstract check(ctx: Ctx, final_check: boolean): Check;

  /** Nelson–Oppen guidance: are `a` and `b` equal in the theory's current
   * candidate model? Used to pick the polarity of arrangement splits. */
  eq_hint(_a: TermId, _b: TermId): boolean | null {
    return null;
  }

  /** Add model values for the terms this theory knows. `known` already
   * holds the values decided by theories that ran before. */
  abstract model(terms: Terms, known: Map<TermId, Value>): void;

  /** JSON snapshot of the theory state for the playground. */
  abstract snapshot(terms: Terms): string;

  /** Evaluate an application of one of this theory's symbols on model
   * values (used to verify models). None when unspecified (e.g. a
   * selector applied to the wrong constructor). */
  eval_app(_sym: string, _args: Value[], _terms: Terms): Value | null {
    return null;
  }

  /** Some value of a sort this theory owns. */
  default_value(_sort: number, _terms: Terms): Value | null {
    return null;
  }

  /** Did the state change since the last call? (Avoids repeating
   * identical snapshots in the trace.) */
  take_changed(): boolean {
    return true;
  }

  /** Keep a detailed record of each check for the snapshot (on while
   * tracing; the playground draws it). */
  set_recording(_on: boolean): void {}
}
