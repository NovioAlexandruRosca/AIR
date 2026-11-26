//! CDCL solver: DPLL search + two-watched-literal BCP + MOMS decisions +
//! First-UIP clause learning + non-chronological backjumping.
//!
//! The solver is also the SAT engine of CDCL(T): an optional [`TheoryHook`]
//! is consulted after every BCP fixpoint (partial check) and when all
//! problem clauses are satisfied (final check). The hook can propagate
//! literals, report conflicts, add clauses and ask for case splits; the
//! solver only ever sees clauses and literals, never theory terms.
//!
//! Data structures
//! - `clauses: Vec<Clause>`: originals first, then learned and theory
//!   clauses in creation order. A clause id is its index and never changes.
//! - `watches[lit]`: clauses watching `lit` (it is `lits[0]` or `lits[1]`),
//!   each with a blocker literal. The list is visited when `lit` becomes false.
//! - Per variable: `value`, `level`, `reason` (None = decision or unassigned).
//! - `trail`: assigned literals in assignment order; `trail_lim[d]` is the
//!   trail position where decision level `d + 1` starts.
//
// TypeScript port notes: Rust fields that share their name with an accessor
// method (`num_vars`, `clauses`, `trail`, `value`, `model`) are stored as
// `num_vars_`, `clauses_`, `trail_`, `value_`, `model_`; the private method
// `reduce_db()` is `reduce_db_()` because the pub field `reduce_db` keeps
// its name.

import { Cnf } from "./dimacs";
import { Lit, lit_new, lit_not, lit_var, lit_is_positive, lit_index, lit_to_dimacs } from "./lit";
import { DecisionOrigin, Event, MomsCandidate, Tracer } from "./trace";
import { now } from "./util";

/// The `k` in the MOMS score `(f(x) + f(¬x)) * 2^k + f(x) * f(¬x)`.
export const MOMS_K = 1;
/// How many MOMS candidates a `Decide` event records.
const TRACED_CANDIDATES = 8;
/// Consecutive hook rounds without any effect before giving up.
const MAX_IDLE_HOOK_ROUNDS = 3;

export type Status =
  | "Sat"
  | "Unsat"
  /** Stopped before an answer; see `Solver::stop_reason`. */
  | "Unknown";

export function Status_as_str(s: Status): string {
  switch (s) {
    case "Sat":
      return "SAT";
    case "Unsat":
      return "UNSAT";
    case "Unknown":
      return "UNKNOWN";
  }
}

export type StopReason =
  | "ConflictLimit"
  | "TimeLimit"
  | "Cancelled"
  /** A theory could not decide (e.g. branch-and-bound limit); see
   * `Solver::incomplete_reason`. */
  | "Incomplete";

export function StopReason_as_str(r: StopReason): string {
  switch (r) {
    case "ConflictLimit":
      return "conflict limit";
    case "TimeLimit":
      return "time limit";
    case "Cancelled":
      return "cancelled";
    case "Incomplete":
      return "theory incomplete";
  }
}

export type ClauseKind =
  /** Input clause (for SMT: Tseitin, purification and registration axioms). */
  | "Original"
  /** Learned by conflict analysis. */
  | "Learned"
  /** Permanent clause added during search (axioms for a new theory atom). */
  | "Axiom"
  /** Theory lemma / explanation / conflict clause; deletable like learned. */
  | "Theory";

export class Clause {
  lits: Lit[];
  learnt: boolean;
  kind: ClauseKind;
  /// Literal block distance: distinct decision levels among the literals
  /// when the clause was learned (0 for original clauses).
  lbd: number;
  /// Removed by learned-clause database reduction; `lits` is then empty.
  deleted: boolean;
  constructor(init?: Partial<Clause>) {
    this.lits = init?.lits ?? [];
    this.learnt = init?.learnt ?? false;
    this.kind = init?.kind ?? "Original";
    this.lbd = init?.lbd ?? 0;
    this.deleted = init?.deleted ?? false;
  }
}

export class Stats {
  decisions = 0;
  propagations = 0;
  conflicts = 0;
  learned = 0;
  deleted = 0;
  max_level = 0;
  theory_propagations = 0;
  theory_conflicts = 0;
  theory_splits = 0;
  constructor(init?: Partial<Stats>) {
    Object.assign(this, init ?? {});
  }
}

/// Learned clauses kept before the first database reduction.
export const FIRST_REDUCE_AT = 8_000;

/// A clause produced by a theory, with a human-readable justification.
export class TheoryClause {
  lits: Lit[];
  theory: string;
  why: string;
  /** `new TheoryClause(lits, theory, why)` or `new TheoryClause({ lits, theory, why })`. */
  constructor(lits?: Lit[] | Partial<TheoryClause>, theory?: string, why?: string) {
    if (lits === undefined || Array.isArray(lits)) {
      this.lits = lits ?? [];
      this.theory = theory ?? "";
      this.why = why ?? "";
    } else {
      this.lits = lits.lits ?? [];
      this.theory = lits.theory ?? "";
      this.why = lits.why ?? "";
    }
  }
}

/// What a theory check asks the SAT solver to do.
export class TheoryResponse {
  /// Permanent clauses that are part of the problem (e.g. the definition
  /// of a freshly created atom). They count for MOMS and for "all
  /// problem clauses satisfied".
  axioms: TheoryClause[] = [];
  /// Theory-valid clauses that may help pruning (deletable).
  lemmas: TheoryClause[] = [];
  /// `lits[0]` is implied; the other literals are currently false and
  /// their negations are the explanation.
  propagations: TheoryClause[] = [];
  /// Every literal is currently false: the negations are inconsistent.
  conflict: TheoryClause | null = null;
  /// Decide this literal next (splitting on demand). Only honoured on
  /// a final check.
  split: [Lit, string, string] | null = null;
  /// The theory cannot decide the current assignment.
  unknown: string | null = null;
  constructor(init?: Partial<TheoryResponse>) {
    Object.assign(this, init ?? {});
  }
  static default(): TheoryResponse {
    return new TheoryResponse();
  }
}

/// The theory side of CDCL(T). The solver calls it; it never calls back
/// except through the `&mut Solver` it is handed.
export abstract class TheoryHook {
  /// Called after BCP reaches a fixpoint (`final_check == false`) and when
  /// every problem clause is satisfied (`final_check == true`). On a final
  /// check an empty response means "the assignment is theory-consistent
  /// and complete": the formula is satisfiable.
  abstract check(sat: Solver, final_check: boolean): TheoryResponse;
  /// Everything above decision level `level` was unassigned; the trail
  /// now has `trail_len` literals.
  abstract backjump(level: number, trail_len: number): void;
}

/// Result of replaying user decisions in the playground.
export class Replay {
  /// Number of decisions applied before stopping.
  applied = 0;
  /// Conflicting clause, if propagation ran into one.
  conflict: number | null = null;
  /// Decisions that were skipped because their variable was already set
  /// (index into the decision list, and whether it agreed).
  skipped: [number, boolean][] = [];
  /// "open", "conflict", "sat", "split" or "unknown".
  outcome = "open";
  /// For "split": the literal and why the theory wants it decided.
  split: [Lit, string, string] | null = null;
  note: string | null = null;
  /// Index of the first trace event produced by "let the solver finish".
  finish_from: number | null = null;
  /// For a conflict above level 0: the First-UIP clause CDCL would learn
  /// (not added; the playground keeps it when the user backtracks).
  learned: Lit[] | null = null;
  /// For "units": several clauses are unit and force different literals;
  /// the user picks which to propagate first (clause id, forced literal).
  units: [number, Lit][] = [];
  constructor(init?: Partial<Replay>) {
    Object.assign(this, init ?? {});
  }
}

/// One step of a playground replay: a decision, or the choice of which unit
/// clause to propagate when several are unit at once.
export type Action =
  | { kind: "Decide"; _0: Lit }
  /** Propagate this literal (it must be forced by one of the unit clauses). */
  | { kind: "Pick"; _0: Lit };

/// Remove duplicate literals, keeping the first occurrence's position.
export function dedup_clause(lits: Lit[]): Lit[] {
  const out: Lit[] = [];
  for (const l of lits) {
    if (!out.includes(l)) {
      out.push(l);
    }
  }
  return out;
}

/// True when every clause has at least one literal true under `model`
/// (`model[v]` is the value of variable `v`, 0-based).
export function verify_model(cnf: Cnf, model: boolean[]): boolean {
  return cnf.clauses.every((c) => c.some((l) => model[lit_var(l)] === lit_is_positive(l)));
}

function lit_val(value: (boolean | null)[], l: Lit): boolean | null {
  const v = value[lit_var(l)];
  return v === null ? null : v === lit_is_positive(l);
}

/// Number of unassigned literals if the clause is not satisfied, else None.
function open_size(value: (boolean | null)[], lits: Lit[]): number | null {
  let n = 0;
  for (const l of lits) {
    const v = lit_val(value, l);
    if (v === true) return null;
    if (v === null) n += 1;
  }
  return n;
}

function to_dimacs_sorted(lits: Lit[]): number[] {
  const v = lits.map(lit_to_dimacs);
  v.sort((x, y) => {
    const ax = Math.abs(x);
    const ay = Math.abs(y);
    if (ax !== ay) return ax - ay;
    return (x < 0 ? 1 : 0) - (y < 0 ? 1 : 0);
  });
  return v;
}

/// Binary resolution of `a` (contains ¬p) and `b` (contains p) on var(p).
function resolve(a: Lit[], b: Lit[], p: Lit): Lit[] {
  const np = lit_not(p);
  const out: Lit[] = a.filter((l) => l !== np);
  for (const l of b) {
    if (l !== p && !out.includes(l)) {
      out.push(l);
    }
  }
  return out;
}

/// Watch-list entry. `blocker` is another literal of the clause: if it is
/// true the clause is satisfied and BCP skips it without reading the clause.
interface Watch {
  cid: number;
  blocker: Lit;
}

/// Outcome of BCP plus theory checks run to a fixpoint.
export type Fixpoint = { kind: "Stable" } | { kind: "Conflict"; _0: number } | { kind: "Unknown"; _0: string };

/// Effect of applying one theory response.
export type Applied =
  | { kind: "Nothing" }
  | { kind: "Progress" }
  | { kind: "Conflict"; _0: number }
  | { kind: "Split"; _0: Lit; _1: string; _2: string }
  | { kind: "Unknown"; _0: string };

/// Effect of adding one clause during search.
export type Added = { kind: "Quiet" } | { kind: "Unit" } | { kind: "Conflict"; _0: number };

export class Solver {
  num_vars_: number;
  num_original_: number;
  clauses_: Clause[];
  /// Axiom clauses added during search; with the originals they form the
  /// problem MOMS looks at.
  extra_problem: number[];
  watches: Watch[][];
  value_: (boolean | null)[];
  level: number[];
  reason: (number | null)[];
  trail_: Lit[];
  trail_lim: number[];
  qhead: number;
  seen: boolean[];
  moms_count: number[];
  model_: boolean[];
  max_conflicts: number | null;
  /// Give up (Unknown) once this instant has passed (ms, see `now()`).
  deadline: number | null;
  /// Give up (Unknown) as soon as another thread sets this flag.
  cancel: { value: boolean } | null;
  /// Why the last `solve` returned Unknown.
  stop_reason: StopReason | null;
  /// Message from a theory that returned "unknown".
  incomplete_reason: string | null;
  /// Delete the worse half of the learned clauses whenever more than
  /// `max_learnts` are alive. The limit is raised in `solve` above anything
  /// a trace can record, so traces never contain a deletion.
  reduce_db: boolean;
  max_learnts: number;
  learnts_alive: number;
  /// CDCL(T): the theory combination, if any.
  hook: TheoryHook | null;
  /// Playground replay: unit clauses found by `propagate` are collected in
  /// `pending_units` instead of being propagated, so the user can choose.
  manual_units: boolean;
  pending_units: [number, Lit][];
  stats: Stats;
  tracer: Tracer;

  private constructor(cnf: Cnf, tracer: Tracer) {
    const n = cnf.num_vars;
    this.num_vars_ = n;
    this.num_original_ = cnf.clauses.length;
    this.clauses_ = [];
    this.extra_problem = [];
    this.watches = Array.from({ length: 2 * n }, () => []);
    this.value_ = new Array(n).fill(null);
    this.level = new Array(n).fill(0);
    this.reason = new Array(n).fill(null);
    this.trail_ = [];
    this.trail_lim = [];
    this.qhead = 0;
    this.seen = new Array(n).fill(false);
    this.moms_count = new Array(2 * n).fill(0);
    this.model_ = [];
    this.max_conflicts = null;
    this.deadline = null;
    this.cancel = null;
    this.stop_reason = null;
    this.incomplete_reason = null;
    this.reduce_db = true;
    this.max_learnts = FIRST_REDUCE_AT;
    this.learnts_alive = 0;
    this.hook = null;
    this.manual_units = false;
    this.pending_units = [];
    this.stats = new Stats();
    this.tracer = tracer;
  }

  static new(cnf: Cnf): Solver {
    return Solver.with_tracer(cnf, Tracer.disabled());
  }

  static with_tracer(cnf: Cnf, tracer: Tracer): Solver {
    const s = new Solver(cnf, tracer);
    for (const c of cnf.clauses) {
      const lits = dedup_clause(c);
      const id = s.clauses_.length;
      if (lits.length >= 2) {
        s.watches[lit_index(lits[0])].push({ cid: id, blocker: lits[1] });
        s.watches[lit_index(lits[1])].push({ cid: id, blocker: lits[0] });
      }
      s.clauses_.push(new Clause({ lits, learnt: false, kind: "Original", lbd: 0, deleted: false }));
    }
    return s;
  }

  num_vars(): number {
    return this.num_vars_;
  }

  num_original(): number {
    return this.num_original_;
  }

  clauses(): Clause[] {
    return this.clauses_;
  }

  /// Assigned literals in assignment order.
  trail(): Lit[] {
    return this.trail_;
  }

  /// Decision level at which `var` was assigned (meaningless if unassigned).
  var_level(v: number): number {
    return this.level[v];
  }

  /// Reason clause of an assigned variable (None for decisions).
  var_reason(v: number): number | null {
    return this.reason[v];
  }

  value(l: Lit): boolean | null {
    return lit_val(this.value_, l);
  }

  /// Create a fresh Boolean variable (used for atoms made during search).
  new_var(): number {
    const v = this.num_vars_;
    this.num_vars_ += 1;
    this.value_.push(null);
    this.level.push(0);
    this.reason.push(null);
    this.seen.push(false);
    this.moms_count.push(0, 0);
    this.watches.push([]);
    this.watches.push([]);
    return v;
  }

  /// Model as DIMACS literals (free variables are reported false).
  model_dimacs(): number[] {
    return this.model_.map((b, v) => lit_to_dimacs(lit_new(v, b)));
  }

  model(): boolean[] {
    return this.model_;
  }

  decision_level(): number {
    return this.trail_lim.length;
  }

  lit_value(l: Lit): boolean | null {
    return lit_val(this.value_, l);
  }

  /// Unit and empty input clauses are handled at level 0 up front.
  /// Returns the conflicting clause, if any.
  load_units(): number | null {
    for (let cid = 0; cid < this.num_original_; cid++) {
      const len = this.clauses_[cid].lits.length;
      if (len === 0) return cid;
      if (len === 1) {
        const l = this.clauses_[cid].lits[0];
        const v = this.lit_value(l);
        if (v === true) {
          // nothing
        } else if (v === false) {
          return cid;
        } else if (this.manual_units) {
          // manual units: the input's unit clauses wait too
          if (!this.pending_units.some(([c]) => c === cid)) {
            this.pending_units.push([cid, l]);
          }
        } else {
          this.enqueue(l, cid);
        }
      }
    }
    return null;
  }

  solve(): Status {
    // Every learned clause costs at least 3 events (Conflict, Learn,
    // Backjump), so no reduction can happen while a trace is recorded.
    if (this.tracer.enabled) {
      this.max_learnts = Math.max(this.max_learnts, Math.trunc(this.tracer.limit / 3) + 1);
    }
    const cid0 = this.load_units();
    if (cid0 !== null) {
      if (this.clauses_[cid0].lits.length !== 0) {
        this.stats.conflicts += 1;
      }
      this.tracer.push(() => ({ kind: "Conflict", clause: cid0, level: 0 }));
      return this.finish("Unsat");
    }

    let idle_final_rounds = 0;
    for (;;) {
      const reason = this.external_stop();
      if (reason !== null) {
        this.stop_reason = reason;
        return this.finish("Unknown");
      }
      const fp = this.fixpoint();
      if (fp.kind === "Conflict") {
        const status = this.on_conflict(fp._0);
        if (status !== null) {
          return this.finish(status);
        }
        continue;
      } else if (fp.kind === "Unknown") {
        return this.give_up(fp._0);
      }

      let decision: [Lit, number, MomsCandidate[], DecisionOrigin | null];
      const pb = this.pick_branch();
      if (pb !== null) {
        decision = [pb[0], pb[1], pb[2], null];
      } else {
        if (this.hook === null) {
          return this.finish("Sat");
        }
        const a = this.call_hook(true);
        switch (a.kind) {
          case "Nothing":
            return this.finish("Sat");
          case "Progress":
            idle_final_rounds = 0;
            continue;
          case "Conflict": {
            const status = this.on_conflict(a._0);
            if (status !== null) {
              return this.finish(status);
            }
            continue;
          }
          case "Unknown":
            return this.give_up(a._0);
          case "Split": {
            const lit = a._0;
            const by = a._1;
            const why = a._2;
            if (this.lit_value(lit) !== null) {
              // Already decided: the theory will see it next round.
              idle_final_rounds += 1;
              if (idle_final_rounds > MAX_IDLE_HOOK_ROUNDS) {
                return this.give_up(`${by} asked to split on an assigned literal`);
              }
              continue;
            }
            this.stats.theory_splits += 1;
            decision = [lit, 0, [], new DecisionOrigin({ by, why })];
            break;
          }
        }
      }
      idle_final_rounds = 0;
      const [lit, min_size, candidates, origin] = decision;
      this.decide_traced(lit, min_size, candidates, origin);
    }
  }

  decide_traced(lit: Lit, min_size: number, candidates: MomsCandidate[], origin: DecisionOrigin | null): void {
    this.stats.decisions += 1;
    this.trail_lim.push(this.trail_.length);
    const level = this.decision_level();
    this.stats.max_level = Math.max(this.stats.max_level, level);
    this.tracer.push(() => ({
      kind: "Decide",
      lit: lit_to_dimacs(lit),
      level,
      min_size,
      candidates,
      origin,
    }));
    this.enqueue(lit, null);
  }

  give_up(msg: string): Status {
    this.stop_reason = "Incomplete";
    this.incomplete_reason = msg;
    return this.finish("Unknown");
  }

  /// Handle a falsified clause: record it, learn and backjump. Returns a
  /// final status when the conflict settles the problem.
  on_conflict(confl: number): Status | null {
    this.stats.conflicts += 1;
    // Theory clauses may be falsified entirely below the current level.
    let max_level = 0;
    for (const l of this.clauses_[confl].lits) {
      max_level = Math.max(max_level, this.level[lit_var(l)]);
    }
    if (max_level < this.decision_level()) {
      this.backjump(max_level);
    }
    const level = this.decision_level();
    this.tracer.push(() => ({ kind: "Conflict", clause: confl, level }));
    if (level === 0) {
      return "Unsat";
    }
    if (this.max_conflicts !== null && this.stats.conflicts > this.max_conflicts) {
      this.stop_reason = "ConflictLimit";
      return "Unknown";
    }
    this.learn_and_backjump(confl);
    if (this.reduce_db && this.learnts_alive > this.max_learnts) {
      this.reduce_db_();
      this.max_learnts += Math.trunc(this.max_learnts / 10);
    }
    return null;
  }

  /// BCP, then partial theory checks, until nothing changes.
  fixpoint(): Fixpoint {
    let idle = 0;
    for (;;) {
      const confl = this.propagate();
      if (confl !== null) {
        return { kind: "Conflict", _0: confl };
      }
      // Manual units: Boolean propagation is not finished while unit
      // clauses wait for the user, so the theories are not asked yet.
      if (this.manual_units) {
        this.refresh_pending_units();
        if (this.pending_units.length !== 0) {
          return { kind: "Stable" };
        }
      }
      if (this.hook === null) {
        return { kind: "Stable" };
      }
      const a = this.call_hook(false);
      switch (a.kind) {
        case "Conflict":
          return { kind: "Conflict", _0: a._0 };
        case "Unknown":
          return { kind: "Unknown", _0: a._0 };
        case "Progress":
          idle = 0;
          break;
        case "Nothing":
        case "Split":
          idle += 1;
          if (this.qhead === this.trail_.length || idle > MAX_IDLE_HOOK_ROUNDS) {
            return { kind: "Stable" };
          }
          break;
      }
    }
  }

  /// Run the theory hook once and apply its response.
  call_hook(final_check: boolean): Applied {
    const hook = this.hook;
    if (hook === null) {
      return { kind: "Nothing" };
    }
    this.hook = null;
    const resp = hook.check(this, final_check);
    this.hook = hook;

    const before = this.trail_.length;
    for (const tc of resp.axioms) {
      const ad = this.add_clause_during_search(tc, "Axiom", "axiom");
      if (ad.kind === "Conflict") {
        return { kind: "Conflict", _0: ad._0 };
      }
    }
    for (const tc of resp.lemmas) {
      const ad = this.add_clause_during_search(tc, "Theory", "lemma");
      if (ad.kind === "Conflict") {
        return { kind: "Conflict", _0: ad._0 };
      }
    }
    if (resp.conflict !== null) {
      this.stats.theory_conflicts += 1;
      const ad = this.add_clause_during_search(resp.conflict, "Theory", "conflict");
      if (ad.kind === "Conflict") {
        return { kind: "Conflict", _0: ad._0 };
      }
      // A "conflict" that is not falsified (stale): just keep the lemma.
    }
    for (const tc of resp.propagations) {
      if (tc.lits.length === 0) {
        continue;
      }
      const implied = tc.lits[0];
      if (this.lit_value(implied) === true) {
        continue;
      }
      const ad = this.add_clause_during_search(tc, "Theory", "explanation");
      if (ad.kind === "Conflict") {
        return { kind: "Conflict", _0: ad._0 };
      } else if (ad.kind === "Unit") {
        this.stats.theory_propagations += 1;
      }
    }
    if (resp.unknown !== null) {
      return { kind: "Unknown", _0: resp.unknown };
    }
    if (this.trail_.length > before) {
      return { kind: "Progress" };
    }
    if (resp.split !== null) {
      const [lit, by, why] = resp.split;
      return { kind: "Split", _0: lit, _1: by, _2: why };
    }
    return { kind: "Nothing" };
  }

  /// Add a clause in the middle of search, choosing watches so that the
  /// 2WL invariant holds for the current assignment. Unit clauses are
  /// asserted at level 0 (after backjumping there) so they are never lost.
  add_clause_during_search(tc: TheoryClause, kind: ClauseKind, kind_name: string): Added {
    const lits = dedup_clause(tc.lits);
    if (lits.some((l) => lits.includes(lit_not(l)))) {
      return { kind: "Quiet" }; // tautology
    }
    // True literals first, then unassigned, then false by decreasing level.
    const key = (l: Lit): [number, number] => {
      const v = this.lit_value(l);
      if (v === true) return [0, 0];
      if (v === null) return [1, 0];
      return [2, -this.level[lit_var(l)]];
    };
    const keyed = lits.map((l) => ({ l, k: key(l) }));
    keyed.sort((a, b) => a.k[0] - b.k[0] || a.k[1] - b.k[1]);
    for (let i = 0; i < lits.length; i++) lits[i] = keyed[i].l;
    if (lits.length === 1 && this.lit_value(lits[0]) !== true && this.decision_level() > 0) {
      this.backjump(0);
    }

    const id = this.clauses_.length;
    const learnt = kind === "Theory";
    if (lits.length >= 2) {
      this.watches[lit_index(lits[0])].push({ cid: id, blocker: lits[1] });
      this.watches[lit_index(lits[1])].push({ cid: id, blocker: lits[0] });
    }
    const trace_lits = to_dimacs_sorted(lits);
    this.tracer.push(() => ({
      kind: "TheoryClause",
      clause: id,
      lits: trace_lits,
      kind_: kind_name,
      theory: tc.theory,
      why: tc.why,
    }));
    const first = lits.length > 0 ? lits[0] : null;
    const second = lits.length > 1 ? lits[1] : null;
    this.clauses_.push(new Clause({ lits, learnt, kind, lbd: 0, deleted: false }));
    if (kind === "Axiom") {
      this.extra_problem.push(id);
    }
    if (learnt) {
      this.learnts_alive += 1;
    }

    if (first === null) {
      return { kind: "Conflict", _0: id }; // empty clause
    }
    const fv = this.lit_value(first);
    if (fv === true) return { kind: "Quiet" };
    if (fv === false) return { kind: "Conflict", _0: id };
    const unit = second === null ? true : this.lit_value(second) === false;
    if (unit) {
      this.enqueue(first, id);
      return { kind: "Unit" };
    } else {
      return { kind: "Quiet" };
    }
  }

  /// Time limit or cancellation. Checked once per search iteration (one
  /// BCP round plus one decision or conflict), which is cheap next to MOMS.
  external_stop(): StopReason | null {
    if (this.cancel !== null && this.cancel.value) {
      return "Cancelled";
    }
    if (this.deadline !== null && now() >= this.deadline) {
      return "TimeLimit";
    }
    return null;
  }

  finish(status: Status): Status {
    if (status === "Sat") {
      this.model_ = this.value_.map((v) => v ?? false);
      // Problem clauses must hold; learned and theory clauses are only
      // implied (by the problem, or by the theories) and may not.
      // (debug_assert omitted)
    }
    const model = status === "Sat" ? this.model_dimacs() : [];
    // The result is recorded even when the trace was truncated.
    this.tracer.enabled = this.tracer.enabled || this.tracer.truncated;
    this.tracer.limit = Math.max(this.tracer.limit, this.tracer.events.length + 1);
    this.tracer.push(() => ({ kind: "Result", status: Status_as_str(status), model }));
    return status;
  }

  enqueue(lit: Lit, reason: number | null): void {
    const v = lit_var(lit);
    const level = this.decision_level();
    this.value_[v] = lit_is_positive(lit);
    this.level[v] = level;
    this.reason[v] = reason;
    this.trail_.push(lit);
    if (reason !== null) {
      const r = reason;
      this.stats.propagations += 1;
      this.tracer.push(() => ({ kind: "Propagate", lit: lit_to_dimacs(lit), reason: r, level }));
    }
  }

  /// Open a new decision level and assign `lit` (used by tests).
  decide(lit: Lit): void {
    this.trail_lim.push(this.trail_.length);
    this.enqueue(lit, null);
  }

  /// Playground: apply `decisions` in order, propagating (BCP + theory)
  /// after each one, and stop at the first conflict. No learning, no
  /// backjumping: the user sees exactly what their choices imply. When
  /// every problem clause ends up satisfied, the theories' final check is
  /// run once and its verdict reported.
  /// Unit clauses still waiting (manual units): drop those that are no
  /// longer unit (satisfied, or undone by a backjump).
  refresh_pending_units(): void {
    const pending = this.pending_units;
    this.pending_units = [];
    const kept = pending.filter(([cid, l]) => {
      const c = this.clauses_[cid];
      // a falsified one-literal clause stays: it is a conflict
      if (c.lits.length === 1 && this.lit_value(l) === false) {
        return true;
      }
      return !c.deleted && this.lit_value(l) === null && c.lits.every((m) => m === l || this.lit_value(m) === false);
    });
    this.pending_units = kept;
  }

  /// Propagate every waiting unit clause and go back to automatic
  /// propagation (before "let the solver finish").
  flush_pending_units(): void {
    this.manual_units = false;
    this.refresh_pending_units();
    const pending = this.pending_units;
    this.pending_units = [];
    for (const [cid, l] of pending) {
      if (this.lit_value(l) === null) {
        this.enqueue(l, cid);
      }
    }
  }

  /// Replay decisions with automatic unit propagation (see `replay_actions`).
  replay(decisions: Lit[]): Replay {
    const actions: Action[] = decisions.map((d) => ({ kind: "Decide", _0: d }));
    return this.replay_actions(actions, false, (_) => true);
  }

  /// Replay the playground's actions. With `manual`, whenever several unit
  /// clauses force different literals that `choosable` accepts, the replay
  /// stops ("units") unless the next action picks one of them. Units on
  /// other literals (internal helper atoms) are propagated right away.
  replay_actions(actions: Action[], manual: boolean, choosable: (l: Lit) => boolean): Replay {
    const r = new Replay();
    this.manual_units = manual;
    const cid0 = this.load_units();
    if (cid0 !== null) {
      this.tracer.push(() => ({ kind: "Conflict", clause: cid0, level: 0 }));
      r.conflict = cid0;
      r.outcome = "conflict";
      return r;
    }
    const next = { v: 0 };
    const check = (s: Solver, r: Replay, next: { v: number }): boolean => {
      for (;;) {
        const fp = s.fixpoint();
        if (fp.kind === "Conflict") {
          const cid = fp._0;
          const level = s.decision_level();
          s.tracer.push(() => ({ kind: "Conflict", clause: cid, level }));
          r.conflict = cid;
          r.outcome = "conflict";
          // What CDCL would learn: analysis needs a literal of the
          // conflict clause at the current level.
          if (level > 0 && s.clauses_[cid].lits.some((l) => s.level[lit_var(l)] === level)) {
            const tracing = s.tracer.enabled;
            s.tracer.enabled = false;
            const [lits] = s.analyze(cid);
            s.tracer.enabled = tracing;
            r.learned = lits;
          }
          return false;
        } else if (fp.kind === "Unknown") {
          r.outcome = "unknown";
          r.note = fp._0;
          return false;
        }
        // A waiting one-literal clause whose literal became false
        // (another unit clause forced the opposite): a conflict.
        const falsified = s.pending_units.find(([c, l]) => s.clauses_[c].lits.length === 1 && s.lit_value(l) === false);
        if (falsified !== undefined) {
          const cid = falsified[0];
          const level = s.decision_level();
          s.tracer.push(() => ({ kind: "Conflict", clause: cid, level }));
          r.conflict = cid;
          r.outcome = "conflict";
          return false;
        }
        s.refresh_pending_units();
        if (s.pending_units.length === 0) {
          return true;
        }
        // Internal helper atoms, or one literal forced by every unit
        // clause: nothing to choose.
        const lits: Lit[] = [];
        for (const [, l] of s.pending_units) {
          if (!lits.includes(l)) {
            lits.push(l);
          }
        }
        let auto: [number, Lit] | null = s.pending_units.find(([, l]) => !choosable(l)) ?? null;
        if (auto === null && lits.length === 1) {
          auto = s.pending_units[0];
        }
        if (auto !== null) {
          s.enqueue(auto[1], auto[0]);
          continue;
        }
        const act = next.v < actions.length ? actions[next.v] : null;
        if (act !== null && act.kind === "Pick") {
          const p = act._0;
          next.v += 1;
          const found = s.pending_units.find(([, l]) => l === p);
          if (found !== undefined) {
            s.enqueue(found[1], found[0]);
          }
        } else {
          r.outcome = "units";
          r.units = s.pending_units.slice();
          return false;
        }
      }
    };
    if (!check(this, r, next)) {
      return r;
    }
    // Decisions on atoms that a theory only creates later (e.g. a split
    // atom made by the final check) wait until the atom exists.
    const deferred: [number, Lit][] = [];
    const decide_user = (s: Solver, d: Lit) => {
      s.decide_traced(d, 0, [], new DecisionOrigin({ by: "user", why: "chosen in the playground" }));
    };
    while (next.v < actions.length) {
      const i = next.v;
      next.v += 1;
      // a pick that no choice point asked for is out of date: ignore it
      const a = actions[i];
      if (a.kind !== "Decide") {
        continue;
      }
      const d = a._0;
      if (lit_var(d) >= this.num_vars_) {
        deferred.push([i, d]);
        continue;
      }
      const v = this.lit_value(d);
      if (v !== null) {
        r.skipped.push([i, v]);
        continue;
      }
      decide_user(this, d);
      r.applied = i + 1;
      if (!check(this, r, next)) {
        return r;
      }
    }
    for (;;) {
      // Apply deferred decisions whose atom exists by now.
      const pos = deferred.findIndex(([, d]) => lit_var(d) < this.num_vars_);
      if (pos !== -1) {
        const [i, d] = deferred.splice(pos, 1)[0];
        const v = this.lit_value(d);
        if (v !== null) {
          r.skipped.push([i, v]);
        } else {
          decide_user(this, d);
          r.applied = Math.max(r.applied, i + 1);
          if (!check(this, r, next)) {
            return r;
          }
        }
        continue;
      }
      // All problem clauses satisfied? Then ask the theories for a verdict.
      const open = this.problem_clause_ids().some((id) => open_size(this.value_, this.clauses_[id].lits) !== null);
      if (open) {
        r.outcome = "open";
        break;
      }
      if (this.hook === null) {
        r.outcome = "sat";
        break;
      }
      const a = this.call_hook(true);
      if (a.kind === "Nothing") {
        r.outcome = "sat";
        break;
      } else if (a.kind === "Split") {
        const lit = a._0;
        if (deferred.some(([, d]) => lit_var(d) === lit_var(lit))) {
          continue; // the user already chose this split
        }
        r.outcome = "split";
        r.split = [lit, a._1, a._2];
        break;
      } else if (a.kind === "Conflict") {
        const cid = a._0;
        const level = this.decision_level();
        this.tracer.push(() => ({ kind: "Conflict", clause: cid, level }));
        r.conflict = cid;
        r.outcome = "conflict";
        break;
      } else if (a.kind === "Progress") {
        if (!check(this, r, next)) {
          return r;
        }
      } else {
        r.outcome = "unknown";
        r.note = a._0;
        break;
      }
    }
    for (const [i] of deferred) {
      r.skipped.push([i, false]);
    }
    return r;
  }

  problem_clause_ids(): number[] {
    const ids: number[] = [];
    for (let i = 0; i < this.num_original_; i++) ids.push(i);
    for (const id of this.extra_problem) ids.push(id);
    return ids;
  }

  /// Unit propagation with two watched literals. Returns a conflicting
  /// clause id, or None when the queue is exhausted without conflict.
  propagate(): number | null {
    const value = this.value_;
    while (this.qhead < this.trail_.length) {
      const p = this.trail_[this.qhead];
      this.qhead += 1;
      const false_lit = lit_not(p);
      const ws = this.watches[lit_index(false_lit)];
      this.watches[lit_index(false_lit)] = [];
      let i = 0;
      let j = 0;
      let conflict: number | null = null;

      while (i < ws.length) {
        const w = ws[i];
        i += 1;
        // Clause already satisfied by its blocker: skip without reading it.
        if (lit_val(value, w.blocker) === true) {
          ws[j] = w;
          j += 1;
          continue;
        }
        const cid = w.cid;
        const lits = this.clauses_[cid].lits;
        // Keep the falsified watch at position 1.
        if (lits[0] === false_lit) {
          lits[0] = lits[1];
          lits[1] = false_lit;
        }
        const first = lits[0];
        const kept: Watch = { cid, blocker: first };
        if (lit_val(value, first) === true) {
          ws[j] = kept;
          j += 1;
          continue;
        }
        // Look for a non-false literal to watch instead.
        let moved = false;
        for (let k = 2; k < lits.length; k++) {
          if (lit_val(value, lits[k]) !== false) {
            const t = lits[1];
            lits[1] = lits[k];
            lits[k] = t;
            this.watches[lit_index(lits[1])].push(kept);
            moved = true;
            break;
          }
        }
        if (moved) {
          continue;
        }
        // No replacement: the clause is unit or conflicting.
        ws[j] = kept;
        j += 1;
        if (lit_val(value, first) === false) {
          conflict = cid;
          while (i < ws.length) {
            ws[j] = ws[i];
            j += 1;
            i += 1;
          }
        } else if (this.manual_units) {
          if (!this.pending_units.some(([c]) => c === cid)) {
            this.pending_units.push([cid, first]);
          }
        } else {
          this.enqueue(first, cid);
        }
      }

      ws.length = j;
      this.watches[lit_index(false_lit)] = ws;
      if (conflict !== null) {
        return conflict;
      }
    }
    return null;
  }

  /// MOMS: among unsatisfied clauses of minimum open size, pick the
  /// variable maximising `(f(x)+f(¬x)) * 2^k + f(x)*f(¬x)`; ties go to the
  /// lowest variable index, polarity to the more frequent literal.
  /// Only problem clauses (originals and axioms) are scored: learned and
  /// theory clauses are implied by them, and rescanning tens of thousands
  /// of learned clauses at every decision made the solver quadratic.
  /// Returns None when every problem clause is satisfied.
  pick_branch(): [Lit, number, MomsCandidate[]] | null {
    const ids = this.problem_clause_ids();
    let min_size: number | null = null;
    for (const id of ids) {
      const sz = open_size(this.value_, this.clauses_[id].lits);
      if (sz !== null && (min_size === null || sz < min_size)) {
        min_size = sz;
      }
    }
    if (min_size === null) {
      return null;
    }

    this.moms_count.fill(0);
    for (const id of ids) {
      const c = this.clauses_[id];
      if (open_size(this.value_, c.lits) === min_size) {
        for (const l of c.lits) {
          if (lit_val(this.value_, l) === null) {
            this.moms_count[lit_index(l)] += 1;
          }
        }
      }
    }

    const score_of = (v: number, counts: number[]): [number, number, number] => {
      const p = counts[lit_index(lit_new(v, true))];
      const n = counts[lit_index(lit_new(v, false))];
      const s = (p + n) * 2 ** MOMS_K;
      return [p, n, s + p * n];
    };

    let best: [number, number] | null = null;
    for (let v = 0; v < this.num_vars_; v++) {
      const [p, n, s] = score_of(v, this.moms_count);
      if (p + n > 0 && (best === null || s > best[1])) {
        best = [v, s];
      }
    }
    if (best === null) {
      throw new Error("an open clause has an unassigned literal");
    }
    const v = best[0];
    const [p, n] = score_of(v, this.moms_count);
    const lit = lit_new(v, p >= n);

    let candidates: MomsCandidate[] = [];
    if (this.tracer.enabled) {
      for (let u = 0; u < this.num_vars_; u++) {
        const [p, n, s] = score_of(u, this.moms_count);
        if (p + n > 0) {
          candidates.push(new MomsCandidate({ var: u + 1, pos: p, neg: n, score: s }));
        }
      }
      candidates.sort((a, b) => b.score - a.score || a.var - b.var);
      candidates = candidates.slice(0, TRACED_CANDIDATES);
    }
    return [lit, min_size, candidates];
  }

  /// First-UIP conflict analysis. Returns the learned clause with the
  /// asserting literal at index 0 and the highest-level remaining literal
  /// at index 1, the backjump level, and the resolved-away variables
  /// (1-based, the conflict side of the cut).
  analyze(confl: number): [Lit[], number, number[]] {
    const cur = this.decision_level();
    const tracing = this.tracer.enabled;
    const lower: Lit[] = [];
    let counter = 0;
    const conflict_side: number[] = [];
    let resolvent: Lit[] = tracing ? this.clauses_[confl].lits.slice() : [];
    let first_step = true;

    let clause = confl;
    let skip: Lit | null = null;
    let idx = this.trail_.length;
    let uip: Lit;
    for (;;) {
      const cl = this.clauses_[clause].lits;
      for (let k = 0; k < cl.length; k++) {
        const l = cl[k];
        if (l === skip) {
          continue;
        }
        const v = lit_var(l);
        if (!this.seen[v]) {
          this.seen[v] = true;
          if (this.level[v] === cur) {
            counter += 1;
          } else {
            lower.push(l);
          }
        }
      }

      // Most recently assigned marked literal (always at level `cur`).
      for (;;) {
        idx -= 1;
        if (this.seen[lit_var(this.trail_[idx])]) {
          break;
        }
      }
      const p = this.trail_[idx];
      this.seen[lit_var(p)] = false;
      counter -= 1;
      if (counter === 0) {
        uip = p;
        break;
      }

      const r = this.reason[lit_var(p)];
      if (r === null) {
        throw new Error("non-UIP literal at the conflict level is implied");
      }
      if (tracing) {
        const next = resolve(resolvent, this.clauses_[r].lits, p);
        const a = to_dimacs_sorted(resolvent);
        const a_id = first_step ? confl : null;
        const res = to_dimacs_sorted(next);
        const pivot = lit_var(p) + 1;
        this.tracer.push(() => ({
          kind: "Resolve",
          clause_a: a,
          clause_a_id: a_id,
          clause_b: r,
          pivot,
          resolvent: res,
        }));
        resolvent = next;
      }
      first_step = false;
      conflict_side.push(lit_var(p) + 1);
      clause = r;
      skip = p;
    }

    const lits: Lit[] = [lit_not(uip)];
    for (const l of lower) lits.push(l);
    for (let k = 1; k < lits.length; k++) {
      this.seen[lit_var(lits[k])] = false;
    }

    let bt = 0;
    let max_i = 1;
    for (let i = 1; i < lits.length; i++) {
      const l = lits[i];
      if (this.level[lit_var(l)] > bt) {
        bt = this.level[lit_var(l)];
        max_i = i;
      }
    }
    if (lits.length > 1) {
      const t = lits[1];
      lits[1] = lits[max_i];
      lits[max_i] = t;
    }
    return [lits, bt, conflict_side];
  }

  learn_and_backjump(confl: number): void {
    const [lits, bt, conflict_side] = this.analyze(confl);
    const id = this.clauses_.length;
    this.stats.learned += 1;
    this.tracer.push(() => ({
      kind: "Learn",
      clause: id,
      lits: to_dimacs_sorted(lits),
      uip: lit_to_dimacs(lit_not(lits[0])),
      conflict_side,
      reason_side: lits.map((l) => lit_var(l) + 1),
      backjump_level: bt,
    }));
    const levels = new Set(lits.map((l) => this.level[lit_var(l)]));
    this.backjump(bt);
    if (lits.length >= 2) {
      this.watches[lit_index(lits[0])].push({ cid: id, blocker: lits[1] });
      this.watches[lit_index(lits[1])].push({ cid: id, blocker: lits[0] });
    }
    const asserting = lits[0];
    this.clauses_.push(new Clause({ lits, learnt: true, kind: "Learned", lbd: levels.size, deleted: false }));
    this.learnts_alive += 1;
    this.enqueue(asserting, id);
  }

  /// A clause is locked while it is the reason of a current assignment
  /// (its implied literal is always `lits[0]`).
  is_locked(id: number): boolean {
    const c = this.clauses_[id];
    return c.lits.length !== 0 && this.reason[lit_var(c.lits[0])] === id;
  }

  /// Delete the worse half of the unlocked learned clauses: highest LBD
  /// first, then longest. "Glue" clauses (LBD ≤ 2) are always kept.
  /// Clause ids stay valid; deleted clauses just become empty.
  /// (Rust: `fn reduce_db`; renamed because of the `reduce_db` field.)
  reduce_db_(): void {
    const candidates: number[] = [];
    for (let id = this.num_original_; id < this.clauses_.length; id++) {
      const c = this.clauses_[id];
      if (c.learnt && !c.deleted && (c.lbd > 2 || c.kind === "Theory") && !this.is_locked(id)) {
        candidates.push(id);
      }
    }
    candidates.sort((x, y) => {
      const a = this.clauses_[x];
      const b = this.clauses_[y];
      return b.lbd - a.lbd || b.lits.length - a.lits.length;
    });
    const remove = Math.trunc(candidates.length / 2);
    for (const id of candidates.slice(0, remove)) {
      const c = this.clauses_[id];
      c.deleted = true;
      c.lits = [];
    }
    const clauses = this.clauses_;
    for (let k = 0; k < this.watches.length; k++) {
      this.watches[k] = this.watches[k].filter((w) => !clauses[w.cid].deleted);
    }
    this.learnts_alive -= remove;
    this.stats.deleted += remove;
  }

  backjump(to: number): void {
    const from = this.decision_level();
    if (from <= to) {
      return;
    }
    const start = this.trail_lim[to];
    for (let k = start; k < this.trail_.length; k++) {
      const l = this.trail_[k];
      this.value_[lit_var(l)] = null;
      this.reason[lit_var(l)] = null;
    }
    const unassigned = this.trail_.splice(start);
    this.trail_lim.length = to;
    this.qhead = start;
    const trail_len = this.trail_.length;
    if (this.hook !== null) {
      this.hook.backjump(to, trail_len);
    }
    this.tracer.push(() => ({
      kind: "Backjump",
      from,
      to,
      unassigned: unassigned.map(lit_to_dimacs),
    }));
  }
}

export { to_dimacs_sorted };
