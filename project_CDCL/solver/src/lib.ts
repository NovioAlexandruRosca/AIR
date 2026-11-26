//! CDCL SAT solver with a step-by-step trace for visualization.
//!
//! - [`dimacs`] — DIMACS CNF parser
//! - [`solver`] — CDCL (2WL BCP, MOMS, First-UIP, backjumping)
//! - [`trace`] — trace events and their JSON encoding
//! - [`smt`] — CDCL(T): SMT-LIB front end, LIA and DT theories,
//!   Nelson–Oppen combination

import { Cnf } from "./dimacs";
import { lit_to_dimacs } from "./lit";
import { Solver, Status, Status_as_str, StopReason_as_str, dedup_clause, verify_model, MOMS_K } from "./solver";
import { Event_write_json, json_string, Tracer } from "./trace";
import { now } from "./util";

export { parse, Cnf, ParseError } from "./dimacs";
export type { Lit } from "./lit";

/// Default cap on recorded events; beyond it the solver keeps running but
/// stops recording (the UI shows the trace as truncated).
export const DEFAULT_TRACE_LIMIT = 20_000;

/// Wall-clock timings in milliseconds, reported in the trace JSON.
export class Timing {
  parse_ms = 0;
  /// Solve time of the run that recorded the trace (includes tracing cost).
  solve_ms = 0;
  /// Solve time of an identical run without tracing: the solver's real speed.
  solve_untraced_ms: number | null = null;
  constructor(init?: Partial<Timing>) {
    Object.assign(this, init ?? {});
  }
  static default(): Timing {
    return new Timing();
  }
}

/// Ways to stop a solve early; it then ends with status UNKNOWN.
export class Limits {
  max_conflicts: number | null = null;
  /// Milliseconds (Rust: `Duration`).
  timeout: number | null = null;
  /// Set from elsewhere to stop the solve.
  cancel: { value: boolean } | null = null;
  /// Never delete learned clauses (see `Solver::reduce_db`).
  no_reduce = false;
  constructor(init?: Partial<Limits>) {
    Object.assign(this, init ?? {});
  }
  static default(): Limits {
    return new Limits();
  }
}

function ms_since(start: number): number {
  return now() - start;
}

/// Solve `cnf` while recording a trace, and return the whole run as JSON:
///
/// ```text
/// { "num_vars", "num_original", "clauses": [[lits]...], "warnings": [..],
///   "status", "model", "verified", "truncated", "stats": {..},
///   "timing": {..}, "events": [..] }
/// ```
///
/// The formula is solved twice: first with tracing to record the events,
/// then without tracing to measure the solver's own speed (second, so it
/// runs with warm caches). The solver is deterministic, so both runs take
/// exactly the same steps. If the traced run was stopped early, the
/// untraced run is skipped.
export function solve_to_json(cnf: Cnf, trace_limit: number, limits: Limits, parse_ms: number): string {
  const deadline = limits.timeout === null ? null : now() + limits.timeout;
  const configure = (s: Solver) => {
    s.max_conflicts = limits.max_conflicts;
    s.deadline = deadline;
    s.cancel = limits.cancel;
    s.reduce_db = !limits.no_reduce;
  };

  let start = now();
  const solver = Solver.with_tracer(cnf, Tracer.with_limit(trace_limit));
  configure(solver);
  const status = solver.solve();
  const solve_ms = ms_since(start);

  // Re-running a long solve would double the wait; past ~1 s the tracing
  // overhead (capped by the trace limit) is negligible anyway.
  let solve_untraced_ms: number | null = null;
  if (status !== "Unknown" && solve_ms < 1000.0) {
    start = now();
    const plain = Solver.new(cnf);
    configure(plain);
    // A time limit or cancel hitting this second run would make its time meaningless.
    if (plain.solve() !== "Unknown") {
      solve_untraced_ms = ms_since(start);
    }
  }
  const timing = new Timing({ parse_ms, solve_ms, solve_untraced_ms });
  return run_json(cnf, solver, status, timing);
}

export function run_json(cnf: Cnf, solver: Solver, status: Status, timing: Timing): string {
  return run_json_ext(cnf, solver, status, timing, "");
}

/// Like [`run_json`]; `extra` is inserted as additional top-level fields
/// (e.g. `"smt":{...},`), and must end with a comma when not empty.
export function run_json_ext(cnf: Cnf, solver: Solver, status: Status, timing: Timing, extra: string): string {
  const out = { v: "" };
  out.v += `{"num_vars":${cnf.num_vars},"num_original":${cnf.clauses.length},"clauses":[`;
  // Original clauses in input order (the solver permutes its own copies).
  cnf.clauses.forEach((c, i) => {
    if (i > 0) {
      out.v += ",";
    }
    out.v += "[";
    dedup_clause(c).forEach((l, j) => {
      if (j > 0) {
        out.v += ",";
      }
      out.v += String(lit_to_dimacs(l));
    });
    out.v += "]";
  });
  out.v += `],"warnings":[`;
  cnf.warnings.forEach((w, i) => {
    if (i > 0) {
      out.v += ",";
    }
    json_string(out, w);
  });
  const verified = status === "Sat" && verify_model(cnf, solver.model());
  const stop = solver.stop_reason === null ? "null" : `"${StopReason_as_str(solver.stop_reason)}"`;
  out.v += `],"status":"${Status_as_str(status)}","stop_reason":${stop},"verified":${verified},"truncated":${solver.tracer.truncated},"model":[`;
  solver.model_dimacs().forEach((x, i) => {
    if (i > 0) {
      out.v += ",";
    }
    out.v += String(x);
  });
  const st = solver.stats;
  out.v += `],"stats":{"decisions":${st.decisions},"propagations":${st.propagations},"conflicts":${st.conflicts},"learned":${st.learned},"deleted":${st.deleted},"max_level":${st.max_level},"theory_propagations":${st.theory_propagations},"theory_conflicts":${st.theory_conflicts},"theory_splits":${st.theory_splits}},"moms_k":${MOMS_K},`;
  out.v += extra;
  const untraced = timing.solve_untraced_ms === null ? "null" : timing.solve_untraced_ms.toFixed(4);
  out.v += `"timing":{"parse_ms":${timing.parse_ms.toFixed(4)},"solve_ms":${timing.solve_ms.toFixed(4)},"solve_untraced_ms":${untraced}},"events":[`;
  const events = solver.tracer.events;
  const parts: string[] = [];
  for (let i = 0; i < events.length; i++) {
    const e = { v: "" };
    Event_write_json(events[i], e);
    parts.push(e.v);
  }
  out.v += parts.join(",\n");
  out.v += "]}";
  return out.v;
}
