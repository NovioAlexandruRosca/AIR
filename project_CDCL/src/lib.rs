//! CDCL SAT solver with a step-by-step trace for visualization.
//!
//! - [`dimacs`] — DIMACS CNF parser
//! - [`solver`] — CDCL (2WL BCP, MOMS, First-UIP, backjumping)
//! - [`trace`] — trace events and their JSON encoding

pub mod dimacs;
pub mod lit;
pub mod solver;
pub mod trace;

use solver::{Solver, Status};
use std::fmt::Write;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::{Duration, Instant};
use trace::{json_string, Tracer};

pub use dimacs::{parse, Cnf, ParseError};
pub use lit::Lit;

/// Default cap on recorded events; beyond it the solver keeps running but
/// stops recording (the UI shows the trace as truncated).
pub const DEFAULT_TRACE_LIMIT: usize = 20_000;

/// Wall-clock timings in milliseconds, reported in the trace JSON.
#[derive(Debug, Clone, Copy, Default)]
pub struct Timing {
    pub parse_ms: f64,
    /// Solve time of the run that recorded the trace (includes tracing cost).
    pub solve_ms: f64,
    /// Solve time of an identical run without tracing: the solver's real speed.
    pub solve_untraced_ms: Option<f64>,
}

/// Ways to stop a solve early; it then ends with status UNKNOWN.
#[derive(Debug, Clone, Default)]
pub struct Limits {
    pub max_conflicts: Option<u64>,
    pub timeout: Option<Duration>,
    /// Set from another thread to stop the solve.
    pub cancel: Option<Arc<AtomicBool>>,
    /// Never delete learned clauses (see `Solver::reduce_db`).
    pub no_reduce: bool,
}

fn ms_since(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
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
pub fn solve_to_json(cnf: &Cnf, trace_limit: usize, limits: &Limits, parse_ms: f64) -> String {
    let deadline = limits.timeout.map(|t| Instant::now() + t);
    let configure = |s: &mut Solver| {
        s.max_conflicts = limits.max_conflicts;
        s.deadline = deadline;
        s.cancel = limits.cancel.clone();
        s.reduce_db = !limits.no_reduce;
    };

    let start = Instant::now();
    let mut solver = Solver::with_tracer(cnf, Tracer::with_limit(trace_limit));
    configure(&mut solver);
    let status = solver.solve();
    let solve_ms = ms_since(start);

    // Re-running a long solve would double the wait; past ~1 s the tracing
    // overhead (capped by the trace limit) is negligible anyway.
    let mut solve_untraced_ms = None;
    if status != Status::Unknown && solve_ms < 1000.0 {
        let start = Instant::now();
        let mut plain = Solver::new(cnf);
        configure(&mut plain);
        // A time limit or cancel hitting this second run would make its time meaningless.
        if plain.solve() != Status::Unknown {
            solve_untraced_ms = Some(ms_since(start));
        }
    }
    let timing = Timing {
        parse_ms,
        solve_ms,
        solve_untraced_ms,
    };
    run_json(cnf, &solver, status, &timing)
}

pub fn run_json(cnf: &Cnf, solver: &Solver, status: Status, timing: &Timing) -> String {
    let mut out = String::with_capacity(1024 + solver.tracer.events.len() * 64);
    let _ = write!(
        out,
        r#"{{"num_vars":{},"num_original":{},"clauses":["#,
        cnf.num_vars,
        cnf.clauses.len()
    );
    // Original clauses in input order (the solver permutes its own copies).
    for (i, c) in cnf.clauses.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('[');
        for (j, l) in solver::dedup_clause(c).iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            let _ = write!(out, "{}", l.to_dimacs());
        }
        out.push(']');
    }
    out.push_str(r#"],"warnings":["#);
    for (i, w) in cnf.warnings.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_string(&mut out, w);
    }
    let verified = status == Status::Sat && solver::verify_model(cnf, solver.model());
    let _ = write!(
        out,
        r#"],"status":"{}","stop_reason":{},"verified":{},"truncated":{},"model":["#,
        status.as_str(),
        solver
            .stop_reason
            .map_or("null".to_string(), |r| format!("\"{}\"", r.as_str())),
        verified,
        solver.tracer.truncated
    );
    for (i, x) in solver.model_dimacs().iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{x}");
    }
    let st = &solver.stats;
    let _ = write!(
        out,
        r#"],"stats":{{"decisions":{},"propagations":{},"conflicts":{},"learned":{},"deleted":{},"max_level":{}}},"moms_k":{},"#,
        st.decisions,
        st.propagations,
        st.conflicts,
        st.learned,
        st.deleted,
        st.max_level,
        solver::MOMS_K
    );
    let untraced = timing
        .solve_untraced_ms
        .map_or("null".to_string(), |t| format!("{t:.4}"));
    let _ = write!(
        out,
        r#""timing":{{"parse_ms":{:.4},"solve_ms":{:.4},"solve_untraced_ms":{}}},"events":["#,
        timing.parse_ms, timing.solve_ms, untraced
    );
    for (i, e) in solver.tracer.events.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        e.write_json(&mut out);
    }
    out.push_str("]}");
    out
}
