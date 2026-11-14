//! CDCL(T): satisfiability modulo theories on top of the CDCL solver.
//!
//! Pipeline: SMT-LIB text → terms ([`parser`]) → purification + Tseitin
//! ([`preprocess`]) → CDCL search where the [`combine::Combination`] of
//! theories is the solver's theory hook → model built by the theories and
//! verified by evaluating every assertion.
//!
//! Adding a theory: implement [`theory::Theory`] and add it to
//! [`default_theories`]. Parsing, purification, Nelson–Oppen combination and
//! the SAT solver need no change.

pub mod combine;
pub mod dt;
pub mod lia;
pub mod parser;
pub mod preprocess;
pub mod rat;
pub mod sexp;
pub mod term;
pub mod theory;

use crate::solver::{Action, Replay, Solver, Status};
use crate::trace::{json_string, Tracer};
use crate::{run_json_ext, Limits, Lit, Timing};
use combine::{Combination, HookAdapter};
use parser::{parse_problem, Problem};
use preprocess::{preprocess, Prep};
use sexp::SmtError;
use std::cell::RefCell;
use std::fmt::Write;
use std::rc::Rc;
use std::time::Instant;
use term::{TermId, Value, BOOL};
use theory::Theory;

pub use parser::looks_like_smtlib;

/// The theories every SMT problem is solved with, in registration order.
/// To add a theory, implement `Theory` and list it here.
pub fn default_theories() -> Vec<Box<dyn Theory>> {
    vec![Box::new(lia::Lia::new()), Box::new(dt::Dt::new())]
}

pub struct Prepared {
    pub comb: Rc<RefCell<Combination>>,
    pub problem: Problem,
    pub prep: Prep,
    pub parse_ms: f64,
}

/// Parse and preprocess an SMT-LIB problem.
pub fn prepare(text: &str) -> Result<Prepared, SmtError> {
    let start = Instant::now();
    let mut comb = Combination::new(default_theories());
    let problem = parse_problem(text, &mut comb.terms, &mut comb.theories)?;
    let prep = preprocess(&problem, &mut comb)?;
    Ok(Prepared {
        comb: Rc::new(RefCell::new(comb)),
        problem,
        prep,
        parse_ms: start.elapsed().as_secs_f64() * 1000.0,
    })
}

#[derive(Debug, Clone)]
pub struct ModelEntry {
    pub name: String,
    pub sort: String,
    pub value: String,
}

pub struct SmtResult {
    pub status: Status,
    pub solver: Solver,
    pub prepared: Prepared,
    pub model: Vec<ModelEntry>,
    /// Every assertion evaluates to true under the model (SAT only).
    pub verified: Option<bool>,
    pub timing: Timing,
}

fn configure(s: &mut Solver, limits: &Limits, start: Instant) {
    s.max_conflicts = limits.max_conflicts;
    s.deadline = limits.timeout.map(|t| start + t);
    s.cancel = limits.cancel.clone();
    s.reduce_db = !limits.no_reduce;
}

pub fn solve(
    text: &str,
    trace_limit: Option<usize>,
    limits: &Limits,
) -> Result<SmtResult, SmtError> {
    let prepared = prepare(text)?;
    let tracer = match trace_limit {
        Some(l) => Tracer::with_limit(l),
        None => Tracer::disabled(),
    };
    let mut solver = Solver::with_tracer(&prepared.prep.cnf, tracer);
    let start = Instant::now();
    configure(&mut solver, limits, start);
    solver.hook = Some(Box::new(HookAdapter(prepared.comb.clone())));
    let status = solver.solve();
    let solve_ms = start.elapsed().as_secs_f64() * 1000.0;
    let (model, verified) = if status == Status::Sat {
        extract_model(&prepared, &solver)
    } else {
        (Vec::new(), None)
    };
    Ok(SmtResult {
        status,
        solver,
        timing: Timing {
            parse_ms: prepared.parse_ms,
            solve_ms,
            solve_untraced_ms: None,
        },
        prepared,
        model,
        verified,
    })
}

fn extract_model(p: &Prepared, solver: &Solver) -> (Vec<ModelEntry>, Option<bool>) {
    let comb = p.comb.borrow();
    let sat_model = solver.model();
    let bools = |t: TermId| -> Option<bool> {
        // After a full solve the SAT model is set; after a playground replay
        // read the current assignment instead.
        let v = p.prep.bool_vars.get(&t).copied();
        Some(
            v.and_then(|v| {
                if sat_model.is_empty() {
                    solver.value(Lit::new(v, true))
                } else {
                    sat_model.get(v).copied()
                }
            })
            .unwrap_or(false),
        )
    };
    let mut entries = Vec::new();
    for &c in &p.problem.consts {
        let terms = &comb.terms;
        let value = if terms.sort(c) == BOOL {
            Some(Value::Bool(bools(c).unwrap_or(false)))
        } else {
            comb.eval(c, &bools)
        };
        entries.push(ModelEntry {
            name: terms.var_name(c).unwrap_or("?").to_string(),
            sort: terms.sort_name(terms.sort(c)).to_string(),
            value: value.map(|v| v.to_string()).unwrap_or_else(|| "?".into()),
        });
    }
    let verified = comb.model_ready
        && p.problem
            .assertions
            .iter()
            .all(|&a| comb.eval(a, &bools) == Some(Value::Bool(true)));
    (entries, Some(verified))
}

fn json_list(out: &mut String, items: impl IntoIterator<Item = String>) {
    out.push('[');
    for (i, s) in items.into_iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_string(out, &s);
    }
    out.push(']');
}

/// The `"smt":{...},` section of a trace.
fn smt_section(
    p: &Prepared,
    solver: &Solver,
    model: &[ModelEntry],
    verified: Option<bool>,
    all_vars: bool,
) -> String {
    let comb = p.comb.borrow();
    let terms = &comb.terms;
    let mut s = String::from("\"smt\":{\"theories\":");
    json_list(&mut s, comb.theories.iter().map(|t| t.name().to_string()));
    s.push_str(",\"assertions\":");
    json_list(&mut s, p.prep.assertions.iter().cloned());
    s.push_str(",\"purified\":");
    json_list(&mut s, p.prep.purified.iter().cloned());
    s.push_str(",\"definitions\":");
    json_list(&mut s, p.prep.definitions.iter().map(|&d| terms.display(d)));
    s.push_str(",\"fresh\":");
    json_list(&mut s, p.prep.fresh.iter().map(|&f| terms.display(f)));
    s.push_str(",\"shared\":[");
    for (i, &v) in comb.shared.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str("{\"name\":");
        json_string(&mut s, &terms.display(v));
        s.push_str(",\"theories\":");
        json_list(
            &mut s,
            comb.uses
                .get(&v)
                .map(|u| {
                    u.iter()
                        .map(|&t| comb.theory_name(t).to_string())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default(),
        );
        s.push('}');
    }
    s.push_str("],\"interface\":[");
    for (i, &(x, y, v)) in comb.interface.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str("{\"x\":");
        json_string(&mut s, &terms.display(x));
        s.push_str(",\"y\":");
        json_string(&mut s, &terms.display(y));
        let _ = write!(s, ",\"var\":{}}}", v + 1);
    }
    s.push_str("],\"vars\":[");
    let n = if all_vars {
        comb.vars.len()
    } else {
        p.prep.cnf.num_vars
    };
    for (i, info) in comb.vars.iter().take(n).enumerate() {
        if i > 0 {
            s.push(',');
        }
        info.write_json(i, &mut s);
    }
    s.push_str("],\"clause_origin\":");
    json_list(&mut s, p.prep.clause_origin.iter().cloned());
    s.push_str(",\"model\":[");
    for (i, m) in model.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str("{\"name\":");
        json_string(&mut s, &m.name);
        s.push_str(",\"sort\":");
        json_string(&mut s, &m.sort);
        s.push_str(",\"value\":");
        json_string(&mut s, &m.value);
        s.push('}');
    }
    let _ = write!(
        s,
        "],\"model_verified\":{},\"incomplete\":",
        verified.map_or("null".to_string(), |v| v.to_string())
    );
    match &solver.incomplete_reason {
        Some(r) => json_string(&mut s, r),
        None => s.push_str("null"),
    }
    s.push_str(",\"final\":");
    s.push_str(&comb.snapshot_all());
    s.push_str("},");
    s
}

/// Full trace JSON of an SMT run (same format as SAT traces plus "smt").
pub fn result_json(r: &SmtResult) -> String {
    let extra = smt_section(&r.prepared, &r.solver, &r.model, r.verified, false);
    run_json_ext(&r.prepared.prep.cnf, &r.solver, r.status, &r.timing, &extra)
}

/// Solve and return the JSON trace (used by the web server).
pub fn solve_to_json(text: &str, trace_limit: usize, limits: &Limits) -> Result<String, SmtError> {
    let r = solve(text, Some(trace_limit), limits)?;
    Ok(result_json(&r))
}

fn replay_section(solver: &Solver, r: &Replay, theories: Option<String>) -> String {
    let mut s = format!(
        "\"replay\":{{\"outcome\":\"{}\",\"applied\":{},\"conflict\":{},\"skipped\":[",
        r.outcome,
        r.applied,
        r.conflict.map_or("null".to_string(), |c| c.to_string())
    );
    for (i, (idx, v)) in r.skipped.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "[{idx},{v}]");
    }
    s.push_str("],\"split\":");
    match &r.split {
        Some((lit, by, why)) => {
            let _ = write!(s, "{{\"lit\":{},\"by\":", lit.to_dimacs());
            json_string(&mut s, by);
            s.push_str(",\"why\":");
            json_string(&mut s, why);
            s.push('}');
        }
        None => s.push_str("null"),
    }
    let _ = write!(
        s,
        ",\"finish_from\":{}",
        r.finish_from.map_or("null".to_string(), |n| n.to_string())
    );
    s.push_str(",\"learned\":");
    match &r.learned {
        Some(c) => {
            s.push('[');
            for (i, l) in c.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                let _ = write!(s, "{}", l.to_dimacs());
            }
            s.push(']');
        }
        None => s.push_str("null"),
    }
    s.push_str(",\"units\":[");
    for (i, (cid, l)) in r.units.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "{{\"clause\":{cid},\"lit\":{}}}", l.to_dimacs());
    }
    s.push_str("],\"note\":");
    match &r.note {
        Some(n) => json_string(&mut s, n),
        None => s.push_str("null"),
    }
    s.push_str(",\"trail\":[");
    for (i, &l) in solver.trail().iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(
            s,
            "{{\"lit\":{},\"level\":{},\"reason\":{}}}",
            l.to_dimacs(),
            solver.var_level(l.var()),
            solver
                .var_reason(l.var())
                .map_or("null".to_string(), |c| c.to_string())
        );
    }
    s.push_str("],\"db\":[");
    for (i, c) in solver.clauses().iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push('[');
        for (j, l) in c.lits.iter().enumerate() {
            if j > 0 {
                s.push(',');
            }
            let _ = write!(s, "{}", l.to_dimacs());
        }
        s.push(']');
    }
    s.push_str("],\"open\":[");
    for (i, v) in open_vars(solver).iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "{}", v + 1);
    }
    let _ = write!(s, "],\"num_vars\":{},\"theories\":", solver.num_vars());
    s.push_str(theories.as_deref().unwrap_or("null"));
    s.push_str("},");
    s
}

/// Playground: replay the user's decisions on a fresh solver (SAT or SMT
/// input) and report the resulting state. Stateless, so every click is an
/// independent, reproducible request.
/// The assertions as written, as JSON trees whose leaves point at the
/// Boolean variables of their (purified) atoms: what the playground shows
/// and lets the user click.
fn formula_json(p: &Prepared) -> String {
    fn tree(comb: &Combination, prep: &Prep, t: TermId, out: &mut String) {
        let terms = &comb.terms;
        let node = terms.node(t);
        let connective = match terms.sym(t) {
            Some(s @ ("and" | "or" | "not" | "=>" | "xor" | "ite")) => Some(s),
            Some("=") if terms.sort(node.args[0]) == BOOL => Some("iff"),
            _ => None,
        };
        match &node.op {
            term::Op::True => out.push_str("{\"const\":true}"),
            term::Op::False => out.push_str("{\"const\":false}"),
            _ if connective.is_some() => {
                let _ = write!(out, "{{\"op\":\"{}\",\"args\":[", connective.unwrap());
                for (i, &a) in node.args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    tree(comb, prep, a, out);
                }
                out.push_str("]}");
            }
            _ => {
                let var = match &node.op {
                    term::Op::Var(_) => prep.bool_vars.get(&t).copied(),
                    _ => {
                        let pure = prep.atom_map.get(&t).copied().unwrap_or(t);
                        comb.atom_of.get(&pure).copied()
                    }
                };
                let _ = write!(out, "{{\"atom\":{},\"label\":", var.map_or(0, |v| v + 1));
                json_string(out, &terms.display(t));
                out.push('}');
            }
        }
    }
    let comb = p.comb.borrow();
    let mut s = String::from("\"formula\":[");
    for (i, &a) in p.problem.assertions.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        tree(&comb, &p.prep, a, &mut s);
    }
    s.push_str("],");
    s
}

/// Lemmas the playground keeps across replays (only over variables that
/// exist before search starts, so they mean the same thing every time).
fn add_lemmas(cnf: &mut crate::Cnf, origin: Option<&mut Vec<String>>, lemmas: &[Vec<i64>]) {
    let n = cnf.num_vars;
    let mut origin = origin;
    for c in lemmas {
        if c.is_empty() || c.iter().any(|&l| l == 0 || l.unsigned_abs() as usize > n) {
            continue;
        }
        cnf.clauses
            .push(c.iter().map(|&l| Lit::from_dimacs(l)).collect());
        if let Some(o) = origin.as_deref_mut() {
            o.push("clause learned earlier in the playground".into());
        }
    }
}

/// Is every unsatisfied problem clause open only in atoms a theory created
/// for itself (bound atoms defining an equality, branch atoms, testers)?
fn only_helpers_open(solver: &Solver, comb: &Combination) -> bool {
    let mut any = false;
    for c in solver.clauses() {
        if c.learnt || c.deleted || c.lits.iter().any(|&l| solver.value(l) == Some(true)) {
            continue;
        }
        for &l in &c.lits {
            if solver.value(l).is_none() {
                any = true;
                if comb.vars.get(l.var()).is_none_or(|v| v.kind != combine::VarKind::TheoryAtom) {
                    return false;
                }
            }
        }
    }
    any
}

/// The variables still to decide: unassigned literals of the problem clauses
/// (input clauses and theory axioms) that are not satisfied yet.
fn open_vars(solver: &Solver) -> Vec<usize> {
    let mut out = Vec::new();
    for c in solver.clauses() {
        if c.learnt || c.deleted || c.lits.iter().any(|&l| solver.value(l) == Some(true)) {
            continue;
        }
        for &l in &c.lits {
            if solver.value(l).is_none() && !out.contains(&l.var()) {
                out.push(l.var());
            }
        }
    }
    out
}

/// "Let the solver finish": continue with ordinary CDCL(T) search from the
/// user's decisions (it may backjump over them) until SAT or UNSAT.
fn finish_search(solver: &mut Solver, replay: &mut Replay) {
    if !matches!(replay.outcome, "open" | "split" | "units") {
        return;
    }
    solver.flush_pending_units();
    replay.split = None;
    replay.units.clear();
    replay.finish_from = Some(solver.tracer.events.len());
    replay.outcome = match solver.solve() {
        Status::Sat => "sat",
        Status::Unsat => "unsat",
        Status::Unknown => "unknown",
    };
}

pub fn playground_json(
    text: &str,
    decisions: &[i64],
    lemmas: &[Vec<i64>],
    theory_propagation: bool,
    finish: bool,
) -> Result<String, String> {
    let actions: Vec<(bool, i64)> = decisions.iter().map(|&d| (false, d)).collect();
    playground_actions_json(text, &actions, lemmas, theory_propagation, finish)
}

/// Like `playground_json`, but `actions` also holds picks `(true, lit)`: which
/// unit clause to propagate when several are unit at once.
pub fn playground_actions_json(
    text: &str,
    actions: &[(bool, i64)],
    lemmas: &[Vec<i64>],
    theory_propagation: bool,
    finish: bool,
) -> Result<String, String> {
    let to_actions = |n: usize| -> Vec<Action> {
        actions
            .iter()
            .filter(|&&(_, d)| d != 0 && (d.unsigned_abs() as usize) <= n)
            .map(|&(pick, d)| {
                let l = Lit::from_dimacs(d);
                if pick {
                    Action::Pick(l)
                } else {
                    Action::Decide(l)
                }
            })
            .collect()
    };
    let timing = Timing::default();
    if looks_like_smtlib(text) {
        let mut prepared = prepare(text).map_err(|e| e.to_string())?;
        let Prep {
            cnf, clause_origin, ..
        } = &mut prepared.prep;
        add_lemmas(cnf, Some(clause_origin), lemmas);
        let mut solver = Solver::with_tracer(
            &prepared.prep.cnf,
            Tracer::with_limit(crate::DEFAULT_TRACE_LIMIT),
        );
        prepared.comb.borrow_mut().theory_propagation = theory_propagation;
        solver.hook = Some(Box::new(HookAdapter(prepared.comb.clone())));
        // Decisions may name variables created during earlier replays (e.g.
        // split atoms); those are only valid once they exist again.
        let acts = to_actions(usize::MAX);
        // Unit clauses over atoms the user sees are chosen by the user;
        // those over helper atoms are propagated automatically.
        let comb = prepared.comb.clone();
        let choosable = move |l: Lit| {
            comb.borrow()
                .vars
                .get(l.var())
                .is_some_and(|v| matches!(v.kind, combine::VarKind::Atom | combine::VarKind::Bool))
        };
        let mut replay = solver.replay_actions(&acts, !finish, &choosable);
        // When the only open choices are the theories' own helper atoms
        // (e.g. which side of x ≠ y), nothing instructive is left to decide
        // by hand: let the solver complete them. The page shows such an
        // equality split into its two halves.
        let auto = !finish && replay.outcome == "open" && only_helpers_open(&solver, &prepared.comb.borrow());
        if auto {
            replay.note = Some("only the theories' helper atoms were left (an equality is decided through ≤ and ≥), so the solver decided them".into());
        }
        if finish || auto {
            // The solver's own run uses theory propagation: much shorter.
            prepared.comb.borrow_mut().theory_propagation = true;
            finish_search(&mut solver, &mut replay);
        }
        let theories = prepared.comb.borrow().snapshot_all();
        let (model, verified) = if replay.outcome == "sat" {
            extract_model(&prepared, &solver)
        } else {
            (Vec::new(), None)
        };
        let mut extra = smt_section(&prepared, &solver, &model, verified, true);
        extra.push_str(&formula_json(&prepared));
        extra.push_str(&replay_section(&solver, &replay, Some(theories)));
        Ok(run_json_ext(
            &prepared.prep.cnf,
            &solver,
            Status::Unknown,
            &timing,
            &extra,
        ))
    } else {
        let mut cnf = crate::parse(text).map_err(|e| e.to_string())?;
        add_lemmas(&mut cnf, None, lemmas);
        let mut solver = Solver::with_tracer(&cnf, Tracer::with_limit(crate::DEFAULT_TRACE_LIMIT));
        let acts = to_actions(cnf.num_vars);
        let mut replay = solver.replay_actions(&acts, !finish, &|_| true);
        if finish {
            finish_search(&mut solver, &mut replay);
        }
        let extra = replay_section(&solver, &replay, None);
        Ok(run_json_ext(
            &cnf,
            &solver,
            Status::Unknown,
            &timing,
            &extra,
        ))
    }
}

/// SMT-LIB style model: `(define-fun x () Int 3)` lines.
pub fn model_smtlib(model: &[ModelEntry]) -> String {
    let mut s = String::from("(\n");
    for m in model {
        let _ = writeln!(s, "  (define-fun {} () {} {})", m.name, m.sort, m.value);
    }
    s.push(')');
    s
}
