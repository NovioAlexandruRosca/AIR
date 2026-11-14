//! End-to-end checks: random 3-SAT against brute force, pigeonhole UNSAT,
//! and trace consistency (every recorded step is legal when replayed, which
//! is what the playground relies on).

mod common;

use cdcl::solver::{verify_model, Solver, Status};
use cdcl::trace::{Event, Tracer};
use cdcl::{Cnf, Lit};
use common::check_trace;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_3sat(rng: &mut Rng, vars: usize, clauses: usize) -> Cnf {
    let mut cs = Vec::new();
    for _ in 0..clauses {
        let mut c = Vec::new();
        while c.len() < 3 {
            let v = rng.below(vars as u64) as usize;
            if c.iter().any(|l: &Lit| l.var() == v) {
                continue;
            }
            c.push(Lit::new(v, rng.below(2) == 0));
        }
        cs.push(c);
    }
    Cnf {
        num_vars: vars,
        clauses: cs,
        warnings: vec![],
    }
}

fn brute_force_sat(cnf: &Cnf) -> bool {
    let n = cnf.num_vars;
    (0u64..1 << n).any(|mask| {
        let model: Vec<bool> = (0..n).map(|v| mask >> v & 1 == 1).collect();
        verify_model(cnf, &model)
    })
}

/// PHP(n+1, n): n+1 pigeons into n holes, always UNSAT.
fn pigeonhole(holes: usize) -> Cnf {
    let pigeons = holes + 1;
    let var = |p: usize, h: usize| p * holes + h;
    let mut cs = Vec::new();
    for p in 0..pigeons {
        cs.push((0..holes).map(|h| Lit::new(var(p, h), true)).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                cs.push(vec![Lit::new(var(p, h), false), Lit::new(var(q, h), false)]);
            }
        }
    }
    Cnf {
        num_vars: pigeons * holes,
        clauses: cs,
        warnings: vec![],
    }
}

fn solve_traced(cnf: &Cnf) -> (Status, Solver) {
    let mut s = Solver::with_tracer(cnf, Tracer::with_limit(1_000_000));
    let st = s.solve();
    (st, s)
}

#[test]
fn random_3sat_matches_brute_force() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let (mut sat, mut unsat) = (0, 0);
    for round in 0..600 {
        let vars = 3 + round % 10;
        let clauses = (vars as f64 * (3.0 + rng.below(30) as f64 / 10.0)) as usize;
        let cnf = random_3sat(&mut rng, vars, clauses);
        let (status, solver) = solve_traced(&cnf);
        let expected = brute_force_sat(&cnf);
        assert_eq!(status == Status::Sat, expected, "round {round}");
        if expected {
            sat += 1;
            assert!(verify_model(&cnf, solver.model()));
        } else {
            unsat += 1;
        }
        check_trace(&cnf, &solver.tracer.events, status);
    }
    assert!(
        sat > 50 && unsat > 50,
        "test mix too lopsided: {sat} SAT / {unsat} UNSAT"
    );
}

#[test]
fn pigeonhole_is_unsat() {
    for holes in 1..=6 {
        let cnf = pigeonhole(holes);
        let (status, solver) = solve_traced(&cnf);
        assert_eq!(status, Status::Unsat, "PHP({}, {holes})", holes + 1);
        check_trace(&cnf, &solver.tracer.events, status);
    }
}

#[test]
fn larger_random_instances_without_trace() {
    let mut rng = Rng(42);
    for _ in 0..20 {
        let cnf = random_3sat(&mut rng, 75, 320);
        let mut s = Solver::new(&cnf);
        match s.solve() {
            Status::Sat => assert!(verify_model(&cnf, s.model())),
            Status::Unsat => {}
            Status::Unknown => unreachable!(),
        }
    }
}

#[test]
fn clause_deletion_keeps_answers_correct() {
    // Reduce after only a handful of learned clauses to exercise deletion hard.
    let mut rng = Rng(0xC0FFEE);
    let mut deleted = 0;
    for round in 0..400 {
        let vars = 6 + round % 7;
        let cnf = random_3sat(&mut rng, vars, vars * 4 + (round % 5));
        let mut s = Solver::new(&cnf);
        s.max_learnts = 4;
        let status = s.solve();
        assert_eq!(
            status == Status::Sat,
            brute_force_sat(&cnf),
            "round {round}"
        );
        if status == Status::Sat {
            assert!(verify_model(&cnf, s.model()));
        }
        deleted += s.stats.deleted;
    }
    for holes in 2..=7 {
        let mut s = Solver::new(&pigeonhole(holes));
        s.max_learnts = 20;
        assert_eq!(s.solve(), Status::Unsat);
        deleted += s.stats.deleted;
    }
    assert!(deleted > 0, "test never triggered a reduction");
}

#[test]
fn traces_never_contain_deletions() {
    // Even when asked to reduce early, a traced run defers deletion until
    // after the trace limit could have been reached.
    let cnf = pigeonhole(7);
    let mut s = Solver::with_tracer(&cnf, Tracer::with_limit(30_000));
    s.max_learnts = 4;
    let status = s.solve();
    assert_eq!(status, Status::Unsat);
    assert!(s.stats.deleted == 0 || s.tracer.truncated);
    if !s.tracer.truncated {
        check_trace(&cnf, &s.tracer.events, status);
    }
}

#[test]
fn limits_stop_the_solver() {
    use cdcl::solver::StopReason;
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::time::Instant;

    let cnf = pigeonhole(9); // far too hard to finish within these limits

    let mut s = Solver::new(&cnf);
    s.deadline = Some(Instant::now());
    assert_eq!(s.solve(), Status::Unknown);
    assert_eq!(s.stop_reason, Some(StopReason::TimeLimit));

    let mut s = Solver::new(&cnf);
    s.cancel = Some(Arc::new(AtomicBool::new(true)));
    assert_eq!(s.solve(), Status::Unknown);
    assert_eq!(s.stop_reason, Some(StopReason::Cancelled));

    let mut s = Solver::new(&cnf);
    s.max_conflicts = Some(10);
    assert_eq!(s.solve(), Status::Unknown);
    assert_eq!(s.stop_reason, Some(StopReason::ConflictLimit));
    assert_eq!(s.stats.conflicts, 11);
}

#[test]
fn truncated_trace_still_records_result() {
    let cnf = pigeonhole(5);
    let mut s = Solver::with_tracer(&cnf, Tracer::with_limit(50));
    assert_eq!(s.solve(), Status::Unsat);
    assert!(s.tracer.truncated);
    assert_eq!(s.tracer.events.len(), 51);
    assert!(matches!(s.tracer.events.last(), Some(Event::Result { .. })));
}
