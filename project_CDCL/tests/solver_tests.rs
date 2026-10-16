//! End-to-end checks: random 3-SAT against brute force, pigeonhole UNSAT,
//! the example files, and trace consistency (every recorded step is legal
//! when replayed, which is what the visualizer relies on).

use cdcl::solver::{verify_model, Solver, Status};
use cdcl::trace::{Event, Tracer};
use cdcl::{parse, Cnf, Lit};

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

/// Replay a trace and check every step against the clause database.
fn check_trace(cnf: &Cnf, events: &[Event], status: Status) {
    let mut clauses: Vec<Vec<i64>> = cnf
        .clauses
        .iter()
        .map(|c| c.iter().map(|l| l.to_dimacs()).collect())
        .collect();
    let mut value: Vec<Option<bool>> = vec![None; cnf.num_vars + 1];
    let mut level_of: Vec<usize> = vec![0; cnf.num_vars + 1];
    let mut trail: Vec<i64> = Vec::new();
    let mut level = 0;
    let val = |value: &Vec<Option<bool>>, l: i64| value[l.unsigned_abs() as usize].map(|b| b == (l > 0));

    for e in events {
        match e {
            Event::Decide { lit, level: lv, .. } => {
                assert_eq!(val(&value, *lit), None, "decision on assigned var");
                level += 1;
                assert_eq!(*lv, level);
                value[lit.unsigned_abs() as usize] = Some(*lit > 0);
                level_of[lit.unsigned_abs() as usize] = level;
                trail.push(*lit);
            }
            Event::Propagate { lit, reason, level: lv } => {
                assert_eq!(*lv, level);
                let c = &clauses[*reason];
                assert!(c.contains(lit), "reason clause lacks the literal");
                for &o in c.iter().filter(|&&o| o != *lit) {
                    assert_eq!(val(&value, o), Some(false), "reason clause not unit");
                }
                assert_eq!(val(&value, *lit), None);
                value[lit.unsigned_abs() as usize] = Some(*lit > 0);
                level_of[lit.unsigned_abs() as usize] = level;
                trail.push(*lit);
            }
            Event::Conflict { clause, level: lv } => {
                assert_eq!(*lv, level);
                for &o in &clauses[*clause] {
                    assert_eq!(val(&value, o), Some(false), "conflict clause not falsified");
                }
            }
            Event::Resolve { pivot, resolvent, .. } => {
                assert!(!resolvent.iter().any(|l| l.unsigned_abs() as usize == *pivot));
            }
            Event::Learn {
                clause,
                lits,
                uip,
                backjump_level,
                ..
            } => {
                assert_eq!(*clause, clauses.len());
                assert!(lits.contains(&-uip));
                // Exactly one literal at the conflict level: the negated UIP.
                let at_cur: Vec<_> = lits
                    .iter()
                    .filter(|l| level_of[l.unsigned_abs() as usize] == level)
                    .collect();
                assert_eq!(at_cur, vec![&-uip]);
                for &l in lits {
                    assert_eq!(val(&value, l), Some(false));
                }
                let bt = lits
                    .iter()
                    .filter(|&&l| l != -uip)
                    .map(|l| level_of[l.unsigned_abs() as usize])
                    .max()
                    .unwrap_or(0);
                assert_eq!(*backjump_level, bt);
                clauses.push(lits.clone());
            }
            Event::Backjump { from, to, unassigned } => {
                assert_eq!(*from, level);
                assert!(to < from);
                let keep = trail.len() - unassigned.len();
                assert_eq!(&trail[keep..], &unassigned[..]);
                for l in unassigned {
                    assert!(level_of[l.unsigned_abs() as usize] > *to);
                    value[l.unsigned_abs() as usize] = None;
                }
                trail.truncate(keep);
                level = *to;
            }
            Event::Result { status: s, model } => {
                assert_eq!(*s, status.as_str());
                if status == Status::Sat {
                    for c in &clauses[..cnf.clauses.len()] {
                        assert!(c.iter().any(|l| model.contains(l)));
                    }
                }
            }
        }
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
    assert!(sat > 50 && unsat > 50, "test mix too lopsided: {sat} SAT / {unsat} UNSAT");
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
fn example_files() {
    let cases = [
        ("examples/spec_example.cnf", Status::Sat),
        ("examples/uip.cnf", Status::Sat),
        ("examples/uip_moms.cnf", Status::Sat),
        ("examples/backjump.cnf", Status::Sat),
        ("examples/php_3_2.cnf", Status::Unsat),
        ("examples/unsat_small.cnf", Status::Unsat),
    ];
    for (path, expected) in cases {
        let text = std::fs::read_to_string(path).unwrap();
        let cnf = parse(&text).unwrap();
        let (status, solver) = solve_traced(&cnf);
        assert_eq!(status, expected, "{path}");
        check_trace(&cnf, &solver.tracer.events, status);
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
        assert_eq!(status == Status::Sat, brute_force_sat(&cnf), "round {round}");
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
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::time::Instant;
    use cdcl::solver::StopReason;

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
fn ui_examples_match_example_files() {
    let html = std::fs::read_to_string("ui/index.html").unwrap().replace("\r\n", "\n");
    for (id, path) in [
        ("spec", "examples/spec_example.cnf"),
        ("uip", "examples/uip_moms.cnf"),
        ("backjump", "examples/backjump.cnf"),
        ("php", "examples/php_3_2.cnf"),
        ("unsat", "examples/unsat_small.cnf"),
    ] {
        let file = std::fs::read_to_string(path).unwrap().replace("\r\n", "\n");
        let block = format!("<script type=\"text/plain\" id=\"ex-{id}\">{file}</script>");
        assert!(html.contains(&block), "ui example '{id}' differs from {path}");
    }
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
