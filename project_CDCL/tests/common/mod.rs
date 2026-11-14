//! Shared test helper: replay a solver trace and check that every recorded
//! step is legal. This is exactly what the visualizer relies on.

#![allow(dead_code)]

use cdcl::solver::Status;
use cdcl::trace::Event;
use cdcl::Cnf;

/// Replay a trace of a DIMACS run and check it against the clause database.
pub fn check_trace(cnf: &Cnf, events: &[Event], status: Status) {
    let clauses: Vec<Vec<i64>> = cnf
        .clauses
        .iter()
        .map(|c| c.iter().map(|l| l.to_dimacs()).collect())
        .collect();
    check_trace_raw(cnf.num_vars, clauses, events, status.as_str());
}

/// Replay any trace (SAT or SMT): `clauses` are the original clauses,
/// learned and theory clauses are taken from the events.
pub fn check_trace_raw(
    num_vars: usize,
    mut clauses: Vec<Vec<i64>>,
    events: &[Event],
    status: &str,
) {
    let num_original = clauses.len();
    let mut value: Vec<Option<bool>> = vec![None; num_vars + 1];
    let mut level_of: Vec<usize> = vec![0; num_vars + 1];
    let mut trail: Vec<i64> = Vec::new();
    let mut level = 0;
    let val =
        |value: &Vec<Option<bool>>, l: i64| value[l.unsigned_abs() as usize].map(|b| b == (l > 0));

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
            Event::Propagate {
                lit,
                reason,
                level: lv,
            } => {
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
            Event::Resolve {
                pivot, resolvent, ..
            } => {
                assert!(!resolvent
                    .iter()
                    .any(|l| l.unsigned_abs() as usize == *pivot));
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
            Event::Backjump {
                from,
                to,
                unassigned,
            } => {
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
            Event::TheoryClause { clause, lits, .. } => {
                assert_eq!(*clause, clauses.len(), "theory clause ids are sequential");
                clauses.push(lits.clone());
            }
            Event::NewVar { var, .. } => {
                assert_eq!(
                    *var,
                    value.len(),
                    "new variables are numbered consecutively"
                );
                value.push(None);
                level_of.push(0);
            }
            Event::Theory { .. } => {}
            Event::Result { status: s, model } => {
                assert_eq!(*s, status);
                if status == "SAT" {
                    for c in &clauses[..num_original] {
                        assert!(
                            c.iter().any(|l| model.contains(l)),
                            "model violates an original clause"
                        );
                    }
                }
            }
        }
    }
}
