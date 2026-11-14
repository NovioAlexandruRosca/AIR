//! CDCL(T) end-to-end tests: LIA, DT, their Nelson–Oppen combination,
//! purification, and random LIA problems against brute force. Every SAT
//! answer must come with a model that satisfies every assertion, and every
//! trace must replay consistently.

mod common;

use cdcl::smt::combine::VarKind;
use cdcl::smt::{self, SmtResult};
use cdcl::solver::Status;
use cdcl::trace::Event;
use cdcl::Limits;
use common::check_trace_raw;

fn run(text: &str) -> SmtResult {
    let r = smt::solve(text, Some(1_000_000), &Limits::default())
        .unwrap_or_else(|e| panic!("{e}\n{text}"));
    let clauses: Vec<Vec<i64>> = r
        .prepared
        .prep
        .cnf
        .clauses
        .iter()
        .map(|c| {
            cdcl::solver::dedup_clause(c)
                .iter()
                .map(|l| l.to_dimacs())
                .collect()
        })
        .collect();
    check_trace_raw(
        r.prepared.prep.cnf.num_vars,
        clauses,
        &r.solver.tracer.events,
        r.status.as_str(),
    );
    if r.status == Status::Sat {
        assert_eq!(
            r.verified,
            Some(true),
            "model does not satisfy the assertions:\n{text}\n{:?}",
            r.model
        );
    }
    r
}

fn expect(text: &str, status: Status) -> SmtResult {
    let r = run(text);
    assert_eq!(
        r.status, status,
        "{text}\nmodel: {:?}\nincomplete: {:?}",
        r.model, r.solver.incomplete_reason
    );
    r
}

fn value(r: &SmtResult, name: &str) -> String {
    r.model
        .iter()
        .find(|m| m.name == name)
        .map(|m| m.value.clone())
        .unwrap_or_default()
}

const LIST: &str = "(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))\n";

// ------------------------------------------------------------------ LIA

#[test]
fn lia_simplex_conflict() {
    let r = expect(
        "(declare-const x Int) (declare-const y Int)
         (assert (>= (+ x y) 10)) (assert (<= x 3)) (assert (<= y 6))",
        Status::Unsat,
    );
    let conflict = r.solver.tracer.events.iter().any(|e| matches!(e, Event::Theory { theory, kind: "conflict", message, .. } if theory == "LIA" && message.contains("Simplex row")));
    assert!(
        conflict,
        "the conflict should be explained by a Simplex row"
    );
}

#[test]
fn lia_sat_with_model() {
    let r = expect(
        "(declare-const x Int) (declare-const y Int)
         (assert (= (+ x (* 2 y)) 7)) (assert (>= x 0)) (assert (>= y 0)) (assert (> x y))",
        Status::Sat,
    );
    let x: i64 = value(&r, "x").parse().unwrap();
    let y: i64 = value(&r, "y").parse().unwrap();
    assert_eq!(x + 2 * y, 7);
    assert!(x > y && y >= 0);
}

#[test]
fn lia_gcd_test() {
    // 2x - 2y = 1 has rational but no integer solutions.
    expect(
        "(declare-const x Int) (declare-const y Int) (assert (= (- (* 2 x) (* 2 y)) 1))",
        Status::Unsat,
    );
}

#[test]
fn lia_branch_and_bound() {
    // 2x + 3y = 1 inside the box [0,3]² has no integer solution, and the
    // gcd of the coefficients is 1: only branching finds that out.
    let r = expect(
        "(declare-const x Int) (declare-const y Int)
         (assert (= (+ (* 2 x) (* 3 y)) 1))
         (assert (and (>= x 0) (<= x 3) (>= y 0) (<= y 3)))",
        Status::Unsat,
    );
    assert!(
        r.solver.stats.theory_splits > 0,
        "expected branch-and-bound splits"
    );
    // and a satisfiable variant that needs integral values
    let r = expect(
        "(declare-const x Int) (declare-const y Int)
         (assert (= (+ (* 2 x) (* 3 y)) 7)) (assert (>= x 0)) (assert (>= y 0)) (assert (<= y 1))",
        Status::Sat,
    );
    assert_eq!(value(&r, "x"), "2");
    assert_eq!(value(&r, "y"), "1");
}

#[test]
fn lia_boolean_structure_and_negative_numbers() {
    expect(
        "(declare-const x Int)
         (assert (or (< x 0) (> x 10))) (assert (>= x 5)) (assert (<= x 7))",
        Status::Unsat,
    );
    let r = expect(
        "(declare-const x Int) (declare-const b Bool)
         (assert (=> b (< x (- 3)))) (assert b) (assert (> x (- 6)))",
        Status::Sat,
    );
    let x: i64 = value(&r, "x")
        .trim_matches(|c| c == '(' || c == ')')
        .replace("- ", "-")
        .parse()
        .unwrap();
    assert!(x < -3 && x > -6);
}

#[test]
fn lia_disequality_is_non_convex() {
    // x ≠ y with 0 ≤ x,y ≤ 1 and x + y = 1 is fine; with x = y forced it is not.
    expect(
        "(declare-const x Int) (declare-const y Int)
         (assert (distinct x y)) (assert (and (>= x 0) (<= x 1) (>= y 0) (<= y 1)))",
        Status::Sat,
    );
    expect(
        "(declare-const x Int) (declare-const y Int) (declare-const z Int)
         (assert (distinct x y z)) (assert (and (>= x 0) (<= x 1) (>= y 0) (<= y 1) (>= z 0) (<= z 1)))",
        Status::Unsat,
    );
}

// ------------------------------------------------------------------ DT

#[test]
fn dt_tester_clash() {
    expect(
        &format!("{LIST}(declare-const l List) (declare-const x Int) (assert (= l (cons x nil))) (assert ((_ is nil) l))"),
        Status::Unsat,
    );
}

#[test]
fn dt_acyclicity() {
    let r = expect(
        &format!("{LIST}(declare-const l List) (assert (= l (cons 1 l)))"),
        Status::Unsat,
    );
    // 1 inside a list is an LIA term in a DT context: purified.
    assert_eq!(r.prepared.prep.fresh.len(), 1);
    let cyc = r.solver.tracer.events.iter().any(|e| matches!(e, Event::Theory { kind: "conflict", message, .. } if message.contains("acyclicity")));
    assert!(cyc);
}

#[test]
fn dt_constructor_exclusion() {
    expect(
        &format!("{LIST}(declare-const l List) (assert (not ((_ is nil) l))) (assert (not ((_ is cons) l)))"),
        Status::Unsat,
    );
    let r = expect(
        &format!("{LIST}(declare-const l List) (declare-const m List) (assert (not ((_ is cons) l))) (assert (not (= l m)))"),
        Status::Sat,
    );
    assert_eq!(value(&r, "l"), "nil");
    assert_ne!(value(&r, "m"), "nil");
}

#[test]
fn dt_finite_sort_pigeonhole() {
    let color = "(declare-datatypes ((Color 0)) (((red) (green) (blue))))";
    expect(
        &format!("{color} (declare-const a Color) (declare-const b Color) (declare-const c Color) (declare-const d Color) (assert (distinct a b c d))"),
        Status::Unsat,
    );
    expect(
        &format!("{color} (declare-const a Color) (declare-const b Color) (declare-const c Color) (assert (distinct a b c))"),
        Status::Sat,
    );
}

#[test]
fn dt_selectors_and_model() {
    let r = expect(
        &format!(
            "{LIST}(declare-const l List) (declare-const x Int) (declare-const y Int)
             (assert (= l (cons x (cons y nil)))) (assert (= (head (tail l)) 5)) (assert (= (+ x y) 8))"
        ),
        Status::Sat,
    );
    assert_eq!(value(&r, "x"), "3");
    assert_eq!(value(&r, "l"), "(cons 3 (cons 5 nil))");
}

// ------------------------------------------------------------------ combination

#[test]
fn purification_and_nelson_oppen_equality_exchange() {
    // DT: cons(x, nil) = cons(y, nil) ⇒ x = y (injectivity), which LIA needs.
    let r = expect(
        &format!("{LIST}(declare-const x Int) (declare-const y Int) (assert (= (cons x nil) (cons y nil))) (assert (< x y))"),
        Status::Unsat,
    );
    let no = r.solver.tracer.events.iter().any(|e| {
        matches!(
            e,
            Event::Theory {
                kind: "nelson-oppen",
                ..
            }
        )
    });
    assert!(no, "expected a Nelson–Oppen equality exchange event");
}

#[test]
fn purification_of_selector_inside_arithmetic() {
    // head(l) = x + 1 mixes DT and LIA: k = head(l) is introduced.
    let r = expect(
        &format!(
            "{LIST}(declare-const l List) (declare-const x Int) (declare-const y Int)
                  (assert (= (head l) (+ x 1))) (assert (= l (cons y nil))) (assert (> x y))"
        ),
        Status::Unsat,
    );
    assert!(!r.prepared.prep.definitions.is_empty());
}

#[test]
fn non_convex_combination_needs_arrangement_splits() {
    // Three different singleton lists over values in {1,2}: DT needs the
    // heads pairwise different, LIA has only two values. Neither theory alone
    // derives an equality; the arrangement must be guessed.
    let base = |hi: i32| {
        format!(
            "{LIST}(declare-const x Int) (declare-const y Int) (declare-const z Int)
             (assert (and (>= x 1) (<= x {hi}) (>= y 1) (<= y {hi}) (>= z 1) (<= z {hi})))
             (assert (distinct (cons x nil) (cons y nil) (cons z nil)))"
        )
    };
    let r = expect(&base(2), Status::Unsat);
    // The arrangement is guessed: either by MOMS (interface equalities occur
    // in LIA's definition clauses: delayed theory combination) or by a
    // Nelson–Oppen split on the final check.
    let comb = r.prepared.comb.borrow();
    let guessed = r.solver.tracer.events.iter().any(|e| match e {
        Event::Decide { lit, .. } => {
            comb.vars[(lit.unsigned_abs() - 1) as usize].kind == VarKind::Interface
        }
        _ => false,
    });
    assert!(guessed, "expected decisions on interface equalities");
    assert!(r
        .solver
        .tracer
        .events
        .iter()
        .any(|e| matches!(e, Event::Theory { theory, kind: "conflict", .. } if theory == "DT")));
    drop(comb);
    let r = expect(&base(3), Status::Sat);
    let vals: Vec<String> = ["x", "y", "z"].iter().map(|n| value(&r, n)).collect();
    assert!(vals[0] != vals[1] && vals[0] != vals[2] && vals[1] != vals[2]);
}

#[test]
fn shared_variable_through_datatype_equality() {
    let r = expect(
        &format!("{LIST}(declare-const l List) (declare-const x Int)
                  (assert ((_ is cons) l)) (assert (= (head l) x)) (assert (> x 41)) (assert (< x 43))"),
        Status::Sat,
    );
    assert_eq!(value(&r, "x"), "42");
    assert!(value(&r, "l").starts_with("(cons 42 "));
}

#[test]
fn example_files_give_expected_answers() {
    for (name, expected) in [
        ("dpllt_intro", Status::Unsat),
        ("learn_backtrack", Status::Unsat),
        ("several_decisions", Status::Sat),
        ("no_lists", Status::Sat),
        ("lia_simplex", Status::Unsat),
        ("lia_gcd", Status::Unsat),
        ("lia_branch", Status::Unsat),
        ("lia_sat", Status::Sat),
        ("dt_lists", Status::Sat),
        ("dt_cycle", Status::Unsat),
        ("dt_intro", Status::Unsat),
        ("dt_colors", Status::Unsat),
        ("combo_injectivity", Status::Unsat),
        ("combo_purify", Status::Unsat),
        ("nonconvex", Status::Unsat),
        ("combo_sat", Status::Sat),
    ] {
        let text = std::fs::read_to_string(format!("examples/smt/{name}.smt2")).unwrap();
        let r = run(&text);
        assert_eq!(r.status, expected, "{name}");
    }
}

#[test]
fn parse_errors_are_reported() {
    for (src, needle) in [
        (
            "(declare-const x Int) (assert (< x y))",
            "unknown symbol 'y'",
        ),
        ("(declare-const x Int) (assert (* x x))", "Bool formula"),
        ("(declare-const x Int) (assert (< (* x x) 3))", "non-linear"),
        ("(declare-fun f (Int) Int)", "uninterpreted functions"),
        ("(declare-const x Int) (assert (< x 1)", "unclosed"),
        ("(assert (= 1 true))", "mixes sorts"),
    ] {
        let e = smt::solve(src, None, &Limits::default())
            .err()
            .unwrap_or_else(|| panic!("{src} should fail"));
        assert!(e.message.contains(needle), "{src}: got '{}'", e.message);
    }
}

#[test]
fn playground_replays_user_decisions() {
    let src = "(declare-const x Int) (declare-const y Int) (assert (or (<= x 2) (>= y 5))) (assert (>= x 4))";
    let json = smt::playground_json(src, &[], &[], true, false).unwrap();
    assert!(json.contains("\"replay\":{\"outcome\""));
    // x ≥ 4 is a unit clause: LIA then refutes x ≤ 2 by bound propagation,
    // which makes y ≥ 5 true by BCP.
    assert!(json.contains("bound propagation"), "{json}");
}

#[test]
fn playground_textbook_mode_and_finish() {
    let src = std::fs::read_to_string("examples/smt/dpllt_intro.smt2").unwrap();
    // Without theory propagation nothing beyond BCP happens at level 0:
    // the user still has a choice to make (as in the slides).
    let json = smt::playground_json(&src, &[], &[], false, false).unwrap();
    assert!(json.contains("\"outcome\":\"open\""), "{json}");
    assert!(json.contains("\"formula\":["));
    // Letting the solver finish proves the formula unsatisfiable.
    let json = smt::playground_json(&src, &[], &[], false, true).unwrap();
    assert!(json.contains("\"outcome\":\"unsat\""), "{json}");
    // A kept lemma is used as a clause: with (¬(x+1>0) ∨ ¬(x<0)) the
    // solver propagates x<0 to false by itself.
    let r = smt::prepare(&src).unwrap();
    let comb = r.comb.borrow();
    let var = |label: &str| comb.vars.iter().position(|v| v.label == label).unwrap() as i64 + 1;
    let (a, b) = (var("x + 1 > 0"), var("x < 0"));
    drop(comb);
    let json = smt::playground_json(&src, &[], &[vec![-a, -b]], false, false).unwrap();
    assert!(
        json.contains(&format!("\"lit\":{}", -b)),
        "x < 0 should be propagated false: {json}"
    );
}

// ------------------------------------------------------------------ random LIA vs brute force

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % (hi - lo + 1) as u64) as i64
    }
}

#[derive(Clone)]
struct Atom {
    coeffs: [i64; 3],
    op: &'static str,
    k: i64,
}

impl Atom {
    fn holds(&self, v: [i64; 3]) -> bool {
        let s: i64 = (0..3).map(|i| self.coeffs[i] * v[i]).sum();
        match self.op {
            "<=" => s <= self.k,
            "<" => s < self.k,
            ">=" => s >= self.k,
            ">" => s > self.k,
            _ => s == self.k,
        }
    }
    fn smt(&self) -> String {
        let names = ["x", "y", "z"];
        let parts: Vec<String> = (0..3)
            .filter(|&i| self.coeffs[i] != 0)
            .map(|i| {
                let c = self.coeffs[i];
                if c < 0 {
                    format!("(* (- {}) {})", -c, names[i])
                } else {
                    format!("(* {c} {})", names[i])
                }
            })
            .collect();
        let lhs = match parts.len() {
            0 => "0".to_string(),
            1 => parts[0].clone(),
            _ => format!("(+ {})", parts.join(" ")),
        };
        let k = if self.k < 0 {
            format!("(- {})", -self.k)
        } else {
            self.k.to_string()
        };
        format!("({} {lhs} {k})", self.op)
    }
}

#[test]
fn random_lia_matches_brute_force() {
    let mut rng = Rng(0xDEC0DE);
    let (mut sat, mut unsat) = (0, 0);
    for round in 0..250 {
        let n_clauses = rng.range(3, 8) as usize;
        let mut clauses: Vec<Vec<(bool, Atom)>> = Vec::new();
        for _ in 0..n_clauses {
            let len = rng.range(1, 2) as usize;
            let mut c = Vec::new();
            for _ in 0..len {
                let coeffs = [rng.range(-3, 3), rng.range(-3, 3), rng.range(-3, 3)];
                let op = ["<=", "<", ">=", ">", "="][rng.range(0, 4) as usize];
                let k = rng.range(-6, 6);
                c.push((rng.range(0, 3) != 0, Atom { coeffs, op, k }));
            }
            clauses.push(c);
        }
        // bounded domain [-3, 3] for every variable
        let mut text =
            String::from("(declare-const x Int) (declare-const y Int) (declare-const z Int)\n");
        for v in ["x", "y", "z"] {
            text.push_str(&format!("(assert (and (>= {v} (- 3)) (<= {v} 3)))\n"));
        }
        for c in &clauses {
            let lits: Vec<String> = c
                .iter()
                .map(|(pos, a)| {
                    if *pos {
                        a.smt()
                    } else {
                        format!("(not {})", a.smt())
                    }
                })
                .collect();
            text.push_str(&format!("(assert (or {}))\n", lits.join(" ")));
        }
        let mut expected = false;
        'search: for x in -3..=3 {
            for y in -3..=3 {
                for z in -3..=3 {
                    if clauses
                        .iter()
                        .all(|c| c.iter().any(|(pos, a)| a.holds([x, y, z]) == *pos))
                    {
                        expected = true;
                        break 'search;
                    }
                }
            }
        }
        let r = run(&text);
        assert_eq!(r.status == Status::Sat, expected, "round {round}:\n{text}");
        if expected {
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    assert!(
        sat > 30 && unsat > 30,
        "test mix too lopsided: {sat} SAT / {unsat} UNSAT"
    );
}

#[test]
fn playground_records_theory_checks() {
    // LIA: the asserted bounds of each check (normalised over the integers)
    // and the Simplex moves; the learned-clause example needs two pivots.
    let src = std::fs::read_to_string("examples/smt/learn_backtrack.smt2").unwrap();
    let json = smt::playground_json(&src, &[], &[], false, true).unwrap();
    assert!(
        json.contains("\"check\":{\"vars\":[\"x\",\"y\",\"z\"]"),
        "{json}"
    );
    assert!(
        json.contains(
            "\"label\":\"x > z\",\"form\":[[\"x\",1],[\"z\",-1]],\"op\":\">=\",\"bound\":1"
        ),
        "{json}"
    );
    assert!(json.contains("(pivot)"), "{json}");
    // DT: every merge with the rule that made it.
    let src = std::fs::read_to_string("examples/smt/combo_injectivity.smt2").unwrap();
    let json = smt::playground_json(&src, &[], &[], false, true).unwrap();
    assert!(json.contains("\"rule\":\"asserted\""), "{json}");
    assert!(json.contains("\"rule\":\"injectivity\""), "{json}");
    assert!(json.contains("\"nodes\":[{\"term\":"), "{json}");
}
