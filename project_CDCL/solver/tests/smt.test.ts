// CDCL(T) end-to-end tests: LIA, DT, their Nelson–Oppen combination,
// purification, and random LIA problems against brute force. Every SAT
// answer must come with a model that satisfies every assertion, and every
// trace must replay consistently.
// (Port of tests/smt_tests.rs.)

import { readFileSync } from "node:fs";
import { expect, it } from "vitest";
import { Limits } from "../src/lib";
import { lit_to_dimacs } from "../src/lit";
import * as smt from "../src/smt/mod";
import { SmtResult } from "../src/smt/mod";
import { dedup_clause, Status, Status_as_str } from "../src/solver";
import { RustErr } from "../src/util";
import { check_trace_raw } from "./common";

/** `std::fs::read_to_string("examples/smt/<name>.smt2")` (relative to the repo root). */
function example(name: string): string {
  return readFileSync(new URL(`../../examples/smt/${name}.smt2`, import.meta.url), "utf8");
}

function run(text: string): SmtResult {
  let r: SmtResult;
  try {
    r = smt.solve(text, 1_000_000, Limits.default());
  } catch (e) {
    throw new Error(`${e instanceof RustErr ? e.message : String(e)}\n${text}`);
  }
  const clauses: number[][] = r.prepared.prep.cnf.clauses.map((c) => dedup_clause(c).map((l) => lit_to_dimacs(l)));
  check_trace_raw(r.prepared.prep.cnf.num_vars, clauses, r.solver.tracer.events, Status_as_str(r.status));
  if (r.status === "Sat") {
    expect(r.verified, `model does not satisfy the assertions:\n${text}\n${JSON.stringify(r.model)}`).toBe(true);
  }
  return r;
}

function expectStatus(text: string, status: Status): SmtResult {
  const r = run(text);
  expect(r.status, `${text}\nmodel: ${JSON.stringify(r.model)}\nincomplete: ${r.solver.incomplete_reason}`).toBe(status);
  return r;
}

function value(r: SmtResult, name: string): string {
  return r.model.find((m) => m.name === name)?.value ?? "";
}

const LIST = "(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))\n";

// ------------------------------------------------------------------ LIA

it("lia_simplex_conflict", () => {
  const r = expectStatus(
    `(declare-const x Int) (declare-const y Int)
         (assert (>= (+ x y) 10)) (assert (<= x 3)) (assert (<= y 6))`,
    "Unsat",
  );
  const conflict = r.solver.tracer.events.some(
    (e) => e.kind === "Theory" && e.theory === "LIA" && e.kind_ === "conflict" && e.message.includes("Simplex row"),
  );
  expect(conflict, "the conflict should be explained by a Simplex row").toBe(true);
});

it("lia_sat_with_model", () => {
  const r = expectStatus(
    `(declare-const x Int) (declare-const y Int)
         (assert (= (+ x (* 2 y)) 7)) (assert (>= x 0)) (assert (>= y 0)) (assert (> x y))`,
    "Sat",
  );
  const x = parse_i64(value(r, "x"));
  const y = parse_i64(value(r, "y"));
  expect(x + 2 * y).toBe(7);
  expect(x > y && y >= 0).toBe(true);
});

/** `s.parse::<i64>().unwrap()` */
function parse_i64(s: string): number {
  if (!/^[+-]?\d+$/.test(s)) throw new Error(`cannot parse '${s}' as i64`);
  return Number(s);
}

it("lia_gcd_test", () => {
  // 2x - 2y = 1 has rational but no integer solutions.
  expectStatus("(declare-const x Int) (declare-const y Int) (assert (= (- (* 2 x) (* 2 y)) 1))", "Unsat");
});

it("lia_branch_and_bound", () => {
  // 2x + 3y = 1 inside the box [0,3]² has no integer solution, and the
  // gcd of the coefficients is 1: only branching finds that out.
  let r = expectStatus(
    `(declare-const x Int) (declare-const y Int)
         (assert (= (+ (* 2 x) (* 3 y)) 1))
         (assert (and (>= x 0) (<= x 3) (>= y 0) (<= y 3)))`,
    "Unsat",
  );
  expect(r.solver.stats.theory_splits > 0, "expected branch-and-bound splits").toBe(true);
  // and a satisfiable variant that needs integral values
  r = expectStatus(
    `(declare-const x Int) (declare-const y Int)
         (assert (= (+ (* 2 x) (* 3 y)) 7)) (assert (>= x 0)) (assert (>= y 0)) (assert (<= y 1))`,
    "Sat",
  );
  expect(value(r, "x")).toBe("2");
  expect(value(r, "y")).toBe("1");
});

it("lia_boolean_structure_and_negative_numbers", () => {
  expectStatus(
    `(declare-const x Int)
         (assert (or (< x 0) (> x 10))) (assert (>= x 5)) (assert (<= x 7))`,
    "Unsat",
  );
  const r = expectStatus(
    `(declare-const x Int) (declare-const b Bool)
         (assert (=> b (< x (- 3)))) (assert b) (assert (> x (- 6)))`,
    "Sat",
  );
  const x = parse_i64(value(r, "x").replace(/^[()]+|[()]+$/g, "").split("- ").join("-"));
  expect(x < -3 && x > -6).toBe(true);
});

it("lia_disequality_is_non_convex", () => {
  // x ≠ y with 0 ≤ x,y ≤ 1 and x + y = 1 is fine; with x = y forced it is not.
  expectStatus(
    `(declare-const x Int) (declare-const y Int)
         (assert (distinct x y)) (assert (and (>= x 0) (<= x 1) (>= y 0) (<= y 1)))`,
    "Sat",
  );
  expectStatus(
    `(declare-const x Int) (declare-const y Int) (declare-const z Int)
         (assert (distinct x y z)) (assert (and (>= x 0) (<= x 1) (>= y 0) (<= y 1) (>= z 0) (<= z 1)))`,
    "Unsat",
  );
});

// ------------------------------------------------------------------ DT

it("dt_tester_clash", () => {
  expectStatus(
    `${LIST}(declare-const l List) (declare-const x Int) (assert (= l (cons x nil))) (assert ((_ is nil) l))`,
    "Unsat",
  );
});

it("dt_acyclicity", () => {
  const r = expectStatus(`${LIST}(declare-const l List) (assert (= l (cons 1 l)))`, "Unsat");
  // 1 inside a list is an LIA term in a DT context: purified.
  expect(r.prepared.prep.fresh.length).toBe(1);
  const cyc = r.solver.tracer.events.some((e) => e.kind === "Theory" && e.kind_ === "conflict" && e.message.includes("acyclicity"));
  expect(cyc).toBe(true);
});

it("dt_constructor_exclusion", () => {
  expectStatus(`${LIST}(declare-const l List) (assert (not ((_ is nil) l))) (assert (not ((_ is cons) l)))`, "Unsat");
  const r = expectStatus(
    `${LIST}(declare-const l List) (declare-const m List) (assert (not ((_ is cons) l))) (assert (not (= l m)))`,
    "Sat",
  );
  expect(value(r, "l")).toBe("nil");
  expect(value(r, "m")).not.toBe("nil");
});

it("dt_finite_sort_pigeonhole", () => {
  const color = "(declare-datatypes ((Color 0)) (((red) (green) (blue))))";
  expectStatus(
    `${color} (declare-const a Color) (declare-const b Color) (declare-const c Color) (declare-const d Color) (assert (distinct a b c d))`,
    "Unsat",
  );
  expectStatus(`${color} (declare-const a Color) (declare-const b Color) (declare-const c Color) (assert (distinct a b c))`, "Sat");
});

it("dt_selectors_and_model", () => {
  const r = expectStatus(
    `${LIST}(declare-const l List) (declare-const x Int) (declare-const y Int)
             (assert (= l (cons x (cons y nil)))) (assert (= (head (tail l)) 5)) (assert (= (+ x y) 8))`,
    "Sat",
  );
  expect(value(r, "x")).toBe("3");
  expect(value(r, "l")).toBe("(cons 3 (cons 5 nil))");
});

// ------------------------------------------------------------------ combination

it("purification_and_nelson_oppen_equality_exchange", () => {
  // DT: cons(x, nil) = cons(y, nil) ⇒ x = y (injectivity), which LIA needs.
  const r = expectStatus(
    `${LIST}(declare-const x Int) (declare-const y Int) (assert (= (cons x nil) (cons y nil))) (assert (< x y))`,
    "Unsat",
  );
  const no = r.solver.tracer.events.some((e) => e.kind === "Theory" && e.kind_ === "nelson-oppen");
  expect(no, "expected a Nelson–Oppen equality exchange event").toBe(true);
});

it("purification_of_selector_inside_arithmetic", () => {
  // head(l) = x + 1 mixes DT and LIA: k = head(l) is introduced.
  const r = expectStatus(
    `${LIST}(declare-const l List) (declare-const x Int) (declare-const y Int)
                  (assert (= (head l) (+ x 1))) (assert (= l (cons y nil))) (assert (> x y))`,
    "Unsat",
  );
  expect(r.prepared.prep.definitions.length > 0).toBe(true);
});

it("non_convex_combination_needs_arrangement_splits", () => {
  // Three different singleton lists over values in {1,2}: DT needs the
  // heads pairwise different, LIA has only two values. Neither theory alone
  // derives an equality; the arrangement must be guessed.
  const base = (hi: number) =>
    `${LIST}(declare-const x Int) (declare-const y Int) (declare-const z Int)
             (assert (and (>= x 1) (<= x ${hi}) (>= y 1) (<= y ${hi}) (>= z 1) (<= z ${hi})))
             (assert (distinct (cons x nil) (cons y nil) (cons z nil)))`;
  let r = expectStatus(base(2), "Unsat");
  // The arrangement is guessed: either by MOMS (interface equalities occur
  // in LIA's definition clauses: delayed theory combination) or by a
  // Nelson–Oppen split on the final check.
  const comb = r.prepared.comb;
  const guessed = r.solver.tracer.events.some((e) => e.kind === "Decide" && comb.vars[Math.abs(e.lit) - 1].kind === "Interface");
  expect(guessed, "expected decisions on interface equalities").toBe(true);
  expect(r.solver.tracer.events.some((e) => e.kind === "Theory" && e.theory === "DT" && e.kind_ === "conflict")).toBe(true);
  r = expectStatus(base(3), "Sat");
  const vals = ["x", "y", "z"].map((n) => value(r, n));
  expect(vals[0] !== vals[1] && vals[0] !== vals[2] && vals[1] !== vals[2]).toBe(true);
});

it("shared_variable_through_datatype_equality", () => {
  const r = expectStatus(
    `${LIST}(declare-const l List) (declare-const x Int)
                  (assert ((_ is cons) l)) (assert (= (head l) x)) (assert (> x 41)) (assert (< x 43))`,
    "Sat",
  );
  expect(value(r, "x")).toBe("42");
  expect(value(r, "l").startsWith("(cons 42 ")).toBe(true);
});

it("example_files_give_expected_answers", () => {
  const cases: [string, Status][] = [
    ["dpllt_intro", "Unsat"],
    ["learn_backtrack", "Unsat"],
    ["several_decisions", "Sat"],
    ["no_lists", "Sat"],
    ["lia_simplex", "Unsat"],
    ["lia_gcd", "Unsat"],
    ["lia_branch", "Unsat"],
    ["lia_sat", "Sat"],
    ["dt_lists", "Sat"],
    ["dt_cycle", "Unsat"],
    ["dt_intro", "Unsat"],
    ["dt_colors", "Unsat"],
    ["combo_injectivity", "Unsat"],
    ["combo_purify", "Unsat"],
    ["nonconvex", "Unsat"],
    ["combo_sat", "Sat"],
  ];
  for (const [name, expected] of cases) {
    const r = run(example(name));
    expect(r.status, name).toBe(expected);
  }
});

it("parse_errors_are_reported", () => {
  const cases: [string, string][] = [
    ["(declare-const x Int) (assert (< x y))", "unknown symbol 'y'"],
    ["(declare-const x Int) (assert (* x x))", "Bool formula"],
    ["(declare-const x Int) (assert (< (* x x) 3))", "non-linear"],
    ["(declare-fun f (Int) Int)", "uninterpreted functions"],
    ["(declare-const x Int) (assert (< x 1)", "unclosed"],
    ["(assert (= 1 true))", "mixes sorts"],
  ];
  for (const [src, needle] of cases) {
    let message: string | null = null;
    try {
      smt.solve(src, null, Limits.default());
    } catch (e) {
      if (!(e instanceof RustErr)) throw e;
      message = (e.value as { message: string }).message;
    }
    if (message === null) throw new Error(`${src} should fail`);
    expect(message.includes(needle), `${src}: got '${message}'`).toBe(true);
  }
});

it("playground_replays_user_decisions", () => {
  const src = "(declare-const x Int) (declare-const y Int) (assert (or (<= x 2) (>= y 5))) (assert (>= x 4))";
  const json = smt.playground_json(src, [], [], true, false);
  expect(json.includes('"replay":{"outcome"')).toBe(true);
  // x ≥ 4 is a unit clause: LIA then refutes x ≤ 2 by bound propagation,
  // which makes y ≥ 5 true by BCP.
  expect(json.includes("bound propagation"), json).toBe(true);
});

it("playground_textbook_mode_and_finish", () => {
  const src = example("dpllt_intro");
  // Without theory propagation nothing beyond BCP happens at level 0:
  // the user still has a choice to make (as in the slides).
  let json = smt.playground_json(src, [], [], false, false);
  expect(json.includes('"outcome":"open"'), json).toBe(true);
  expect(json.includes('"formula":[')).toBe(true);
  // Letting the solver finish proves the formula unsatisfiable.
  json = smt.playground_json(src, [], [], false, true);
  expect(json.includes('"outcome":"unsat"'), json).toBe(true);
  // A kept lemma is used as a clause: with (¬(x+1>0) ∨ ¬(x<0)) the
  // solver propagates x<0 to false by itself.
  const r = smt.prepare(src);
  const comb = r.comb;
  const v = (label: string) => {
    const i = comb.vars.findIndex((x) => x.label === label);
    if (i < 0) throw new Error(`no variable labelled '${label}'`);
    return i + 1;
  };
  const [a, b] = [v("x + 1 > 0"), v("x < 0")];
  json = smt.playground_json(src, [], [[-a, -b]], false, false);
  expect(json.includes(`"lit":${-b}`), `x < 0 should be propagated false: ${json}`).toBe(true);
});

// ------------------------------------------------------------------ random LIA vs brute force

const U64 = (1n << 64n) - 1n;

/** xorshift64 with u64 wrapping arithmetic (BigInt, masked to 64 bits). */
class Rng {
  constructor(public _0: bigint) {}
  next(): bigint {
    this._0 ^= (this._0 << 13n) & U64;
    this._0 ^= this._0 >> 7n;
    this._0 ^= (this._0 << 17n) & U64;
    return this._0;
  }
  range(lo: number, hi: number): number {
    return lo + Number(this.next() % BigInt(hi - lo + 1));
  }
}

class Atom {
  constructor(
    public coeffs: [number, number, number],
    public op: string,
    public k: number,
  ) {}
  holds(v: [number, number, number]): boolean {
    let s = 0;
    for (let i = 0; i < 3; i++) s += this.coeffs[i] * v[i];
    switch (this.op) {
      case "<=":
        return s <= this.k;
      case "<":
        return s < this.k;
      case ">=":
        return s >= this.k;
      case ">":
        return s > this.k;
      default:
        return s === this.k;
    }
  }
  smt(): string {
    const names = ["x", "y", "z"];
    const parts: string[] = [];
    for (let i = 0; i < 3; i++) {
      if (this.coeffs[i] === 0) continue;
      const c = this.coeffs[i];
      parts.push(c < 0 ? `(* (- ${-c}) ${names[i]})` : `(* ${c} ${names[i]})`);
    }
    const lhs = parts.length === 0 ? "0" : parts.length === 1 ? parts[0] : `(+ ${parts.join(" ")})`;
    const k = this.k < 0 ? `(- ${-this.k})` : `${this.k}`;
    return `(${this.op} ${lhs} ${k})`;
  }
}

it("random_lia_matches_brute_force", () => {
  const rng = new Rng(0xdec0den);
  let sat = 0;
  let unsat = 0;
  for (let round = 0; round < 250; round++) {
    const n_clauses = rng.range(3, 8);
    const clauses: [boolean, Atom][][] = [];
    for (let i = 0; i < n_clauses; i++) {
      const len = rng.range(1, 2);
      const c: [boolean, Atom][] = [];
      for (let j = 0; j < len; j++) {
        const c0 = rng.range(-3, 3);
        const c1 = rng.range(-3, 3);
        const c2 = rng.range(-3, 3);
        const op = ["<=", "<", ">=", ">", "="][rng.range(0, 4)];
        const k = rng.range(-6, 6);
        const pos = rng.range(0, 3) !== 0;
        c.push([pos, new Atom([c0, c1, c2], op, k)]);
      }
      clauses.push(c);
    }
    // bounded domain [-3, 3] for every variable
    let text = "(declare-const x Int) (declare-const y Int) (declare-const z Int)\n";
    for (const v of ["x", "y", "z"]) {
      text += `(assert (and (>= ${v} (- 3)) (<= ${v} 3)))\n`;
    }
    for (const c of clauses) {
      const lits = c.map(([pos, a]) => (pos ? a.smt() : `(not ${a.smt()})`));
      text += `(assert (or ${lits.join(" ")}))\n`;
    }
    let expected = false;
    search: for (let x = -3; x <= 3; x++) {
      for (let y = -3; y <= 3; y++) {
        for (let z = -3; z <= 3; z++) {
          if (clauses.every((c) => c.some(([pos, a]) => a.holds([x, y, z]) === pos))) {
            expected = true;
            break search;
          }
        }
      }
    }
    const r = run(text);
    expect(r.status === "Sat", `round ${round}:\n${text}`).toBe(expected);
    if (expected) {
      sat += 1;
    } else {
      unsat += 1;
    }
  }
  expect(sat > 30 && unsat > 30, `test mix too lopsided: ${sat} SAT / ${unsat} UNSAT`).toBe(true);
}, 120_000);

it("playground_records_theory_checks", () => {
  // LIA: the asserted bounds of each check (normalised over the integers)
  // and the Simplex moves; the learned-clause example needs two pivots.
  let src = example("learn_backtrack");
  let json = smt.playground_json(src, [], [], false, true);
  expect(json.includes('"check":{"vars":["x","y","z"]'), json).toBe(true);
  expect(json.includes('"label":"x > z","form":[["x",1],["z",-1]],"op":">=","bound":1'), json).toBe(true);
  expect(json.includes("(pivot)"), json).toBe(true);
  // DT: every merge with the rule that made it.
  src = example("combo_injectivity");
  json = smt.playground_json(src, [], [], false, true);
  expect(json.includes('"rule":"asserted"'), json).toBe(true);
  expect(json.includes('"rule":"injectivity"'), json).toBe(true);
  expect(json.includes('"nodes":[{"term":'), json).toBe(true);
});
