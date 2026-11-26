// End-to-end checks: random 3-SAT against brute force, pigeonhole UNSAT,
// and trace consistency (every recorded step is legal when replayed, which
// is what the playground relies on).
// (Port of tests/solver_tests.rs.)

import { expect, it } from "vitest";
import { Cnf } from "../src/dimacs";
import { Lit, lit_new, lit_var } from "../src/lit";
import { Solver, Status, verify_model } from "../src/solver";
import { Tracer } from "../src/trace";
import { now } from "../src/util";
import { check_trace } from "./common";

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
  below(n: number): number {
    return Number(this.next() % BigInt(n));
  }
}

function random_3sat(rng: Rng, vars: number, clauses: number): Cnf {
  const cs: Lit[][] = [];
  for (let i = 0; i < clauses; i++) {
    const c: Lit[] = [];
    while (c.length < 3) {
      const v = rng.below(vars);
      if (c.some((l) => lit_var(l) === v)) {
        continue;
      }
      c.push(lit_new(v, rng.below(2) === 0));
    }
    cs.push(c);
  }
  return new Cnf({ num_vars: vars, clauses: cs, warnings: [] });
}

function brute_force_sat(cnf: Cnf): boolean {
  const n = cnf.num_vars;
  for (let mask = 0; mask < 1 << n; mask++) {
    const model: boolean[] = [];
    for (let v = 0; v < n; v++) model.push(((mask >> v) & 1) === 1);
    if (verify_model(cnf, model)) return true;
  }
  return false;
}

/** PHP(n+1, n): n+1 pigeons into n holes, always UNSAT. */
function pigeonhole(holes: number): Cnf {
  const pigeons = holes + 1;
  const v = (p: number, h: number) => p * holes + h;
  const cs: Lit[][] = [];
  for (let p = 0; p < pigeons; p++) {
    const c: Lit[] = [];
    for (let h = 0; h < holes; h++) c.push(lit_new(v(p, h), true));
    cs.push(c);
  }
  for (let h = 0; h < holes; h++) {
    for (let p = 0; p < pigeons; p++) {
      for (let q = p + 1; q < pigeons; q++) {
        cs.push([lit_new(v(p, h), false), lit_new(v(q, h), false)]);
      }
    }
  }
  return new Cnf({ num_vars: pigeons * holes, clauses: cs, warnings: [] });
}

function solve_traced(cnf: Cnf): [Status, Solver] {
  const s = Solver.with_tracer(cnf, Tracer.with_limit(1_000_000));
  const st = s.solve();
  return [st, s];
}

it("random_3sat_matches_brute_force", () => {
  const rng = new Rng(0x9e37_79b9_7f4a_7c15n);
  let sat = 0;
  let unsat = 0;
  for (let round = 0; round < 600; round++) {
    const vars = 3 + (round % 10);
    const clauses = Math.trunc(vars * (3.0 + rng.below(30) / 10.0));
    const cnf = random_3sat(rng, vars, clauses);
    const [status, solver] = solve_traced(cnf);
    const expected = brute_force_sat(cnf);
    expect(status === "Sat", `round ${round}`).toBe(expected);
    if (expected) {
      sat += 1;
      expect(verify_model(cnf, solver.model())).toBe(true);
    } else {
      unsat += 1;
    }
    check_trace(cnf, solver.tracer.events, status);
  }
  expect(sat > 50 && unsat > 50, `test mix too lopsided: ${sat} SAT / ${unsat} UNSAT`).toBe(true);
}, 120_000);

it("pigeonhole_is_unsat", () => {
  for (let holes = 1; holes <= 6; holes++) {
    const cnf = pigeonhole(holes);
    const [status, solver] = solve_traced(cnf);
    expect(status, `PHP(${holes + 1}, ${holes})`).toBe("Unsat");
    check_trace(cnf, solver.tracer.events, status);
  }
}, 120_000);

it("larger_random_instances_without_trace", () => {
  const rng = new Rng(42n);
  for (let i = 0; i < 20; i++) {
    const cnf = random_3sat(rng, 75, 320);
    const s = Solver.new(cnf);
    const st = s.solve();
    switch (st) {
      case "Sat":
        expect(verify_model(cnf, s.model())).toBe(true);
        break;
      case "Unsat":
        break;
      case "Unknown":
        throw new Error("unreachable");
    }
  }
}, 120_000);

it("clause_deletion_keeps_answers_correct", () => {
  // Reduce after only a handful of learned clauses to exercise deletion hard.
  const rng = new Rng(0xc0ffeen);
  let deleted = 0;
  for (let round = 0; round < 400; round++) {
    const vars = 6 + (round % 7);
    const cnf = random_3sat(rng, vars, vars * 4 + (round % 5));
    const s = Solver.new(cnf);
    s.max_learnts = 4;
    const status = s.solve();
    expect(status === "Sat", `round ${round}`).toBe(brute_force_sat(cnf));
    if (status === "Sat") {
      expect(verify_model(cnf, s.model())).toBe(true);
    }
    deleted += s.stats.deleted;
  }
  for (let holes = 2; holes <= 7; holes++) {
    const s = Solver.new(pigeonhole(holes));
    s.max_learnts = 20;
    expect(s.solve()).toBe("Unsat");
    deleted += s.stats.deleted;
  }
  expect(deleted > 0, "test never triggered a reduction").toBe(true);
}, 120_000);

it("traces_never_contain_deletions", () => {
  // Even when asked to reduce early, a traced run defers deletion until
  // after the trace limit could have been reached.
  const cnf = pigeonhole(7);
  const s = Solver.with_tracer(cnf, Tracer.with_limit(30_000));
  s.max_learnts = 4;
  const status = s.solve();
  expect(status).toBe("Unsat");
  expect(s.stats.deleted === 0 || s.tracer.truncated).toBe(true);
  if (!s.tracer.truncated) {
    check_trace(cnf, s.tracer.events, status);
  }
}, 120_000);

it("limits_stop_the_solver", () => {
  const cnf = pigeonhole(9); // far too hard to finish within these limits

  let s = Solver.new(cnf);
  s.deadline = now();
  expect(s.solve()).toBe("Unknown");
  expect(s.stop_reason).toBe("TimeLimit");

  s = Solver.new(cnf);
  s.cancel = { value: true };
  expect(s.solve()).toBe("Unknown");
  expect(s.stop_reason).toBe("Cancelled");

  s = Solver.new(cnf);
  s.max_conflicts = 10;
  expect(s.solve()).toBe("Unknown");
  expect(s.stop_reason).toBe("ConflictLimit");
  expect(s.stats.conflicts).toBe(11);
});

it("truncated_trace_still_records_result", () => {
  const cnf = pigeonhole(5);
  const s = Solver.with_tracer(cnf, Tracer.with_limit(50));
  expect(s.solve()).toBe("Unsat");
  expect(s.tracer.truncated).toBe(true);
  expect(s.tracer.events.length).toBe(51);
  expect(s.tracer.events[s.tracer.events.length - 1]?.kind).toBe("Result");
});
