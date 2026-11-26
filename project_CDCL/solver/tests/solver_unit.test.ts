import { describe, it, expect } from "vitest";
import { parse } from "../src/dimacs";
import { Lit, lit_from_dimacs } from "../src/lit";
import { Solver, TheoryClause, TheoryHook, TheoryResponse, to_dimacs_sorted, verify_model } from "../src/solver";
import { Tracer } from "../src/trace";

function lit(x: number): Lit {
  return lit_from_dimacs(x);
}

function sorted(lits: Lit[]): number[] {
  return to_dimacs_sorted(lits);
}

/// A toy theory: variables 0 and 1 may not both be true. It reports a
/// conflict instead of using a clause, so the solver has to learn it.
class NotBoth extends TheoryHook {
  check(sat: Solver, _final_check: boolean): TheoryResponse {
    const r = TheoryResponse.default();
    if (sat.value(lit(1)) === true && sat.value(lit(2)) === true) {
      r.conflict = new TheoryClause([lit(-1), lit(-2)], "toy", "x1 and x2 exclude each other");
    } else if (sat.value(lit(1)) === true && sat.value(lit(2)) === null) {
      r.propagations.push(new TheoryClause([lit(-2), lit(-1)], "toy", "x1 excludes x2"));
    }
    return r;
  }
  backjump(_level: number, _trail_len: number): void {}
}

describe("solver", () => {
  it("bcp_records_reasons_and_levels", () => {
    // C1: ¬1 ∨ 2, C2: ¬2 ∨ 3, C3: ¬3 ∨ ¬1 ∨ 4
    const cnf = parse("p cnf 4 3\n-1 2 0\n-2 3 0\n-3 -1 4 0\n");
    const s = Solver.new(cnf);
    s.decide(lit(1));
    expect(s.propagate()).toBe(null);
    expect(s.trail()).toEqual([lit(1), lit(2), lit(3), lit(4)]);
    expect(s.reason[0]).toBe(null);
    expect(s.reason[1]).toBe(0);
    expect(s.reason[2]).toBe(1);
    expect(s.reason[3]).toBe(2);
    expect(s.level.every((l) => l === 1)).toBe(true);
  });

  it("bcp_detects_conflict", () => {
    const cnf = parse("p cnf 2 3\n-1 2 0\n-1 -2 0\n1 2 0\n");
    const s = Solver.new(cnf);
    s.decide(lit(1));
    expect(s.propagate()).toBe(1);
  });

  /// Hand-checked First-UIP example (see solver.rs).
  it("first_uip_hand_checked", () => {
    const cnf = parse("p cnf 8 6\n-1 6 0\n-6 2 0\n-6 3 5 0\n-2 4 0\n-3 -4 0\n7 8 0\n");
    const s = Solver.with_tracer(cnf, Tracer.with_limit(1000));
    s.decide(lit(-5));
    expect(s.propagate()).toBe(null);
    s.decide(lit(7));
    expect(s.propagate()).toBe(null);
    s.decide(lit(1));
    const confl = s.propagate();
    expect(confl).toBe(4); // C5

    const [learnt, bt, conflict_side] = s.analyze(confl!);
    expect(learnt[0]).toBe(lit(-6));
    expect(sorted(learnt)).toEqual([5, -6]);
    expect(bt).toBe(1);
    expect(conflict_side).toEqual([4, 3, 2]);

    const resolves: [number, number, number[]][] = [];
    for (const e of s.tracer.events) {
      if (e.kind === "Resolve") resolves.push([e.clause_b, e.pivot, e.resolvent]);
    }
    expect(resolves).toEqual([
      [3, 4, [-2, -3]],
      [2, 3, [-2, 5, -6]],
      [1, 2, [5, -6]],
    ]);

    s.backjump(bt);
    expect(s.decision_level()).toBe(1);
    expect(s.lit_value(lit(-5))).toBe(true);
    expect(s.lit_value(lit(7))).toBe(null);
  });

  it("full_solve_learns_and_asserts", () => {
    const cnf = parse("p cnf 8 6\n-1 6 0\n-6 2 0\n-6 3 5 0\n-2 4 0\n-3 -4 0\n7 8 0\n");
    const s = Solver.new(cnf);
    expect(s.solve()).toBe("Sat");
    expect(verify_model(cnf, s.model())).toBe(true);
  });

  it("moms_picks_most_frequent_in_smallest_clauses", () => {
    const cnf = parse("p cnf 6 4\n1 2 0\n1 3 0\n-2 3 0\n4 5 6 0\n");
    const s = Solver.with_tracer(cnf, Tracer.with_limit(10));
    const [l, min, cands] = s.pick_branch()!;
    expect(min).toBe(2);
    expect(l).toBe(lit(2));
    expect(cands[0].var).toBe(2);
    expect(cands[0].score).toBe(5);
  });

  it("unit_and_empty_input_clauses", () => {
    const unsat = parse("p cnf 1 2\n1 0\n-1 0\n");
    expect(Solver.new(unsat).solve()).toBe("Unsat");
    const empty = parse("p cnf 1 1\n0\n");
    expect(Solver.new(empty).solve()).toBe("Unsat");
    const sat = parse("p cnf 2 2\n1 0\n-1 2 0\n");
    const s = Solver.new(sat);
    expect(s.solve()).toBe("Sat");
    expect(s.model_dimacs()).toEqual([1, 2]);
  });

  it("duplicate_literals_are_merged", () => {
    const cnf = parse("p cnf 2 2\n1 1 0\n-1 2 2 0\n");
    const s = Solver.new(cnf);
    expect(s.solve()).toBe("Sat");
    expect(s.model_dimacs()).toEqual([1, 2]);
  });

  it("theory_hook_propagates_and_conflicts", () => {
    // (x1 ∨ x3) ∧ (x2 ∨ x3) ∧ (¬x3): forces x1 and x2, which the theory forbids.
    let cnf = parse("p cnf 3 3\n1 3 0\n2 3 0\n-3 0\n");
    let s = Solver.with_tracer(cnf, Tracer.with_limit(1000));
    s.hook = new NotBoth();
    expect(s.solve()).toBe("Unsat");
    expect(s.tracer.events.some((e) => e.kind === "TheoryClause")).toBe(true);

    // Without ¬x3 the theory pushes x2 false and x3 must be true.
    cnf = parse("p cnf 3 2\n1 3 0\n2 3 0\n");
    s = Solver.new(cnf);
    s.hook = new NotBoth();
    expect(s.solve()).toBe("Sat");
    const m = s.model();
    expect(!(m[0] && m[1])).toBe(true);
    expect(m[2] || (m[0] && m[1])).toBe(true);
  });

  it("replay_stops_at_conflict", () => {
    // ¬1∨2, ¬2∨¬3, 3∨¬1∨4: deciding 3 forces ¬2 and then ¬1.
    let cnf = parse("p cnf 4 3\n-1 2 0\n-2 -3 0\n3 -1 4 0\n");
    let s = Solver.new(cnf);
    let r = s.replay([lit(3), lit(1)]);
    expect(r.outcome).toBe("sat");
    expect(r.skipped).toEqual([[1, false]]);
    expect(s.value(lit(-1))).toBe(true);

    s = Solver.new(cnf);
    r = s.replay([lit(1), lit(3)]);
    expect(r.outcome).toBe("sat");
    expect(r.skipped).toEqual([[1, false]]);
    expect(s.value(lit(2))).toBe(true);
    expect(s.value(lit(4))).toBe(true);

    // Only the first decision: clauses still open.
    cnf = parse("p cnf 3 2\n-1 2 0\n2 3 1 0\n");
    s = Solver.new(cnf);
    r = s.replay([lit(-1)]);
    expect(r.outcome).toBe("open");

    // A decision whose propagation falsifies a clause.
    cnf = parse("p cnf 2 2\n-1 2 0\n-1 -2 0\n");
    s = Solver.new(cnf);
    r = s.replay([lit(1)]);
    expect(r.outcome).toBe("conflict");
    expect(r.applied).toBe(1);
  });
});
