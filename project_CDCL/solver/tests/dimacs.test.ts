import { describe, it, expect } from "vitest";
import { parse, ParseError } from "../src/dimacs";
import { Lit, lit_to_dimacs } from "../src/lit";
import { RustErr } from "../src/util";

function d(c: Lit[]): number[] {
  return c.map(lit_to_dimacs);
}

function unwrap_err(f: () => unknown): ParseError {
  try {
    f();
  } catch (x) {
    if (x instanceof RustErr) return x.value as ParseError;
    throw x;
  }
  throw new Error("expected an error");
}

describe("dimacs", () => {
  it("parses_example_from_spec", () => {
    const cnf = parse(
      "c This is a comment line (starts with 'c')\nc Another comment\np cnf 5 3\n1 -5 4 0\n-1 5 3 4 0\n-3 -4 0\n",
    );
    expect(cnf.num_vars).toBe(5);
    expect(cnf.clauses.length).toBe(3);
    expect(d(cnf.clauses[0])).toEqual([1, -5, 4]);
    expect(d(cnf.clauses[1])).toEqual([-1, 5, 3, 4]);
    expect(d(cnf.clauses[2])).toEqual([-3, -4]);
    expect(cnf.warnings.length).toBe(0);
  });

  it("clauses_may_span_and_share_lines", () => {
    const cnf = parse("p cnf 3 3\n1 2\n3 0 -1 0\n-2\n-3 0\n");
    expect(d(cnf.clauses[0])).toEqual([1, 2, 3]);
    expect(d(cnf.clauses[1])).toEqual([-1]);
    expect(d(cnf.clauses[2])).toEqual([-2, -3]);
  });

  it("satlib_percent_terminator", () => {
    const cnf = parse("p cnf 2 1\n1 2 0\n%\n0\n\n");
    expect(cnf.clauses.length).toBe(1);
    expect(cnf.warnings.length).toBe(0);
  });

  it("empty_clause_is_kept", () => {
    const cnf = parse("p cnf 1 2\n1 0\n0\n");
    expect(cnf.clauses.length).toBe(2);
    expect(cnf.clauses[1].length).toBe(0);
  });

  it("warnings_for_count_mismatch_and_missing_terminator", () => {
    const cnf = parse("p cnf 2 5\n1 2 0\n-1");
    expect(cnf.clauses.length).toBe(2);
    expect(cnf.warnings.length).toBe(2);
  });

  it("errors", () => {
    expect(unwrap_err(() => parse("1 2 0\n")).message).toContain("before");
    expect(unwrap_err(() => parse("c only comments\n")).message).toContain("missing");
    expect(unwrap_err(() => parse("p cnf 2 1\n1 3 0\n")).line).toBe(2);
    expect(unwrap_err(() => parse("p cnf 2 1\n1 x 0\n")).message).toContain("'x'");
    expect(unwrap_err(() => parse("p cnf 2\n")).message).toContain("malformed");
    expect(unwrap_err(() => parse("p cnf 2 1\np cnf 2 1\n")).message).toContain("duplicate");
  });
});
