import { describe, it, expect } from "vitest";
import { BOOL, Terms } from "../src/smt/term";

describe("term", () => {
  it("hash_consing_and_display", () => {
    const t = Terms.new();
    const int = t.add_sort("Int", 0);
    const x = t.var("x", int);
    const y = t.var("y", int);
    const two = t.num(2n, int);
    const m = t.app("*", [two, y], int);
    const s1 = t.app("+", [x, m], int);
    const s2 = t.app("+", [x, m], int);
    expect(s1).toBe(s2);
    const three = t.num(3n, int);
    const le = t.app("<=", [s1, three], BOOL);
    expect(t.display(le)).toBe("x + 2·y ≤ 3");
    expect(t.display_neg(le)).toBe("x + 2·y > 3");
    expect(t.to_smtlib(le)).toBe("(<= (+ x (* 2 y)) 3)");
    const d = t.app("-", [x, s1], int);
    expect(t.display(d)).toBe("x - (x + 2·y)");
  });

  it("fresh_names_avoid_declared_ones", () => {
    const t = Terms.new();
    const int = t.add_sort("Int", 0);
    t.var("k1", int);
    const f = t.fresh_var("k", int);
    expect(t.var_name(f)).toBe("k2");
  });
});
