import { describe, it, expect } from "vitest";
import { Rat, div_ceil, div_floor } from "../src/smt/rat";

describe("rat", () => {
  it("arithmetic_and_rounding", () => {
    const a = Rat.new(5n, 2n);
    expect(a.floor()).toBe(2n);
    expect(a.ceil()).toBe(3n);
    expect(a.neg().floor()).toBe(-3n);
    expect(a.neg().ceil()).toBe(-2n);
    expect(a.add(Rat.new(1n, 2n)).eq(Rat.int(3n))).toBe(true);
    expect(a.mul(Rat.new(2n, 5n)).eq(Rat.ONE)).toBe(true);
    expect(a.div(Rat.new(5n, 4n)).eq(Rat.int(2n))).toBe(true);
    expect(Rat.new(1n, 3n).lt(Rat.new(1n, 2n))).toBe(true);
    expect(Rat.new(4n, -6n).to_string()).toBe("-2/3");
    expect(div_floor(-7n, 2n)).toBe(-4n);
    expect(div_ceil(-7n, 2n)).toBe(-3n);
    expect(div_ceil(7n, 2n)).toBe(4n);
  });
});
