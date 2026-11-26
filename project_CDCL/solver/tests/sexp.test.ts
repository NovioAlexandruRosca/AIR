import { describe, it, expect } from "vitest";
import { parse_all, Sexp_atom, Sexp_head, Sexp_line, Sexp_list, Sexp_to_string, SmtError } from "../src/smt/sexp";
import { RustErr } from "../src/util";

function unwrap_err(f: () => unknown): SmtError {
  try {
    f();
  } catch (x) {
    if (x instanceof RustErr) return x.value as SmtError;
    throw x;
  }
  throw new Error("expected an error");
}

describe("sexp", () => {
  it("parses_nested_lists_comments_and_strings", () => {
    const s = parse_all('; hello\n(assert (<= x 3)) ; tail\n(set-info :source "a ""b""")\n');
    expect(s.length).toBe(2);
    expect(Sexp_head(s[0])).toBe("assert");
    expect(Sexp_to_string(s[0])).toBe("(assert (<= x 3))");
    expect(Sexp_atom(Sexp_list(s[1])![2])).toBe('"a "b""');
    expect(Sexp_line(s[1])).toBe(3);
  });

  it("reports_unbalanced_parentheses", () => {
    expect(unwrap_err(() => parse_all("(a (b)")).line).toBe(1);
    expect(unwrap_err(() => parse_all("a)")).message.includes("unexpected")).toBe(true);
  });
});
