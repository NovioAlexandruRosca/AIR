//! S-expression reader for SMT-LIB input.
// (port of src/smt/sexp.rs)

import { RustErr } from "../util";

export type Sexp =
  /** Symbol, numeral, keyword or string literal, with its line number. */
  | { kind: "Atom"; _0: string; _1: number }
  | { kind: "List"; _0: Sexp[]; _1: number };

export class SmtError {
  constructor(
    public line: number,
    public message: string,
  ) {}

  // impl Display for SmtError
  to_string(): string {
    if (this.line === 0) {
      return `${this.message}`;
    } else {
      return `line ${this.line}: ${this.message}`;
    }
  }

  toString(): string {
    return this.to_string();
  }
}

/** `Err(SmtError { line, message })`: throws `RustErr<SmtError>`. */
export function err(line: number, message: string): never {
  throw new RustErr(new SmtError(line, message));
}

export function Sexp_line(s: Sexp): number {
  return s._1;
}

export function Sexp_atom(s: Sexp): string | null {
  return s.kind === "Atom" ? s._0 : null;
}

export function Sexp_list(s: Sexp): Sexp[] | null {
  return s.kind === "List" ? s._0 : null;
}

/** The head symbol of a list, e.g. `assert` for `(assert ...)`. */
export function Sexp_head(s: Sexp): string | null {
  const l = Sexp_list(s);
  if (l === null || l.length === 0) return null;
  return Sexp_atom(l[0]);
}

// impl Display for Sexp
export function Sexp_to_string(s: Sexp): string {
  switch (s.kind) {
    case "Atom":
      return s._0;
    case "List": {
      let out = "(";
      s._0.forEach((x, i) => {
        if (i > 0) out += " ";
        out += Sexp_to_string(x);
      });
      return out + ")";
    }
  }
}

/** Rust `char::is_whitespace` (Unicode White_Space property). */
export function is_whitespace(c: string): boolean {
  const x = c.codePointAt(0)!;
  return (
    (x >= 0x09 && x <= 0x0d) ||
    x === 0x20 ||
    x === 0x85 ||
    x === 0xa0 ||
    x === 0x1680 ||
    (x >= 0x2000 && x <= 0x200a) ||
    x === 0x2028 ||
    x === 0x2029 ||
    x === 0x202f ||
    x === 0x205f ||
    x === 0x3000
  );
}

/** Parse every top-level s-expression. `;` starts a comment. */
export function parse_all(text: string): Sexp[] {
  // Rust iterates over chars (code points), not UTF-16 units.
  const chars: string[] = Array.from(text);
  let i = 0;
  let line = 1;
  const stack: [Sexp[], number][] = [];
  const top: Sexp[] = [];

  const push = (e: Sexp) => {
    if (stack.length > 0) stack[stack.length - 1][0].push(e);
    else top.push(e);
  };

  while (i < chars.length) {
    const c = chars[i];
    if (c === "\n") {
      line += 1;
      i += 1;
    } else if (is_whitespace(c)) {
      i += 1;
    } else if (c === ";") {
      while (i < chars.length && chars[i] !== "\n") {
        i += 1;
      }
    } else if (c === "(") {
      stack.push([[], line]);
      i += 1;
    } else if (c === ")") {
      const x = stack.pop();
      if (x === undefined) return err(line, "unexpected ')'");
      const [items, l] = x;
      push({ kind: "List", _0: items, _1: l });
      i += 1;
    } else if (c === '"') {
      const start_line = line;
      let s = '"';
      i += 1;
      for (;;) {
        if (i >= chars.length) {
          return err(start_line, "unterminated string literal");
        }
        const ch = chars[i];
        i += 1;
        if (ch === "\n") {
          line += 1;
        }
        if (ch === '"') {
          // "" is an escaped quote in SMT-LIB 2.6
          if (i < chars.length && chars[i] === '"') {
            s += '"';
            i += 1;
            continue;
          }
          break;
        }
        s += ch;
      }
      s += '"';
      push({ kind: "Atom", _0: s, _1: start_line });
    } else if (c === "|") {
      const start_line = line;
      let s = "";
      i += 1;
      for (;;) {
        if (i >= chars.length) {
          return err(start_line, "unterminated |quoted symbol|");
        }
        const ch = chars[i];
        i += 1;
        if (ch === "\n") {
          line += 1;
        }
        if (ch === "|") {
          break;
        }
        s += ch;
      }
      push({ kind: "Atom", _0: s, _1: start_line });
    } else {
      let s = "";
      while (i < chars.length) {
        const ch = chars[i];
        if (is_whitespace(ch) || ch === "(" || ch === ")" || ch === ";" || ch === '"' || ch === "|") {
          break;
        }
        s += ch;
        i += 1;
      }
      push({ kind: "Atom", _0: s, _1: line });
    }
  }
  if (stack.length > 0) {
    return err(stack[stack.length - 1][1], "unclosed '(' (missing ')')");
  }
  return top;
}
