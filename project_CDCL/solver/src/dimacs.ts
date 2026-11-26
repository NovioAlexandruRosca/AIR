//! DIMACS CNF parser (the SAT Competition input format).
//!
//! Accepted:
//! - `c ...` comment lines (anywhere),
//! - one `p cnf <vars> <clauses>` header before the first clause,
//! - clauses as whitespace-separated non-zero integers terminated by `0`,
//!   possibly spanning several lines or sharing a line,
//! - a `%` line, which ends the formula (used by the SATLIB benchmark files).
//!
//! Recoverable irregularities (clause count differs from the header, a last
//! clause without its terminating `0`) are reported as warnings; everything
//! else is a `ParseError` with a line number.

import { Lit, lit_from_dimacs } from "./lit";
import { RustErr } from "./util";

export class Cnf {
  num_vars: number;
  clauses: Lit[][];
  warnings: string[];
  constructor(init?: Partial<Cnf>) {
    this.num_vars = init?.num_vars ?? 0;
    this.clauses = init?.clauses ?? [];
    this.warnings = init?.warnings ?? [];
  }
}

export class ParseError {
  line: number;
  message: string;
  constructor(line: number, message: string) {
    this.line = line;
    this.message = message;
  }

  /** `impl Display` */
  toString(): string {
    if (this.line === 0) {
      return this.message;
    } else {
      return `line ${this.line}: ${this.message}`;
    }
  }
}

function err(line: number, message: string): RustErr<ParseError> {
  return new RustErr(new ParseError(line, message));
}

const U64_MAX = (1n << 64n) - 1n;
const I64_MIN = -(1n << 63n);
const I64_MAX = (1n << 63n) - 1n;

/** `str::parse::<usize>()`; null on error. */
function parse_usize(s: string): number | null {
  if (!/^\+?[0-9]+$/.test(s)) return null;
  const b = BigInt(s);
  if (b > U64_MAX) return null;
  return Number(b);
}

/** `str::parse::<i64>()`; null on error. */
function parse_i64(s: string): number | null {
  if (!/^[+-]?[0-9]+$/.test(s)) return null;
  const b = BigInt(s);
  if (b < I64_MIN || b > I64_MAX) return null;
  return Number(b);
}

/** Rust `str::lines`: split on `\n`, strip a trailing `\r`, no final empty line. */
function rust_lines(input: string): string[] {
  if (input.length === 0) return [];
  const parts = input.split("\n");
  if (parts[parts.length - 1] === "") parts.pop();
  return parts.map((p) => (p.endsWith("\r") ? p.slice(0, -1) : p));
}

function split_whitespace(s: string): string[] {
  return s.split(/\s+/).filter((t) => t.length > 0);
}

export function parse(input: string): Cnf {
  let header: [number, number] | null = null;
  const clauses: Lit[][] = [];
  let current: Lit[] = [];
  const warnings: string[] = [];

  const lines = rust_lines(input);
  for (let i = 0; i < lines.length; i++) {
    const raw = lines[i];
    const line_no = i + 1;
    const line = raw.trim();
    if (line.length === 0 || line.startsWith("c")) {
      continue;
    }
    if (line.startsWith("%")) {
      break;
    }
    if (line.startsWith("p")) {
      if (header !== null) {
        throw err(line_no, "duplicate 'p cnf' header");
      }
      const parts = split_whitespace(line);
      if (parts.length !== 4 || parts[0] !== "p" || parts[1] !== "cnf") {
        throw err(line_no, `malformed header '${line}', expected 'p cnf <vars> <clauses>'`);
      }
      const vars = parse_usize(parts[2]);
      if (vars === null) throw err(line_no, `invalid variable count '${parts[2]}'`);
      const ncl = parse_usize(parts[3]);
      if (ncl === null) throw err(line_no, `invalid clause count '${parts[3]}'`);
      header = [vars, ncl];
      continue;
    }

    if (header === null) {
      throw err(line_no, "clause found before the 'p cnf <vars> <clauses>' header");
    }
    const num_vars = header[0];

    for (const tok of split_whitespace(line)) {
      const x = parse_i64(tok);
      if (x === null) {
        throw err(line_no, `'${tok}' is not an integer literal`);
      }
      if (x === 0) {
        clauses.push(current);
        current = [];
        continue;
      }
      if (Math.abs(x) > num_vars) {
        throw err(line_no, `literal ${x} uses a variable above the declared ${num_vars}`);
      }
      current.push(lit_from_dimacs(x));
    }
  }

  if (header === null) {
    throw err(0, "missing 'p cnf <vars> <clauses>' header");
  }
  const [num_vars, declared] = header;

  if (current.length !== 0) {
    warnings.push("last clause was not terminated by 0; accepted anyway");
    clauses.push(current);
  }
  if (clauses.length !== declared) {
    warnings.push(`header declares ${declared} clauses but ${clauses.length} were read`);
  }

  return new Cnf({ num_vars, clauses, warnings });
}
