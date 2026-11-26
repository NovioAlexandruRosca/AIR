//! SMT-LIB 2 subset: declarations, `assert`, `let`, Boolean connectives and
//! whatever symbols the registered theories own. Theory-specific commands
//! (e.g. `declare-datatypes`) are handed to the theories.
// (port of src/smt/parser.rs)

import { err, parse_all, Sexp, Sexp_atom, Sexp_line, Sexp_list, Sexp_to_string, is_whitespace } from "./sexp";
import { TermId, Terms, BOOL } from "./term";
import { Theory } from "./theory";
import { RustErr } from "../util";

const I128_MAX = (1n << 127n) - 1n;

export class Problem {
  logic: string | null;
  /** Declared constants, in declaration order. */
  consts: TermId[];
  /** Asserted formulas (Bool-sorted terms). */
  assertions: TermId[];
  check_sat: boolean;

  constructor(init?: Partial<Problem>) {
    this.logic = init?.logic ?? null;
    this.consts = init?.consts ?? [];
    this.assertions = init?.assertions ?? [];
    this.check_sat = init?.check_sat ?? false;
  }
}

/** `.or_else(|m| err(line, m))` on a `Result<T, String>`. */
function or_err<T>(line: number, f: () => T): T {
  try {
    return f();
  } catch (x) {
    if (!(x instanceof RustErr)) throw x;
    return err(line, x.value as string);
  }
}

class Parser {
  terms: Terms;
  theories: Theory[];
  consts: Map<string, TermId> = new Map();
  /** `define-fun` macros without arguments. */
  macros: Map<string, TermId> = new Map();
  scopes: Map<string, TermId>[] = [];

  constructor(terms: Terms, theories: Theory[]) {
    this.terms = terms;
    this.theories = theories;
  }

  command(cmd: Sexp, problem: Problem): void {
    const line = Sexp_line(cmd);
    const l = Sexp_list(cmd);
    if (l === null || l.length === 0) {
      return err(line, `expected a command in parentheses, got ${Sexp_to_string(cmd)}`);
    }
    const items = l;
    const head = Sexp_atom(items[0]);
    if (head === null) return err(line, "command name expected");
    switch (head) {
      case "set-logic":
        problem.logic = items.length > 1 ? Sexp_atom(items[1]) : null;
        break;
      case "set-info":
      case "set-option":
      case "get-model":
      case "get-info":
      case "exit":
      case "echo":
      case "get-assertions":
        break;
      case "check-sat":
        problem.check_sat = true;
        break;
      case "declare-const": {
        if (items.length !== 3) {
          return err(line, "usage: (declare-const name Sort)");
        }
        const name = this.symbol(items[1]);
        const sort = this.sort(items[2]);
        this.declare(name, sort, line, problem);
        break;
      }
      case "declare-fun": {
        if (items.length !== 4) {
          return err(line, "usage: (declare-fun name () Sort)");
        }
        const name = this.symbol(items[1]);
        const l2 = Sexp_list(items[2]);
        if (l2 === null || l2.length !== 0) {
          return err(line, `'${name}' takes arguments: uninterpreted functions are not supported (only constants)`);
        }
        const sort = this.sort(items[3]);
        this.declare(name, sort, line, problem);
        break;
      }
      case "define-fun": {
        const l2 = items.length > 2 ? Sexp_list(items[2]) : null;
        if (items.length !== 5 || l2 === null || l2.length !== 0) {
          return err(line, "only argument-free (define-fun name () Sort term) is supported");
        }
        const name = this.symbol(items[1]);
        const sort = this.sort(items[3]);
        const body = this.term(items[4]);
        if (this.terms.sort(body) !== sort) {
          return err(line, `define-fun '${name}': body has sort ${this.terms.sort_name(this.terms.sort(body))}`);
        }
        this.macros.set(name, body);
        break;
      }
      case "assert": {
        if (items.length !== 2) {
          return err(line, "usage: (assert formula)");
        }
        const t = this.term(items[1]);
        if (this.terms.sort(t) !== BOOL) {
          return err(line, `assert needs a Bool formula, got sort ${this.terms.sort_name(this.terms.sort(t))}`);
        }
        problem.assertions.push(t);
        break;
      }
      case "push":
      case "pop":
      case "reset":
      case "check-sat-assuming":
        return err(line, `'${head}' is not supported (single check-sat only)`);
      default: {
        for (let me = 0; me < this.theories.length; me++) {
          if (this.theories[me].command(cmd, this.terms, me)) {
            return;
          }
        }
        return err(line, `unknown or unsupported command '${head}'`);
      }
    }
  }

  declare(name: string, sort: number, line: number, problem: Problem): void {
    if (this.consts.has(name) || this.terms.fun_owner(name) !== null) {
      return err(line, `'${name}' is already declared`);
    }
    const v = this.terms.var(name, sort);
    this.consts.set(name, v);
    problem.consts.push(v);
  }

  symbol(s: Sexp): string {
    const a = Sexp_atom(s);
    if (a !== null && !a.startsWith('"')) return a;
    return err(Sexp_line(s), `symbol expected, got ${Sexp_to_string(s)}`);
  }

  sort(s: Sexp): number {
    const name = Sexp_atom(s);
    if (name === null) return err(Sexp_line(s), `parametric sort ${Sexp_to_string(s)} is not supported`);
    const id = this.terms.sort_named(name);
    if (id !== null) return id;
    return err(Sexp_line(s), `unknown sort '${name}'`);
  }

  lookup(name: string): TermId | null {
    for (let i = this.scopes.length - 1; i >= 0; i--) {
      const t = this.scopes[i].get(name);
      if (t !== undefined) {
        return t;
      }
    }
    return this.macros.get(name) ?? this.consts.get(name) ?? null;
  }

  term(s: Sexp): TermId {
    const line = Sexp_line(s);
    if (s.kind === "Atom") return this.atom_term(s._0, line);
    const items = s._0;
    if (items.length === 0) {
      return err(line, "empty term ()");
    }
    let head: string;
    const h = items[0];
    if (h.kind === "Atom") {
      head = h._0;
    } else {
      // ((_ is C) t): indexed tester
      const idx = h._0;
      if (
        idx.length === 3 &&
        idx[0].kind === "Atom" &&
        idx[1].kind === "Atom" &&
        idx[2].kind === "Atom" &&
        idx[0]._0 === "_" &&
        idx[1]._0 === "is"
      ) {
        head = `is-${idx[2]._0}`;
      } else {
        return err(line, `unsupported function head ${Sexp_to_string(items[0])}`);
      }
    }
    switch (head) {
      case "let":
        return this.let_term(items, line);
      case "!":
        if (items.length > 1) return this.term(items[1]);
        return err(line, "empty annotation (!)");
      case "_":
        return err(line, `unsupported indexed term ${Sexp_to_string(s)}`);
    }
    const args: TermId[] = [];
    for (const a of items.slice(1)) {
      args.push(this.term(a));
    }
    return this.app(head, args, line);
  }

  atom_term(a: string, line: number): TermId {
    if (a === "true") {
      return this.terms.bool_const(true);
    }
    if (a === "false") {
      return this.terms.bool_const(false);
    }
    if (/^[0-9]+$/.test(a)) {
      const n = BigInt(a);
      if (n > I128_MAX) return err(line, `numeral ${a} is too large`);
      const int = this.terms.sort_named("Int");
      if (int !== null) return this.terms.num(n, int);
      return err(line, "numerals need a theory that provides Int");
    }
    const t = this.lookup(a);
    if (t !== null) {
      return t;
    }
    const owner = this.terms.fun_owner(a);
    if (owner !== null) {
      return or_err(line, () => this.theories[owner].mk_app(a, [], this.terms));
    }
    return err(line, `unknown symbol '${a}' (declare it with declare-const)`);
  }

  let_term(items: Sexp[], line: number): TermId {
    if (items.length !== 3) {
      return err(line, "usage: (let ((x t) ...) body)");
    }
    const bindings = Sexp_list(items[1]);
    if (bindings === null) return err(line, "let bindings must be a list");
    // Parallel let: all bound terms are read in the outer scope.
    const scope: Map<string, TermId> = new Map();
    for (const b of bindings) {
      const l = Sexp_list(b);
      if (l !== null && l.length === 2) {
        const n = this.symbol(l[0]);
        const v = this.term(l[1]);
        scope.set(n, v);
      } else {
        return err(Sexp_line(b), "let binding must be (name term)");
      }
    }
    this.scopes.push(scope);
    try {
      return this.term(items[2]);
    } finally {
      this.scopes.pop();
    }
  }

  expect_bool(args: TermId[], op: string, line: number): void {
    for (const a of args) {
      if (this.terms.sort(a) !== BOOL) {
        return err(
          line,
          `'${op}' expects Bool arguments, got ${this.terms.display(a)} : ${this.terms.sort_name(this.terms.sort(a))}`,
        );
      }
    }
  }

  same_sort(args: TermId[], op: string, line: number): void {
    if (args.length < 2) {
      return err(line, `'${op}' needs at least two arguments`);
    }
    const s = this.terms.sort(args[0]);
    for (const a of args.slice(1)) {
      if (this.terms.sort(a) !== s) {
        return err(
          line,
          `'${op}' mixes sorts ${this.terms.sort_name(s)} and ${this.terms.sort_name(this.terms.sort(a))}`,
        );
      }
    }
  }

  /** `a = b`, with constant-constant equalities in a canonical order so
   * `x = y` and `y = x` are the same atom. */
  mk_eq(a: TermId, b: TermId): TermId {
    if (this.terms.is_var(a) && this.terms.is_var(b) && b < a) {
      [a, b] = [b, a];
    }
    return this.terms.app("=", [a, b], BOOL);
  }

  app(head: string, args: TermId[], line: number): TermId {
    switch (head) {
      case "not":
        if (args.length !== 1) {
          return err(line, "'not' takes one argument");
        }
        this.expect_bool(args, head, line);
        return this.terms.app("not", args, BOOL);
      case "and":
      case "or":
        this.expect_bool(args, head, line);
        switch (args.length) {
          case 0:
            return this.terms.bool_const(head === "and");
          case 1:
            return args[0];
          default:
            return this.terms.app(head, args, BOOL);
        }
      case "=>": {
        if (args.length < 2) {
          return err(line, "'=>' needs at least two arguments");
        }
        this.expect_bool(args, head, line);
        // right associative
        let acc = args[args.length - 1];
        for (const a of args.slice(0, args.length - 1).reverse()) {
          acc = this.terms.app("=>", [a, acc], BOOL);
        }
        return acc;
      }
      case "xor": {
        if (args.length < 2) {
          return err(line, "'xor' needs at least two arguments");
        }
        this.expect_bool(args, head, line);
        let acc = args[0];
        for (const a of args.slice(1)) {
          acc = this.terms.app("xor", [acc, a], BOOL);
        }
        return acc;
      }
      case "=": {
        this.same_sort(args, head, line);
        const pairs: TermId[] = [];
        for (let i = 0; i + 1 < args.length; i++) {
          pairs.push(this.mk_eq(args[i], args[i + 1]));
        }
        return pairs.length === 1 ? pairs[0] : this.terms.app("and", pairs, BOOL);
      }
      case "distinct": {
        this.same_sort(args, head, line);
        const parts: TermId[] = [];
        for (let i = 0; i < args.length; i++) {
          for (let j = i + 1; j < args.length; j++) {
            const eq = this.mk_eq(args[i], args[j]);
            parts.push(this.terms.app("not", [eq], BOOL));
          }
        }
        return parts.length === 1 ? parts[0] : this.terms.app("and", parts, BOOL);
      }
      case "ite":
        if (args.length !== 3) {
          return err(line, "'ite' takes three arguments");
        }
        this.expect_bool(args.slice(0, 1), head, line);
        this.same_sort(args.slice(1), head, line);
        if (this.terms.sort(args[1]) !== BOOL) {
          return err(
            line,
            "ite over non-Boolean terms is not supported; write the case split with Boolean connectives",
          );
        }
        return this.terms.app("ite", args, BOOL);
      default: {
        if (this.lookup(head) !== null) {
          return err(line, `'${head}' is a constant, not a function`);
        }
        const owner = this.terms.fun_owner(head);
        if (owner !== null) {
          return or_err(line, () => this.theories[owner].mk_app(head, args, this.terms));
        }
        return err(line, `unknown function '${head}'`);
      }
    }
  }
}

export function parse_problem(text: string, terms: Terms, theories: Theory[]): Problem {
  const cmds = parse_all(text);
  const p = new Parser(terms, theories);
  const problem = new Problem();
  for (const cmd of cmds) {
    p.command(cmd, problem);
  }
  if (problem.assertions.length === 0 && !problem.check_sat) {
    return err(0, "no (assert ...) or (check-sat) found: is this an SMT-LIB file?");
  }
  return problem;
}

/** Rust `str::trim` (Unicode White_Space on both ends). */
function trim(s: string): string {
  const chars = Array.from(s);
  let a = 0;
  let b = chars.length;
  while (a < b && is_whitespace(chars[a])) a++;
  while (b > a && is_whitespace(chars[b - 1])) b--;
  return chars.slice(a, b).join("");
}

/** Is this text SMT-LIB (as opposed to DIMACS)? The first non-comment
 * character of SMT-LIB is '('. */
export function looks_like_smtlib(text: string): boolean {
  for (const line of text.split("\n")) {
    const l = trim(line);
    if (l.length === 0 || l.startsWith(";")) {
      continue;
    }
    return l.startsWith("(");
  }
  return false;
}
