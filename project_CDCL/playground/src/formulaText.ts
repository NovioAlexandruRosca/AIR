// A readable way to type formulas, translated to the SMT-LIB the solver reads.
//
//   (x + 1 > 0 or x + y > 0) and (x < 0 or x + y > 4) and not (x + y > 0)
//   ((x <= y) \/ (z < y)) /\ (x <= y)
//
// Connectives: and && /\ \and ∧ · or || \/ \or ∨ · not ! ~ \not ¬ ·
// -> => ⇒ implies · <-> <=> ⇔ iff. Arithmetic: + - and multiplication by a
// number (2*x, 2x), comparisons < <= > >= = == != ≤ ≥ ≠. A name compared or
// added is an Int; a name used as a formula is a Bool. Each line (and each
// top-level "and") becomes one assertion.

type Tok = { t: string; pos: number };

const WORDS: Record<string, string> = {
  and: "and", or: "or", not: "not", implies: "=>", iff: "iff", true: "true", false: "false",
  "\\and": "and", "\\or": "or", "\\not": "not", "\\land": "and", "\\lor": "or", "\\lnot": "not", "\\neg": "not",
};
const SYMBOLS: [string, string][] = [
  ["<->", "iff"], ["<=>", "iff"], ["⇔", "iff"], ["->", "=>"], ["=>", "=>"], ["⇒", "=>"], ["→", "=>"],
  ["/\\", "and"], ["\\/", "or"], ["&&", "and"], ["||", "or"], ["∧", "and"], ["∨", "or"], ["&", "and"], ["|", "or"],
  ["¬", "not"], ["!=", "!="], ["/=", "!="], ["≠", "!="], ["!", "not"], ["~", "not"],
  ["<=", "<="], [">=", ">="], ["≤", "<="], ["≥", ">="], ["==", "="], ["=", "="], ["<", "<"], [">", ">"],
  ["+", "+"], ["-", "-"], ["−", "-"], ["*", "*"], ["·", "*"], ["(", "("], [")", ")"],
];

export class FormulaError extends Error {
  constructor(msg: string, public pos: number) {
    super(msg);
  }
}

function lex(src: string): Tok[] {
  const out: Tok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    const word = /^\\?[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i));
    if (word) {
      const w = word[0];
      out.push({ t: WORDS[w.toLowerCase()] ?? (w.startsWith("\\") ? bad(w, i) : w), pos: i });
      i += w.length;
      continue;
    }
    const numM = /^\d+/.exec(src.slice(i));
    if (numM) {
      out.push({ t: numM[0], pos: i });
      i += numM[0].length;
      continue;
    }
    const sym = SYMBOLS.find(([s]) => src.startsWith(s, i));
    if (!sym) throw new FormulaError(`unexpected '${c}'`, i);
    out.push({ t: sym[1], pos: i });
    i += sym[0].length;
  }
  return out;
}

function bad(w: string, pos: number): never {
  throw new FormulaError(`unknown command '${w}' (try \\and, \\or, \\not)`, pos);
}

const REL = new Set(["<", "<=", ">", ">=", "=", "!="]);
const isName = (t: string) => /^[A-Za-z_]/.test(t) && !["and", "or", "not", "=>", "iff", "true", "false"].includes(t);
const isNum = (t: string) => /^\d+$/.test(t);

/** Parse one formula into an SMT-LIB term, recording the sorts of the names it uses. */
class Parser {
  i = 0;
  constructor(private toks: Tok[], private sorts: Map<string, "Int" | "Bool">, private end: number) {}

  peek = () => this.toks[this.i]?.t;
  pos = () => this.toks[this.i]?.pos ?? this.end;
  next = () => this.toks[this.i++]?.t;
  expect(t: string) {
    if (this.peek() !== t) throw new FormulaError(this.peek() === undefined ? `missing '${t}'` : `expected '${t}' but found '${this.peek()}'`, this.pos());
    this.i++;
  }
  sort(name: string, s: "Int" | "Bool", pos: number) {
    const was = this.sorts.get(name);
    if (was && was !== s) throw new FormulaError(`'${name}' is used both as a number and as a formula`, pos);
    this.sorts.set(name, s);
  }

  formula(): string {
    const a = this.implication();
    if (this.peek() === "iff") {
      this.next();
      return `(= ${a} ${this.formula()})`;
    }
    return a;
  }
  implication(): string {
    const a = this.disjunction();
    if (this.peek() === "=>") {
      this.next();
      return `(=> ${a} ${this.implication()})`;
    }
    return a;
  }
  disjunction(): string {
    const xs = [this.conjunction()];
    while (this.peek() === "or") {
      this.next();
      xs.push(this.conjunction());
    }
    return xs.length === 1 ? xs[0] : `(or ${xs.join(" ")})`;
  }
  conjunction(): string {
    const xs = [this.negation()];
    while (this.peek() === "and") {
      this.next();
      xs.push(this.negation());
    }
    return xs.length === 1 ? xs[0] : `(and ${xs.join(" ")})`;
  }
  negation(): string {
    if (this.peek() === "not") {
      this.next();
      return `(not ${this.negation()})`;
    }
    return this.atom();
  }
  atom(): string {
    const t = this.peek();
    if (t === "true" || t === "false") {
      this.next();
      return t;
    }
    if (t === "(") {
      // a parenthesised formula, unless it turns out to be arithmetic: (x + y) > 3
      const save = this.i;
      const saved = new Map(this.sorts);
      let first: unknown = null;
      try {
        this.next();
        const f = this.formula();
        this.expect(")");
        if (!REL.has(this.peek() ?? "") && !["+", "-", "*"].includes(this.peek() ?? "")) return f;
      } catch (e) {
        first = e; // try arithmetic below; if that fails too, this is the better message
      }
      this.i = save;
      this.sorts.clear();
      saved.forEach((v, k) => this.sorts.set(k, v));
      try {
        return this.comparison();
      } catch (e) {
        throw first ?? e;
      }
    }
    if (t !== undefined && isName(t)) {
      const after = this.toks[this.i + 1]?.t;
      if (!REL.has(after ?? "") && !["+", "-", "*"].includes(after ?? "")) {
        this.sort(t, "Bool", this.pos());
        this.next();
        return t;
      }
    }
    return this.comparison();
  }
  comparison(): string {
    const a = this.sum();
    const op = this.peek();
    if (!op || !REL.has(op)) throw new FormulaError(op === undefined ? "a comparison (<, ≤, =, …) is missing" : `expected a comparison but found '${op}'`, this.pos());
    this.next();
    const b = this.sum();
    return op === "!=" ? `(not (= ${a} ${b}))` : `(${op} ${a} ${b})`;
  }
  sum(): string {
    let acc = this.product();
    while (this.peek() === "+" || this.peek() === "-") {
      const op = this.next();
      const b = this.product();
      acc = `(${op} ${acc} ${b})`;
    }
    return acc;
  }
  product(): string {
    let acc = this.unary();
    while (this.peek() === "*" || (isNum(stripNeg(acc)) && this.peek() !== undefined && isName(this.peek()!))) {
      if (this.peek() === "*") this.next(); // "2x" means 2*x
      const b = this.unary();
      if (!isNum(stripNeg(acc)) && !isNum(stripNeg(b))) throw new FormulaError("only multiplication by a number is linear", this.pos());
      acc = `(* ${acc} ${b})`;
    }
    return acc;
  }
  unary(): string {
    const t = this.peek();
    const pos = this.pos();
    if (t === "-") {
      this.next();
      const a = this.unary();
      return `(- ${a})`;
    }
    if (t === "(") {
      this.next();
      const s = this.sum();
      this.expect(")");
      return s;
    }
    if (t !== undefined && isNum(t)) {
      this.next();
      return t;
    }
    if (t !== undefined && isName(t)) {
      this.sort(t, "Int", pos);
      this.next();
      return t;
    }
    throw new FormulaError(t === undefined ? "the formula ends too early" : `unexpected '${t}'`, pos);
  }
}

const stripNeg = (s: string) => s.replace(/^\(- (\d+)\)$/, "$1");

/** The assertions of a readable formula, as SMT-LIB text. */
export function toSmtLib(src: string): string {
  const sorts = new Map<string, "Int" | "Bool">();
  const asserts: string[] = [];
  let offset = 0;
  for (const line of src.split("\n")) {
    const body = line.replace(/[;#].*$/, "");
    if (body.trim()) {
      let toks: Tok[];
      try {
        toks = lex(body);
      } catch (e) {
        throw e instanceof FormulaError ? new FormulaError(e.message, e.pos + offset) : e;
      }
      const p = new Parser(toks, sorts, body.length);
      let f: string;
      try {
        f = p.formula();
        if (p.peek() !== undefined) throw new FormulaError(`unexpected '${p.peek()}'`, p.pos());
      } catch (e) {
        throw e instanceof FormulaError ? new FormulaError(e.message, e.pos + offset) : e;
      }
      // a top-level conjunction becomes several assertions
      asserts.push(...splitAnd(f));
    }
    offset += line.length + 1;
  }
  if (!asserts.length) throw new FormulaError("type a formula", 0);
  const decls = [...sorts].map(([n, s]) => `(declare-const ${n} ${s})`);
  return ["; typed in the formula editor", ...decls, ...asserts.map((a) => `(assert ${a})`), "(check-sat)"].join("\n");
}

/** `(and A B C)` at the top → [A, B, C]. */
function splitAnd(f: string): string[] {
  if (!f.startsWith("(and ")) return [f];
  const out: string[] = [];
  let depth = 0;
  let start = -1;
  for (let i = 5; i < f.length - 1; i++) {
    const c = f[i];
    if (c === " " && depth === 0) {
      if (start >= 0) out.push(f.slice(start, i));
      start = -1;
      continue;
    }
    if (start < 0) start = i;
    if (c === "(") depth++;
    else if (c === ")") depth--;
  }
  if (start >= 0) out.push(f.slice(start, f.length - 1));
  return out;
}
