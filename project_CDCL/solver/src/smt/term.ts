//! Hash-consed terms, sorts and the signature (which theory owns which
//! sort and function symbol). Formulas are Bool-sorted terms.
// (port of src/smt/term.rs)

export type TermId = number;
export type SortId = number;
export type TheoryId = number;

/** The only built-in sort: everything else is provided by a theory. */
export const BOOL: SortId = 0;

/** Core (theory-independent) Boolean symbols. */
export const CORE_SYMBOLS: string[] = ["and", "or", "not", "=>", "xor", "=", "distinct", "ite"];

export class SortInfo {
  constructor(
    public name: string,
    /** Theory that owns the sort (None for Bool). */
    public theory: TheoryId | null,
  ) {}

  clone(): SortInfo {
    return new SortInfo(this.name, this.theory);
  }
}

export type Op =
  /** Uninterpreted constant (declared, or created by purification). */
  | { kind: "Var"; _0: string }
  /** Integer numeral. */
  | { kind: "Num"; _0: bigint }
  | { kind: "True" }
  | { kind: "False" }
  /** Application of a core or theory symbol. */
  | { kind: "App"; _0: string };

/** derive(PartialEq) for Op. */
export function Op_eq(a: Op, b: Op): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "True" || a.kind === "False") return true;
  return (a as { _0: unknown })._0 === (b as { _0: unknown })._0;
}

/** Hash key of an Op (one letter for the variant, then the payload). */
function op_key(op: Op): string {
  switch (op.kind) {
    case "Var":
      return "V" + op._0;
    case "Num":
      return "N" + op._0.toString();
    case "True":
      return "T";
    case "False":
      return "F";
    case "App":
      return "A" + op._0;
  }
}

export class Node {
  constructor(
    public op: Op,
    public args: TermId[],
    public sort: SortId,
  ) {}

  clone(): Node {
    return new Node(this.op, this.args.slice(), this.sort);
  }
}

/** HashMap<Node, TermId> key: `sort;args;op` (the op goes last since a
 * symbol name may contain any character). */
function node_key(n: Node): string {
  return `${n.sort};${n.args.join(",")};${op_key(n.op)}`;
}

/** Term bank + signature. */
export class Terms {
  private nodes: Node[] = [];
  private map: Map<string, TermId> = new Map();
  sorts: SortInfo[] = [];
  private sort_by_name: Map<string, SortId> = new Map();
  /** Function symbol -> owning theory. (Rust field `fun_owner`; renamed
   * because the method of the same name exists.) */
  private fun_owner_map: Map<string, TheoryId> = new Map();
  /** Names of declared constants (to keep fresh names unique). */
  private names: Set<string> = new Set();
  private fresh_counter = 0;

  // impl Default for Terms: Terms::new()
  constructor() {
    this.add_sort("Bool", null);
  }

  static new(): Terms {
    return new Terms();
  }

  // derive(Clone)
  clone(): Terms {
    const t = new Terms();
    t.nodes = this.nodes.map((n) => n.clone());
    t.map = new Map(this.map);
    t.sorts = this.sorts.map((s) => s.clone());
    t.sort_by_name = new Map(this.sort_by_name);
    t.fun_owner_map = new Map(this.fun_owner_map);
    t.names = new Set(this.names);
    t.fresh_counter = this.fresh_counter;
    return t;
  }

  // ------------------------------------------------------------ signature

  add_sort(name: string, theory: TheoryId | null): SortId {
    const id = this.sorts.length;
    this.sorts.push(new SortInfo(name, theory));
    this.sort_by_name.set(name, id);
    return id;
  }

  sort_named(name: string): SortId | null {
    return this.sort_by_name.get(name) ?? null;
  }

  sort_name(s: SortId): string {
    return this.sorts[s].name;
  }

  sort_owner(s: SortId): TheoryId | null {
    return this.sorts[s].theory;
  }

  add_fun(name: string, theory: TheoryId): void {
    this.fun_owner_map.set(name, theory);
  }

  fun_owner(name: string): TheoryId | null {
    return this.fun_owner_map.get(name) ?? null;
  }

  is_declared(name: string): boolean {
    return this.names.has(name) || this.fun_owner_map.has(name);
  }

  // ------------------------------------------------------------ terms

  mk(op: Op, args: TermId[], sort: SortId): TermId {
    const node = new Node(op, args, sort);
    const key = node_key(node);
    const found = this.map.get(key);
    if (found !== undefined) {
      return found;
    }
    const id = this.nodes.length;
    this.nodes.push(node);
    this.map.set(key, id);
    return id;
  }

  var(name: string, sort: SortId): TermId {
    this.names.add(name);
    return this.mk({ kind: "Var", _0: name }, [], sort);
  }

  num(n: bigint, sort: SortId): TermId {
    return this.mk({ kind: "Num", _0: n }, [], sort);
  }

  app(sym: string, args: TermId[], sort: SortId): TermId {
    return this.mk({ kind: "App", _0: sym }, args, sort);
  }

  bool_const(b: boolean): TermId {
    return this.mk(b ? { kind: "True" } : { kind: "False" }, [], BOOL);
  }

  /** A fresh constant named `{prefix}{n}` that clashes with no declared name. */
  fresh_var(prefix: string, sort: SortId): TermId {
    for (;;) {
      this.fresh_counter += 1;
      const name = `${prefix}${this.fresh_counter}`;
      if (!this.is_declared(name)) {
        return this.var(name, sort);
      }
    }
  }

  node(t: TermId): Node {
    return this.nodes[t];
  }

  sort(t: TermId): SortId {
    return this.nodes[t].sort;
  }

  args(t: TermId): TermId[] {
    return this.nodes[t].args;
  }

  is_var(t: TermId): boolean {
    return this.nodes[t].op.kind === "Var";
  }

  /** Symbol of an application, if `t` is one. */
  sym(t: TermId): string | null {
    const op = this.nodes[t].op;
    return op.kind === "App" ? op._0 : null;
  }

  var_name(t: TermId): string | null {
    const op = this.nodes[t].op;
    return op.kind === "Var" ? op._0 : null;
  }

  /** Theory owning the term's top symbol. Constants belong to no theory
   * (they can be shared); numerals belong to the owner of their sort. */
  owner(t: TermId): TheoryId | null {
    const n = this.nodes[t];
    switch (n.op.kind) {
      case "Var":
      case "True":
      case "False":
        return null;
      case "Num":
        return this.sort_owner(n.sort);
      case "App":
        return this.fun_owner(n.op._0);
    }
  }

  /** All constants occurring in `t`. */
  vars_in(t: TermId, out: TermId[]): void {
    if (this.is_var(t)) {
      if (!out.includes(t)) {
        out.push(t);
      }
      return;
    }
    for (const a of this.nodes[t].args) {
      this.vars_in(a, out);
    }
  }

  // ------------------------------------------------------------ printing

  /** Human-readable infix rendering (`x + 2·y ≤ 3`, `head(l) = k1`). */
  display(t: TermId): string {
    const s = { v: "" };
    this.fmt_term(t, 0, s);
    return s.v;
  }

  /** Rendering of the negation of an atom (`x > 3` for `x ≤ 3`). */
  display_neg(t: TermId): string {
    const n = this.nodes[t];
    if (n.op.kind === "App") {
      if (n.args.length === 2) {
        let flip: string | null;
        switch (n.op._0) {
          case "=":
            flip = "≠";
            break;
          case "<=":
            flip = ">";
            break;
          case "<":
            flip = "≥";
            break;
          case ">=":
            flip = "<";
            break;
          case ">":
            flip = "≤";
            break;
          default:
            flip = null;
        }
        if (flip !== null) {
          const s = { v: "" };
          this.fmt_term(n.args[0], 3, s);
          s.v += ` ${flip} `;
          this.fmt_term(n.args[1], 3, s);
          return s.v;
        }
      }
    }
    const s = { v: "¬" };
    this.fmt_term(t, 9, s);
    return s.v;
  }

  /** SMT-LIB rendering, e.g. `(<= (+ x 1) 3)`. */
  to_smtlib(t: TermId): string {
    const n = this.nodes[t];
    const op = n.op;
    switch (op.kind) {
      case "Var":
        return op._0;
      case "Num":
        if (op._0 < 0n) return `(- ${-op._0})`;
        return op._0.toString();
      case "True":
        return "true";
      case "False":
        return "false";
      case "App": {
        const sym = op._0;
        if (n.args.length === 0) {
          return sym;
        }
        let head: string;
        if (sym.startsWith("is-") && this.fun_owner(sym) !== null) {
          head = `(_ is ${sym.slice(3)})`;
        } else {
          head = sym;
        }
        const args = n.args.map((a) => this.to_smtlib(a));
        return `(${head} ${args.join(" ")})`;
      }
    }
  }

  private fmt_term(t: TermId, parent_prec: number, out: { v: string }): void {
    const n = this.nodes[t];
    let sym: string;
    switch (n.op.kind) {
      case "Var":
        out.v += n.op._0;
        return;
      case "Num": {
        const v = n.op._0;
        if (v < 0n && parent_prec > 0) {
          out.v += `(${v})`;
        } else {
          out.v += v.toString();
        }
        return;
      }
      case "True":
        out.v += "true";
        return;
      case "False":
        out.v += "false";
        return;
      case "App":
        sym = n.op._0;
        break;
    }
    // (infix symbol, precedence)
    let infix: [string, number] | null;
    switch (sym) {
      case "=>":
        infix = ["⇒", 1];
        break;
      case "or":
        infix = ["∨", 2];
        break;
      case "xor":
        infix = ["⊕", 2];
        break;
      case "and":
        infix = ["∧", 3];
        break;
      case "=":
        infix = ["=", 4];
        break;
      case "<=":
        infix = ["≤", 4];
        break;
      case "<":
        infix = ["<", 4];
        break;
      case ">=":
        infix = ["≥", 4];
        break;
      case ">":
        infix = [">", 4];
        break;
      case "+":
        infix = ["+", 5];
        break;
      case "-":
        infix = n.args.length >= 2 ? ["-", 5] : null;
        break;
      case "*":
        infix = ["·", 6];
        break;
      default:
        infix = null;
    }
    if (infix !== null) {
      const [op, prec] = infix;
      const paren = prec <= parent_prec && parent_prec !== 0;
      if (paren) {
        out.v += "(";
      }
      n.args.forEach((a, i) => {
        if (i > 0) {
          if (op === "·") {
            out.v += "·";
          } else {
            out.v += ` ${op} `;
          }
        }
        // Right operands of non-associative operators need parentheses
        // at equal precedence; left operands do not.
        const p = i === 0 ? prec - 1 : prec;
        this.fmt_term(a, Math.max(p, 1), out);
      });
      if (paren) {
        out.v += ")";
      }
      return;
    }
    switch (sym) {
      case "not":
        out.v += "¬";
        this.fmt_term(n.args[0], 9, out);
        break;
      case "-":
        out.v += "-";
        this.fmt_term(n.args[0], 9, out);
        break;
      default:
        out.v += sym;
        if (n.args.length > 0) {
          out.v += "(";
          n.args.forEach((a, i) => {
            if (i > 0) {
              out.v += ", ";
            }
            this.fmt_term(a, 0, out);
          });
          out.v += ")";
        }
    }
  }
}

/** A value in a model. */
export type Value =
  | { kind: "Bool"; _0: boolean }
  | { kind: "Int"; _0: bigint }
  /** Constructor application. */
  | { kind: "Dt"; _0: string; _1: Value[] };

/** derive(PartialEq) for Value. */
export function Value_eq(a: Value, b: Value): boolean {
  if (a.kind === "Dt" && b.kind === "Dt") {
    return a._0 === b._0 && a._1.length === b._1.length && a._1.every((x, i) => Value_eq(x, b._1[i]));
  }
  return a.kind === b.kind && a._0 === b._0;
}

/** impl Display for Value.
 * SMT-LIB syntax: `3`, `(- 3)`, `nil`, `(cons 1 nil)`. */
export function Value_to_string(v: Value): string {
  switch (v.kind) {
    case "Bool":
      return `${v._0}`;
    case "Int":
      if (v._0 < 0n) return `(- ${-v._0})`;
      return `${v._0}`;
    case "Dt": {
      if (v._1.length === 0) return v._0;
      let s = `(${v._0}`;
      for (const a of v._1) {
        s += ` ${Value_to_string(a)}`;
      }
      return s + ")";
    }
  }
}
