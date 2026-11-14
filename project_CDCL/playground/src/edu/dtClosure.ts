// A small congruence closure for the DT levels: terms over constructors and
// constants, closed under congruence and injectivity, with the three ways
// DT finds a conflict (two constructors, a disequality, a cycle).

export interface Term {
  f: string;
  args: number[];
  text: string;
}

export class Terms {
  list: Term[] = [];
  private ids = new Map<string, number>();

  /** Parse `f(t1, …, tn)` or a name, adding every subterm; returns its id. */
  add(src: string): number {
    let i = 0;
    const ws = () => {
      while (src[i] === " ") i++;
    };
    const term = (): number => {
      ws();
      let name = "";
      while (i < src.length && /[\w']/.test(src[i])) name += src[i++];
      if (!name) throw new Error(`bad term '${src}'`);
      ws();
      const args: number[] = [];
      if (src[i] === "(") {
        i++;
        for (;;) {
          args.push(term());
          ws();
          if (src[i] === ",") i++;
          else if (src[i] === ")") {
            i++;
            break;
          } else throw new Error(`bad term '${src}'`);
        }
      }
      const text = args.length ? `${name}(${args.map((a) => this.list[a].text).join(", ")})` : name;
      const old = this.ids.get(text);
      if (old !== undefined) return old;
      this.list.push({ f: name, args, text });
      this.ids.set(text, this.list.length - 1);
      return this.list.length - 1;
    };
    return term();
  }
}

export class UF {
  p: number[];
  constructor(n: number) {
    this.p = Array.from({ length: n }, (_, i) => i);
  }
  find(a: number): number {
    while (this.p[a] !== a) a = this.p[a] = this.p[this.p[a]];
    return a;
  }
  union(a: number, b: number): boolean {
    const x = this.find(a);
    const y = this.find(b);
    if (x === y) return false;
    this.p[Math.max(x, y)] = Math.min(x, y);
    return true;
  }
  same(a: number, b: number) {
    return this.find(a) === this.find(b);
  }
  copy() {
    const u = new UF(0);
    u.p = [...this.p];
    return u;
  }
}

export type Why = "given" | "congruence" | "injectivity";

/** Does merging a and b follow in one step from the classes uf has? */
export function oneStep(T: Terms, ctors: Set<string>, eqs: [number, number][], uf: UF, a: number, b: number): Why | null {
  const A = uf.find(a);
  const B = uf.find(b);
  if (A === B) return null;
  if (eqs.some(([s, t]) => (uf.find(s) === A && uf.find(t) === B) || (uf.find(s) === B && uf.find(t) === A))) return "given";
  const n = T.list.length;
  const inA = (i: number) => uf.find(i) === A;
  const inB = (i: number) => uf.find(i) === B;
  for (let s = 0; s < n; s++) {
    if (!inA(s)) continue;
    for (let t = 0; t < n; t++) {
      if (!inB(t)) continue;
      const S = T.list[s];
      const U = T.list[t];
      if (S.f === U.f && S.args.length === U.args.length && S.args.length > 0 && S.args.every((x, i) => uf.same(x, U.args[i]))) return "congruence";
    }
  }
  for (let s = 0; s < n; s++)
    for (let t = 0; t < n; t++) {
      const S = T.list[s];
      const U = T.list[t];
      if (s === t || S.f !== U.f || !ctors.has(S.f) || S.args.length !== U.args.length || !uf.same(s, t)) continue;
      if (S.args.some((x, i) => (inA(x) && inB(U.args[i])) || (inB(x) && inA(U.args[i])))) return "injectivity";
    }
  return null;
}

/** Close the given equalities under congruence and injectivity. */
export function close(T: Terms, ctors: Set<string>, eqs: [number, number][]): UF {
  const uf = new UF(T.list.length);
  for (const [a, b] of eqs) uf.union(a, b);
  let changed = true;
  while (changed) {
    changed = false;
    const n = T.list.length;
    for (let s = 0; s < n; s++)
      for (let t = s + 1; t < n; t++) {
        const S = T.list[s];
        const U = T.list[t];
        if (S.f !== U.f || S.args.length !== U.args.length || !S.args.length) continue;
        if (!uf.same(s, t) && S.args.every((x, i) => uf.same(x, U.args[i]))) changed = uf.union(s, t) || changed;
        if (uf.same(s, t) && ctors.has(S.f)) S.args.forEach((x, i) => (changed = uf.union(x, U.args[i]) || changed));
      }
  }
  return uf;
}

export type ConflictKind = "none" | "clash" | "diseq" | "cycle";

/** The conflicts of a closed set of classes. */
export function conflicts(T: Terms, ctors: Set<string>, uf: UF, diseqs: [number, number][]): { kind: ConflictKind; text: string }[] {
  const out: { kind: ConflictKind; text: string }[] = [];
  const head = new Map<number, number>();
  T.list.forEach((t, i) => {
    if (!ctors.has(t.f)) return;
    const r = uf.find(i);
    const h = head.get(r);
    if (h === undefined) head.set(r, i);
    else if (T.list[h].f !== t.f) out.push({ kind: "clash", text: `${T.list[h].text} = ${t.text}: two different constructors` });
  });
  for (const [a, b] of diseqs) if (uf.same(a, b)) out.push({ kind: "diseq", text: `${T.list[a].text} ≠ ${T.list[b].text}, but they are equal` });
  // a cycle: a class reaches itself through constructor arguments
  const edges = new Map<number, Set<number>>();
  T.list.forEach((t, i) => {
    if (!ctors.has(t.f)) return;
    const r = uf.find(i);
    for (const a of t.args) {
      if (!edges.has(r)) edges.set(r, new Set());
      edges.get(r)!.add(uf.find(a));
    }
  });
  const state = new Map<number, 1 | 2>();
  let cyc: number | null = null;
  const dfs = (v: number) => {
    state.set(v, 1);
    for (const w of edges.get(v) ?? []) {
      if (cyc !== null) return;
      if (state.get(w) === 1) cyc = w;
      else if (!state.has(w)) dfs(w);
    }
    state.set(v, 2);
  };
  for (const v of edges.keys()) if (!state.has(v) && cyc === null) dfs(v);
  if (cyc !== null) {
    const members = T.list.map((_, i) => i).filter((i) => uf.find(i) === cyc);
    out.push({ kind: "cycle", text: `${members.map((i) => T.list[i].text).join(" = ")} contains itself as a proper subterm` });
  }
  return out;
}

/** The classes of uf (with at least two members), as lists of term ids. */
export function classes(T: Terms, uf: UF): number[][] {
  const m = new Map<number, number[]>();
  T.list.forEach((_, i) => {
    const r = uf.find(i);
    m.set(r, [...(m.get(r) ?? []), i]);
  });
  return [...m.values()].filter((c) => c.length > 1);
}
