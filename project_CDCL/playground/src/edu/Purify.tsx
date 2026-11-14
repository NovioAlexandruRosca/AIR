import { useMemo, useState } from "react";
import type { PurifyLevel } from "./levels";

// ---------------------------------------------------------------- terms
/** A term or literal: `f` is an operator (+ − · = ≤ …), a number, a name or a function symbol. */
interface Node {
  f: string;
  args: Node[];
  path: string;
}
type Theory = "LIA" | "DT" | "var";
interface Raw {
  f: string;
  args: Raw[];
}

const REL = ["=", "≠", "≤", "≥", "<", ">"];

function parse(src: string, at: string): Node {
  const toks = src.match(/\d+|[A-Za-z_][\w']*|<=|>=|!=|[≤≥≠<>=+\-*·(),]/g) ?? [];
  const norm: Record<string, string> = { "<=": "≤", ">=": "≥", "!=": "≠", "*": "·" };
  const t = toks.map((x) => norm[x] ?? x);
  let i = 0;
  const peek = () => t[i];
  const eat = (x?: string) => {
    if (x !== undefined && t[i] !== x) throw new Error(`expected '${x}' in '${src}'`);
    return t[i++];
  };
  const atom = (): Raw => {
    const x = eat();
    if (x === "(") {
      const e = sum();
      eat(")");
      return e;
    }
    if (/^\d+$/.test(x) && peek() === "·") {
      eat("·");
      return { f: "·", args: [{ f: x, args: [] }, atom()] };
    }
    if (peek() === "(" && /^[A-Za-z_]/.test(x)) {
      eat("(");
      const args = [sum()];
      while (peek() === ",") (eat(","), args.push(sum()));
      eat(")");
      return { f: x, args };
    }
    return { f: x, args: [] };
  };
  const sum = (): Raw => {
    let e = atom();
    while (peek() === "+" || peek() === "-") {
      const op = eat() === "+" ? "+" : "−";
      e = { f: op, args: [e, atom()] };
    }
    return e;
  };
  const lhs = sum();
  const rel = eat();
  if (!REL.includes(rel)) throw new Error(`no relation in '${src}'`);
  const tree = { f: rel, args: [lhs, sum()] };
  const withPath = (n: Raw, p: string): Node => ({ f: n.f, path: p, args: n.args.map((a, k) => withPath(a, `${p}.${k}`)) });
  return withPath(tree, at);
}

const theoryOf = (n: Node, dt: Set<string>): Theory =>
  ["+", "−", "·"].includes(n.f) || /^\d+$/.test(n.f) ? "LIA" : n.args.length || dt.has(n.f) ? "DT" : "var";

/** The literal's theory: comparisons are LIA; an equality goes with its non-variable sides. */
function litTheory(lit: Node, dt: Set<string>): Theory {
  if (lit.f !== "=" && lit.f !== "≠") return "LIA";
  const [a, b] = lit.args.map((s) => theoryOf(s, dt));
  return a !== "var" ? a : b;
}

/** The alien subterms: a term of one theory directly under a symbol of the other. */
function aliens(lit: Node, dt: Set<string>): Set<string> {
  const out = new Set<string>();
  const walk = (n: Node, parent: Theory) => {
    const th = theoryOf(n, dt);
    if (th !== "var" && parent !== "var" && th !== parent) out.add(n.path);
    n.args.forEach((a) => walk(a, th === "var" ? parent : th));
  };
  const th = litTheory(lit, dt);
  lit.args.forEach((a) => walk(a, th));
  return out;
}

const text = (n: Node, sub: (n: Node) => string | null = () => null, top = true): string => {
  const s = sub(n);
  if (s !== null) return s;
  if (REL.includes(n.f)) return `${text(n.args[0], sub, true)} ${n.f} ${text(n.args[1], sub, true)}`;
  if (n.f === "+" || n.f === "−") {
    const e = `${text(n.args[0], sub, false)} ${n.f} ${text(n.args[1], sub, false)}`;
    return top ? e : `(${e})`;
  }
  if (n.f === "·") return `${text(n.args[0], sub, false)}·${text(n.args[1], sub, false)}`;
  return n.args.length ? `${n.f}(${n.args.map((a) => text(a, sub, true)).join(", ")})` : n.f;
};
const names = (n: Node, out = new Set<string>(), dt?: Set<string>): Set<string> => {
  if (!n.args.length && /^[A-Za-z_]/.test(n.f) && !dt?.has(n.f)) out.add(n.f);
  n.args.forEach((a) => names(a, out, dt));
  return out;
};

type Phase = "aliens" | "shared" | "done";

/** Purify mixed literals: mark the alien subterms, then find the shared constants. */
export function Purify({ level, onSolved }: { level: PurifyLevel; onSolved: () => void }) {
  const P = useMemo(() => {
    const dt = new Set(level.dtSymbols);
    const lits = level.literals.map((l, i) => parse(l, String(i)));
    const truth = new Set(lits.flatMap((l) => [...aliens(l, dt)]));
    const all = new Map<string, Node>();
    const index = (n: Node) => (all.set(n.path, n), n.args.forEach(index));
    lits.forEach(index);
    // fresh constants, innermost first: v1, v2, …
    const order = [...truth].sort((a, b) => b.split(".").length - a.split(".").length || a.localeCompare(b));
    const fresh = new Map(order.map((p, k) => [p, `v${k + 1}`]));
    const sub = (self?: string) => (n: Node) => (n.path !== self && fresh.has(n.path) ? fresh.get(n.path)! : null);
    const lia: string[] = [];
    const dtPart: string[] = [];
    const used = { LIA: new Set<string>(), DT: new Set<string>() };
    const put = (th: Theory, s: string, n: Node) => {
      (th === "DT" ? dtPart : lia).push(s);
      const ns = names(n, new Set(), dt);
      // a fresh constant stands for its subterm: count it, not what is inside
      const add = (m: Node) => {
        if (fresh.has(m.path) && m !== n) used[th === "DT" ? "DT" : "LIA"].add(fresh.get(m.path)!);
        else if (!m.args.length && ns.has(m.f)) used[th === "DT" ? "DT" : "LIA"].add(m.f);
        else m.args.forEach(add);
      };
      add(n);
    };
    lits.forEach((l) => put(litTheory(l, dt), text(l, sub()), l));
    for (const p of order) {
      const n = all.get(p)!;
      const th = theoryOf(n, dt);
      put(th, `${fresh.get(p)} = ${text(n, sub(p))}`, n);
      used[th === "DT" ? "DT" : "LIA"].add(fresh.get(p)!);
    }
    const shared = [...used.LIA].filter((v) => used.DT.has(v)).sort();
    const candidates = [...new Set([...used.LIA, ...used.DT])].sort();
    return { dt, lits, truth, all, lia, dtPart, shared, candidates };
  }, [level]);

  const [phase, setPhase] = useState<Phase>("aliens");
  const [marked, setMarked] = useState<Set<string>>(new Set());
  const [picked, setPicked] = useState<Set<string>>(new Set());
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);

  const toggle = <T,>(set: (f: (s: Set<T>) => Set<T>) => void, x: T) => {
    set((s) => {
      const n = new Set(s);
      if (n.has(x)) n.delete(x);
      else n.add(x);
      return n;
    });
    setMsg(null);
  };

  const checkAliens = () => {
    const extra = [...marked].filter((p) => !P.truth.has(p));
    const missing = [...P.truth].filter((p) => !marked.has(p));
    if (!extra.length && !missing.length) {
      setMsg({ ok: true, text: `Right: ${P.truth.size === 1 ? "that subterm is replaced by a fresh constant, which gets" : "those subterms are replaced by fresh constants, and each one gets"} a definition in the theory of its subterm. Now: which constants are shared?` });
      setPhase("shared");
      return;
    }
    if (extra.length) {
      const n = P.all.get(extra[0])!;
      const th = theoryOf(n, P.dt);
      setMsg({
        ok: false,
        text:
          th === "var"
            ? `${text(n)} is a constant: it can appear in both parts as it is, nothing to replace.`
            : `${text(n)} is a ${th} term, and so is what it sits in: it stays where it is.`,
      });
    } else setMsg({ ok: false, text: `Something is missing: look for ${missing.some((p) => theoryOf(P.all.get(p)!, P.dt) === "DT") ? "a DT term (a constructor or selector) used inside arithmetic" : "an arithmetic term inside a DT term"}${missing.some((p) => p.split(".").length > 3) ? ", also inside other aliens" : ""}.` });
  };

  const checkShared = () => {
    const want = new Set(P.shared);
    const extra = [...picked].filter((v) => !want.has(v));
    const missing = P.shared.filter((v) => !picked.has(v));
    if (!extra.length && !missing.length) {
      setMsg({ ok: true, text: `Right: ${P.shared.length === 1 ? `${P.shared[0]} is the only constant` : `${P.shared.join(", ")} are the only constants`} both parts mention. Nelson–Oppen only exchanges equalities between these.` });
      setPhase("done");
      onSolved();
    } else
      setMsg({
        ok: false,
        text: extra.length ? `${extra[0]} appears only in the ${P.lia.some((l) => new RegExp(`\\b${extra[0]}\\b`).test(l)) ? "LIA" : "DT"} part.` : `${missing[0]} appears in both parts.`,
      });
  };

  // a literal as nested clickable subterms
  const view = (n: Node, top = true): React.ReactNode => {
    if (REL.includes(n.f))
      return (
        <span className="pur-lit">
          {view(n.args[0], true)} <span className="conn">{n.f}</span> {view(n.args[1], true)}
        </span>
      );
    const inner =
      n.f === "+" || n.f === "−" ? (
        <>
          {!top && "("}
          {view(n.args[0], false)} {n.f} {view(n.args[1], false)}
          {!top && ")"}
        </>
      ) : n.f === "·" ? (
        <>
          {view(n.args[0], false)}·{view(n.args[1], false)}
        </>
      ) : n.args.length ? (
        <>
          {n.f}(
          {n.args.map((a, k) => (
            <span key={k}>
              {k > 0 && ", "}
              {view(a, true)}
            </span>
          ))}
          )
        </>
      ) : (
        n.f
      );
    const on = marked.has(n.path);
    const res = phase !== "aliens" && P.truth.has(n.path);
    return (
      <span
        className={`pur-term ${on || res ? "alien" : ""}`}
        onClick={(e) => {
          e.stopPropagation();
          if (phase === "aliens") toggle(setMarked, n.path);
        }}
      >
        {inner}
      </span>
    );
  };

  return (
    <div className="edu-body">
      <h4>The literals</h4>
      <div className="pur-lits">
        {P.lits.map((l, i) => (
          <div key={i} className="mono">
            {view(l)}
          </div>
        ))}
      </div>
      <p className="note">DT symbols: {level.dtSymbols.join(", ")}. Arithmetic (+, −, numbers, ≤ …) is LIA.</p>
      {phase === "aliens" && (
        <>
          <p className="note">Click every <b>alien</b> subterm (click again to unmark). Each one gets replaced by a fresh constant.</p>
          <div className="row">
            <button className="primary" onClick={checkAliens}>Check</button>
            <button className="ghost" onClick={() => { setMarked(new Set()); setMsg(null); }}>Start again</button>
          </div>
        </>
      )}
      {phase !== "aliens" && (
        <div className="exchange">
          <div>
            <h4>LIA part</h4>
            {P.lia.map((l, i) => <div key={i} className="mono">{l}</div>)}
          </div>
          <div>
            <h4>DT part</h4>
            {P.dtPart.map((l, i) => <div key={i} className="mono">{l}</div>)}
          </div>
        </div>
      )}
      {phase !== "aliens" && (
        <>
          <h4>Which constants are shared?</h4>
          <div className="lemma-lits">
            {P.candidates.map((v) => (
              <button key={v} className={`chip ${picked.has(v) || (phase === "done" && P.shared.includes(v)) ? "t picked" : "u"}`} onClick={() => phase === "shared" && toggle(setPicked, v)}>
                {v}
              </button>
            ))}
          </div>
          {phase === "shared" && (
            <div className="row">
              <button className="primary" onClick={checkShared}>Check</button>
            </div>
          )}
        </>
      )}
      {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
    </div>
  );
}
