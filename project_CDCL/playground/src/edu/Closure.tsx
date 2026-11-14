import { useMemo, useState } from "react";
import { classes, close, conflicts, oneStep, Terms, UF, type ConflictKind } from "./dtClosure";
import type { ClosureLevel } from "./levels";

const PALETTE = ["#fde2a7", "#cfe8ff", "#d7f5d0", "#f6d1f0", "#ffd9c7", "#e2dcff", "#d2f3f0"];
const WHY: Record<string, string> = {
  given: "it is given (or follows from the given equalities by transitivity)",
  congruence: "congruence: the same constructor applied to equal arguments",
  injectivity: "injectivity: equal constructor terms have equal arguments",
};
const KINDS: { kind: ConflictKind; label: string }[] = [
  { kind: "none", label: "No conflict" },
  { kind: "clash", label: "Two different constructors are equal" },
  { kind: "diseq", label: "A disequality is broken" },
  { kind: "cycle", label: "A term equals one of its own subterms" },
];

/** Build the equivalence classes DT derives, one justified merge at a time. */
export function Closure({ level, onSolved }: { level: ClosureLevel; onSolved: () => void }) {
  const P = useMemo(() => {
    const T = new Terms();
    const eqs = level.eqs.map(([a, b]) => [T.add(a), T.add(b)] as [number, number]);
    const diseqs = level.diseqs.map(([a, b]) => [T.add(a), T.add(b)] as [number, number]);
    const ctors = new Set(level.ctors);
    const final = close(T, ctors, eqs);
    return { T, eqs, diseqs, ctors, final, found: conflicts(T, ctors, final, diseqs) };
  }, [level]);
  const { T, eqs, ctors, final, found } = P;
  const [uf, setUf] = useState(() => new UF(T.list.length));
  const [first, setFirst] = useState<number | null>(null);
  const [log, setLog] = useState<string[]>([]);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);
  const [solved, setSolved] = useState(false);

  const mine = classes(T, uf);
  // your classes only ever merge what DT derives, so they are complete when
  // there are as many as DT has
  const roots = (u: UF) => new Set(T.list.map((_, i) => u.find(i))).size;
  const complete = roots(uf) === roots(final);
  const color = (i: number) => {
    const k = mine.findIndex((c) => c.includes(i));
    return k < 0 ? undefined : PALETTE[k % PALETTE.length];
  };

  const click = (i: number) => {
    if (complete) return;
    if (first === null || first === i) {
      setFirst(first === i ? null : i);
      setMsg(null);
      return;
    }
    const a = first;
    setFirst(null);
    if (uf.same(a, i)) {
      setMsg({ ok: false, text: `${T.list[a].text} and ${T.list[i].text} are already in the same class.` });
      return;
    }
    if (!final.same(a, i)) {
      setMsg({ ok: false, text: `Nothing forces ${T.list[a].text} = ${T.list[i].text}: DT never derives it.` });
      return;
    }
    const why = oneStep(T, ctors, eqs, uf, a, i);
    if (!why) {
      setMsg({ ok: false, text: `${T.list[a].text} = ${T.list[i].text} does hold in the end, but it does not follow in one step from your classes yet. Derive something else first.` });
      return;
    }
    const next = uf.copy();
    next.union(a, i);
    setUf(next);
    setLog((l) => [...l, `${T.list[a].text} = ${T.list[i].text}: ${WHY[why]}`]);
    setMsg({ ok: true, text: `${T.list[a].text} = ${T.list[i].text} by ${why}.` });
  };

  const answer = (k: ConflictKind) => {
    const kinds = found.map((f) => f.kind);
    const right = k === "none" ? kinds.length === 0 : kinds.includes(k);
    if (right) {
      setMsg({ ok: true, text: k === "none" ? "Right: the classes are consistent, so DT accepts these literals." : `Right: ${found.find((f) => f.kind === k)!.text}. DT reports a conflict, and the literals used become a lemma.` });
      setSolved(true);
      onSolved();
    } else setMsg({ ok: false, text: k === "none" ? "Look again at the classes: something in them cannot hold." : "Not this one. Look at each class: which constructors does it contain, and is any ≠ inside one class?" });
  };

  return (
    <div className="edu-body">
      <h4>The literals DT receives</h4>
      <div className="lemma-lits">
        {level.eqs.map(([a, b], i) => <span key={`e${i}`} className="chip t static">{T.list[T.add(a)].text} = {T.list[T.add(b)].text}</span>)}
        {level.diseqs.map(([a, b], i) => <span key={`d${i}`} className="chip f static">{T.list[T.add(a)].text} ≠ {T.list[T.add(b)].text}</span>)}
      </div>
      <p className="note">Constructors: {level.ctors.join(", ")}. Everything else is a constant.</p>
      <h4>The terms {complete ? "(every class is complete)" : "— click two terms that must be equal"}</h4>
      <div className="lemma-lits">
        {T.list.map((t, i) => (
          <button key={i} className={`chip u dt-term ${first === i ? "first" : ""}`} style={{ background: color(i) }} onClick={() => click(i)}>
            {t.text}
          </button>
        ))}
      </div>
      {complete && !solved && (
        <div className="edu-question column">
          <span>Every equality DT can derive is there. Is there a conflict?</span>
          <div className="row">
            {KINDS.map((k) => (
              <button key={k.kind} onClick={() => answer(k.kind)}>{k.label}</button>
            ))}
          </div>
        </div>
      )}
      <div className="row">
        <button className="ghost" onClick={() => { setUf(new UF(T.list.length)); setLog([]); setMsg(null); setFirst(null); setSolved(false); }}>Start again</button>
      </div>
      {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
      {log.length > 0 && <ol className="edu-solution">{log.map((l, i) => <li key={i}>{l}</li>)}</ol>}
    </div>
  );
}
