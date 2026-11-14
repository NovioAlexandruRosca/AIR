import { useState } from "react";
import { solveSmt } from "../api";
import type { LemmaLevel } from "./levels";

const negate = (l: string) => (l.startsWith("¬") ? l.slice(1).replace(/^\((.*)\)$/, "$1") : /\s/.test(l) ? `¬(${l})` : `¬${l}`);

/** Pick the literals LIA can blame; their negations are the lemma. The solver checks the choice. */
export function Lemma({ level, onSolved }: { level: LemmaLevel; onSolved: () => void }) {
  const [chosen, setChosen] = useState<number[]>([]);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);
  const [busy, setBusy] = useState(false);

  const smt = (ids: number[]) =>
    level.vars.map((v) => `(declare-const ${v} Int)`).join("\n") + "\n" + ids.map((i) => `(assert ${level.literals[i].smt})`).join("\n") + "\n(check-sat)";
  const toggle = (i: number) => {
    setChosen((c) => (c.includes(i) ? c.filter((x) => x !== i) : [...c, i].sort((a, b) => a - b)));
    setMsg(null);
  };
  const lemma = (ids: number[]) => "(" + ids.map((i) => negate(level.literals[i].label)).join(" ∨ ") + ")";

  const check = async () => {
    if (!chosen.length) {
      setMsg({ ok: false, text: "Pick the literals that cannot hold together." });
      return;
    }
    setBusy(true);
    try {
      const r = await solveSmt(smt(chosen));
      if (r.status !== "UNSAT") {
        const at = r.model.map((m) => `${m.name} = ${m.value}`).join(", ");
        setMsg({ ok: false, text: `These can all hold together${at ? `, e.g. ${at}` : ""}: they are not a conflict yet. Add the literal that breaks it.` });
        return;
      }
      // smallest? try leaving each one out
      for (const i of chosen) {
        const rest = chosen.filter((x) => x !== i);
        if (rest.length && (await solveSmt(smt(rest))).status === "UNSAT") {
          setMsg({ ok: false, text: `These conflict, but ${level.literals[i].label} is not needed: the others conflict without it. A smaller lemma blocks more of the search.` });
          return;
        }
      }
      setMsg({
        ok: true,
        text: `Right! LIA blames exactly these, so the SAT solver adds the theory lemma ${lemma(chosen)}: at least one of them must be false. Then CDCL analyses the conflict as usual.`,
      });
      onSolved();
    } catch (e) {
      setMsg({ ok: false, text: (e as Error).message });
    } finally {
      setBusy(false);
    }
  };

  return (
    <div className="edu-body">
      <h4>The context LIA receives (it answers "unsat")</h4>
      <div className="lemma-lits">
        {level.literals.map((l, i) => (
          <button key={i} className={`chip ${chosen.includes(i) ? "f picked" : "u"}`} onClick={() => toggle(i)}>
            {l.label}
          </button>
        ))}
      </div>
      <p className="note">Click the literals that conflict. The lemma is the clause of their negations.</p>
      <div className="lemma-out">
        Your lemma: <span className="mono">{chosen.length ? lemma(chosen) : "—"}</span>
      </div>
      <div className="row">
        <button className="primary" onClick={check} disabled={busy}>{busy ? "Checking…" : "Check"}</button>
        <button className="ghost" onClick={() => { setChosen([]); setMsg(null); }}>Start again</button>
      </div>
      {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
    </div>
  );
}
