import { useMemo, useState } from "react";
import { solveSmt } from "../api";
import { close, conflicts, Terms } from "./dtClosure";
import type { ExchangeLevel } from "./levels";

type Phase = "lia" | "dt" | "verdict" | "done";
const pairKey = (a: string, b: string) => [a, b].sort().join("=");

/** Nelson–Oppen by hand: which equalities between the shared constants each theory tells the other. */
export function Exchange({ level, onSolved }: { level: ExchangeLevel; onSolved: () => void }) {
  const pairs = useMemo(() => {
    const out: [string, string][] = [];
    level.shared.forEach((a, i) => level.shared.slice(i + 1).forEach((b) => out.push([a, b])));
    return out;
  }, [level]);
  const [phase, setPhase] = useState<Phase>("lia");
  const [chosen, setChosen] = useState<Set<string>>(new Set());
  const [fromLia, setFromLia] = useState<[string, string][]>([]);
  const [fromDt, setFromDt] = useState<[string, string][]>([]);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);
  const [busy, setBusy] = useState(false);

  const smt = (extra: string[]) =>
    level.liaVars.map((v) => `(declare-const ${v} Int)`).join("\n") + "\n" + [...level.lia.map((l) => l.smt), ...extra].map((a) => `(assert ${a})`).join("\n") + "\n(check-sat)";
  const eqSmt = ([a, b]: [string, string]) => `(= ${a} ${b})`;

  /** DT's closure with the equalities LIA told it */
  const dt = (extra: [string, string][]) => {
    const T = new Terms();
    const eqs = [...level.dt.eqs, ...extra].map(([a, b]) => [T.add(a), T.add(b)] as [number, number]);
    const diseqs = level.dt.diseqs.map(([a, b]) => [T.add(a), T.add(b)] as [number, number]);
    const ctors = new Set(level.ctors);
    const uf = close(T, ctors, eqs);
    const id = (v: string) => T.add(v);
    return { entails: (a: string, b: string) => uf.same(id(a), id(b)), conflicts: conflicts(T, ctors, uf, diseqs) };
  };

  const toggle = (k: string) => {
    setChosen((c) => {
      const n = new Set(c);
      if (n.has(k)) n.delete(k);
      else n.add(k);
      return n;
    });
    setMsg(null);
  };
  const compare = (truth: [string, string][], what: string): boolean => {
    const want = new Set(truth.map(([a, b]) => pairKey(a, b)));
    const extra = [...chosen].filter((k) => !want.has(k));
    const missing = [...want].filter((k) => !chosen.has(k));
    if (!extra.length && !missing.length) return true;
    setMsg({
      ok: false,
      text: extra.length ? `${extra[0].replace("=", " = ")} does not follow from ${what}: there is a model of it where they differ.` : `${missing[0].replace("=", " = ")} is forced too (by ${what}).`,
    });
    return false;
  };

  const checkLia = async () => {
    setBusy(true);
    try {
      const truth: [string, string][] = [];
      for (const p of pairs) if ((await solveSmt(smt([`(not ${eqSmt(p)})`]))).status === "UNSAT") truth.push(p);
      if (!compare(truth, "the LIA literals")) return;
      setFromLia(truth);
      setChosen(new Set());
      setMsg({ ok: true, text: truth.length ? `Right: LIA tells DT ${truth.map(([a, b]) => `${a} = ${b}`).join(", ")}.` : "Right: LIA forces no equality between the shared constants, so it tells DT nothing." });
      setPhase("dt");
    } catch (e) {
      setMsg({ ok: false, text: (e as Error).message });
    } finally {
      setBusy(false);
    }
  };

  const checkDt = () => {
    const d = dt(fromLia);
    const truth = pairs.filter(([a, b]) => d.entails(a, b));
    if (!compare(truth, "DT (with what LIA told it)")) return;
    const fresh = truth.filter(([a, b]) => !fromLia.some((p) => pairKey(...p) === pairKey(a, b)));
    setFromDt(fresh);
    setMsg({ ok: true, text: fresh.length ? `Right: DT tells LIA ${fresh.map(([a, b]) => `${a} = ${b}`).join(", ")}.` : "Right: DT derives nothing new about the shared constants." });
    setPhase("verdict");
  };

  const verdict = async (say: "dt" | "lia" | "none") => {
    setBusy(true);
    try {
      const dtConf = dt(fromLia).conflicts;
      const liaUnsat = (await solveSmt(smt(fromDt.map(eqSmt)))).status === "UNSAT";
      const truth = dtConf.length ? "dt" : liaUnsat ? "lia" : "none";
      if (say === truth) {
        setMsg({
          ok: true,
          text:
            truth === "dt"
              ? `Right: DT finds the conflict (${dtConf[0].text}).`
              : truth === "lia"
                ? `Right: with ${fromDt.map(([a, b]) => `${a} = ${b}`).join(", ")} the LIA literals have no solution.`
                : "Right: both theories are satisfied and agree on which shared constants are equal, so the combination is satisfiable.",
        });
        setPhase("done");
        onSolved();
      } else setMsg({ ok: false, text: "Not quite: check each theory with the equalities it was told." });
    } catch (e) {
      setMsg({ ok: false, text: (e as Error).message });
    } finally {
      setBusy(false);
    }
  };

  const pairButtons = (
    <div className="lemma-lits">
      {pairs.map(([a, b]) => {
        const k = pairKey(a, b);
        return (
          <button key={k} className={`chip ${chosen.has(k) ? "t picked" : "u"}`} onClick={() => toggle(k)}>
            {a} = {b}
          </button>
        );
      })}
    </div>
  );

  return (
    <div className="edu-body">
      <div className="exchange">
        <div>
          <h4>LIA's literals</h4>
          <div className="lemma-lits">{level.lia.map((l, i) => <span key={i} className="chip t static">{l.label}</span>)}</div>
        </div>
        <div>
          <h4>DT's literals</h4>
          <div className="lemma-lits">
            {level.dt.eqs.map(([a, b], i) => <span key={`e${i}`} className="chip t static">{a} = {b}</span>)}
            {level.dt.diseqs.map(([a, b], i) => <span key={`d${i}`} className="chip f static">{a} ≠ {b}</span>)}
          </div>
        </div>
      </div>
      <p className="note">Shared constants: {level.shared.join(", ")}. {fromLia.length > 0 && <>LIA told DT: {fromLia.map(([a, b]) => `${a} = ${b}`).join(", ")}. </>}{phase !== "lia" && phase !== "dt" && fromDt.length > 0 && <>DT told LIA: {fromDt.map(([a, b]) => `${a} = ${b}`).join(", ")}.</>}</p>
      {phase === "lia" && (
        <>
          <h4>1. Which equalities between shared constants does LIA force? (pick none if there are none)</h4>
          {pairButtons}
          <button className="primary" onClick={checkLia} disabled={busy}>{busy ? "Checking…" : "Check"}</button>
        </>
      )}
      {phase === "dt" && (
        <>
          <h4>2. With those, which equalities between shared constants hold in DT?</h4>
          {pairButtons}
          <button className="primary" onClick={checkDt}>Check</button>
        </>
      )}
      {phase === "verdict" && (
        <div className="edu-question column">
          <span>3. After the exchange, what happens?</span>
          <div className="row">
            <button onClick={() => verdict("dt")} disabled={busy}>DT finds a conflict</button>
            <button onClick={() => verdict("lia")} disabled={busy}>LIA finds a conflict</button>
            <button onClick={() => verdict("none")} disabled={busy}>No conflict: sat</button>
          </div>
        </div>
      )}
      <div className="row">
        <button className="ghost" onClick={() => { setPhase("lia"); setChosen(new Set()); setFromLia([]); setFromDt([]); setMsg(null); }}>Start again</button>
      </div>
      {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
    </div>
  );
}
