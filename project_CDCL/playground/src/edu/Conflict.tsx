import { useEffect, useMemo, useState } from "react";
import { Background, ReactFlow } from "@xyflow/react";
import { litText } from "../model";
import { graphEdges, graphNodes, KAPPA, runLevel, showAssertion, truthEdges, type Run } from "./Graph";
import type { ConflictLevel } from "./levels";

type Phase = "uip" | "clause" | "level" | "done";

/** From the implication graph of a conflict: the First UIP, the learnt clause, the backjump level. */
export function Conflict({ level, onSolved }: { level: ConflictLevel; onSolved: () => void }) {
  const [run, setRun] = useState<Run | null>(null);
  const [err, setErr] = useState<string | null>(null);
  const [phase, setPhase] = useState<Phase>("uip");
  const [chosen, setChosen] = useState<string[]>([]);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);

  useEffect(() => {
    setRun(null);
    setErr(null);
    runLevel(level).then(
      (r) => (r.resp.replay.learned ? setRun(r) : setErr("this level does not end in a conflict CDCL can analyse")),
      (e) => setErr((e as Error).message),
    );
  }, [level]);

  const truth = useMemo(() => (run ? [...truthEdges(run)] : []), [run]);
  if (err) return <div className="error">{err}</div>;
  if (!run) return <p className="note">Running the solver…</p>;

  const { L, nodes } = run;
  const learned = run.resp.replay.learned!;
  const levelOf = new Map(nodes.map((n) => [String(n.lit), n.level]));
  const confLevel = Math.max(...nodes.map((n) => n.level));
  // the learnt clause: the negation of each node on the cut
  const cut = learned.map((l) => String(-l));
  const uip = cut.find((id) => levelOf.get(id) === confLevel)!;
  const back = Math.max(0, ...cut.filter((id) => id !== uip).map((id) => levelOf.get(id) ?? 0));
  const text = (id: string) => (id === KAPPA ? KAPPA : litText(L, Number(id)));
  const clauseText = (ids: string[]) => (ids.length ? `(${ids.map((id) => litText(L, -Number(id))).join(" ∨ ")})` : "—");
  const decision = nodes.find((n) => n.level === confLevel && n.decided);

  // does every path from the conflict level's decision to κ pass through id?
  const dominates = (id: string) => {
    if (!decision) return false;
    const out = new Map<string, string[]>();
    for (const e of truth) {
      const [a, b] = e.split("->");
      out.set(a, [...(out.get(a) ?? []), b]);
    }
    const seen = new Set<string>([id]);
    const todo = [String(decision.lit)];
    if (todo[0] === id) return true;
    while (todo.length) {
      const v = todo.pop()!;
      if (v === KAPPA) return false;
      for (const w of out.get(v) ?? []) if (!seen.has(w)) (seen.add(w), todo.push(w));
    }
    return true;
  };

  const click = (id: string) => {
    if (id === KAPPA) return;
    setMsg(null);
    if (phase === "uip") {
      const lv = levelOf.get(id) ?? 0;
      if (id === uip) {
        setMsg({ ok: true, text: `Right: every path from the decision ${decision ? text(String(decision.lit)) : ""} to κ goes through ${text(id)}, and it is the closest such literal to κ. Now the learnt clause.` });
        setChosen([id]);
        setPhase("clause");
      } else if (lv !== confLevel)
        setMsg({ ok: false, text: `${text(id)} is at level ${lv}. The UIP is a literal of the conflict level, ${confLevel}.` });
      else if (!dominates(id))
        setMsg({ ok: false, text: `Not every path from the decision to κ goes through ${text(id)}: there is a way around it.` });
      else setMsg({ ok: false, text: `${text(id)} is a UIP (every path goes through it), but not the first one: there is another one closer to κ.` });
      return;
    }
    if (phase === "clause") setChosen((c) => (c.includes(id) ? c.filter((x) => x !== id) : [...c, id]));
  };

  const checkClause = () => {
    const extra = chosen.filter((id) => !cut.includes(id));
    const missing = cut.filter((id) => !chosen.includes(id));
    if (!extra.length && !missing.length) {
      setMsg({ ok: true, text: `Right: the learnt clause is ${clauseText(cut)}. It has exactly one literal of level ${confLevel}. Where does CDCL jump back to?` });
      setPhase("level");
      return;
    }
    const lv0 = extra.filter((id) => (levelOf.get(id) ?? 0) === 0);
    const sameLevel = extra.filter((id) => levelOf.get(id) === confLevel);
    setMsg({
      ok: false,
      text: lv0.length
        ? `${lv0.map(text).join(", ")} ${lv0.length === 1 ? "is" : "are"} true at level 0 (a fact): CDCL leaves such literals out, they can never be undone.`
        : sameLevel.length
          ? `${sameLevel.map(text).join(", ")} ${sameLevel.length === 1 ? "is" : "are"} at the conflict level but not the UIP: the cut keeps only the UIP from that level; what comes after it is on the conflict side.`
          : extra.length
            ? `${extra.map(text).join(", ")} ${extra.length === 1 ? "does" : "do"} not point into the conflict side of the cut.`
            : `Something is missing: which literals from earlier levels have an edge into the part between the UIP and κ?`,
    });
  };

  const pickLevel = (k: number) => {
    if (k === back) {
      setMsg({
        ok: true,
        text: `Right! After undoing every level above ${k}, ${clauseText(cut)} has only one open literal, ${litText(L, -Number(uip))}: it is unit, so CDCL propagates it right away at level ${k}. ${k === confLevel - 1 ? "" : `Levels ${k + 1}…${confLevel - 1} are skipped: that is the backjump.`}`,
      });
      setPhase("done");
      onSolved();
    } else if (k > back)
      setMsg({ ok: false, text: `That works but jumps less than it could: the clause is already unit at a lower level. Look at the levels of the other literals of the clause.` });
    else setMsg({ ok: false, text: `At level ${k} the clause has more than one open literal (it is not unit yet), so nothing would be propagated.` });
  };

  const flowNodes = graphNodes(run, (id) =>
    phase === "uip" ? "" : id === uip ? "target" : phase === "clause" && chosen.includes(id) ? "picked" : phase !== "clause" && cut.includes(id) ? "picked" : "",
  );
  const flowEdges = graphEdges(truth, () => "");

  return (
    <div className="edu-body graph-level">
      <div className="graph-side">
        <h4>The formula</h4>
        <div className="edu-formula small">{(run.resp.formula ?? []).map((a, i) => <div key={i} className="mono">F{i + 1}: {showAssertion(a)}</div>)}</div>
        <h4>Your answers</h4>
        <ol className="edu-steps">
          <li className={phase === "uip" ? "now" : "done"}>
            <b>First UIP:</b> {phase === "uip" ? "?" : text(uip)}
          </li>
          <li className={phase === "clause" ? "now" : phase === "uip" ? "" : "done"}>
            <b>Learnt clause:</b> <span className="mono">{phase === "uip" ? "?" : phase === "clause" ? clauseText(chosen) : clauseText(cut)}</span>
          </li>
          <li className={phase === "level" ? "now" : phase === "done" ? "done" : ""}>
            <b>Backjump to level:</b> {phase === "done" ? back : "?"}
          </li>
        </ol>
      </div>
      <div className="graph-main">
        <p className="note">
          {phase === "uip" && <>Click the <b>First UIP</b>: the literal of the conflict level (@{confLevel}) closest to κ that every path from the decision to κ goes through.</>}
          {phase === "clause" && <>Click the literals on the cut: the UIP and every literal of an earlier level with an edge into the conflict side. The learnt clause is their negations.</>}
          {phase === "level" && <>Which level does CDCL jump back to?</>}
          {phase === "done" && <>Solved.</>}
        </p>
        <div className="graph edu-graph">
          <ReactFlow
            nodes={flowNodes}
            edges={flowEdges}
            onNodeClick={(_, n) => click(n.id)}
            fitView
            fitViewOptions={{ padding: 0.2 }}
            nodesDraggable={false}
            nodesConnectable={false}
            zoomOnScroll={false}
            preventScrolling={false}
            proOptions={{ hideAttribution: true }}
          >
            <Background gap={24} color="#e7e2d6" />
          </ReactFlow>
        </div>
        <div className="row">
          {phase === "clause" && <button className="primary" onClick={checkClause}>Check the clause</button>}
          {phase === "level" &&
            Array.from({ length: confLevel }, (_, k) => (
              <button key={k} onClick={() => pickLevel(k)}>
                level {k}
              </button>
            ))}
          <button className="ghost" onClick={() => { setPhase("uip"); setChosen([]); setMsg(null); }}>Start again</button>
        </div>
        {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
      </div>
    </div>
  );
}
