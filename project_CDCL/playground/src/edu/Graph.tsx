import { useEffect, useMemo, useRef, useState } from "react";
import { Background, MarkerType, Position, ReactFlow, type Edge, type Node } from "@xyflow/react";
import { playground, type FormulaNode, type Lit, type Pick, type PlaygroundResponse } from "../api";
import { litText, makeLabels, visibleVar, type Labels } from "../model";
import type { GraphLevel } from "./levels";

export const KAPPA = "κ";

export interface Run {
  resp: PlaygroundResponse;
  L: Labels;
  /** trail literals shown as nodes, with their level and whether they were decided */
  nodes: { lit: Lit; level: number; decided: boolean }[];
  /** node id → the node ids it really comes from */
  causes: Map<string, string[]>;
}

type Pick3 = { src: string; decisions: string[]; theoryPropagation: boolean };

/** Run the level on the solver: its decisions (picking the first unit clause whenever asked). */
export async function runLevel(level: Pick3): Promise<Run> {
  const base = { src: level.src, lemmas: [], theoryPropagation: level.theoryPropagation, finish: false };
  const first = await playground({ ...base, decisions: [] });
  const L0 = makeLabels(first);
  const byLabel = new Map<string, number>();
  L0.vars.forEach((v, i) => v && byLabel.set(v.label, i));
  L0.written.forEach((w, i) => w && byLabel.set(w, i));
  const decisions = level.decisions.map((d) => {
    const neg = d.startsWith("¬");
    const v = byLabel.get(neg ? d.slice(1) : d);
    if (v === undefined) throw new Error(`no atom '${d}' in this level`);
    return neg ? -v : v;
  });
  const picks: Pick[] = [];
  let resp = await playground({ ...base, decisions, picks });
  for (let i = 0; i < 10 && resp.replay.outcome === "units"; i++) {
    picks.push({ after: resp.replay.applied, lit: resp.replay.units[0].lit });
    resp = await playground({ ...base, decisions, picks });
  }
  const L = makeLabels(resp);
  const rp = resp.replay;
  const nodes = rp.trail.filter((t) => visibleVar(L, Math.abs(t.lit))).map((t) => ({ lit: t.lit, level: t.level, decided: t.reason === null }));
  const id = (v: number) => String(nodes.find((n) => Math.abs(n.lit) === v)?.lit ?? "");
  const causes = new Map<string, string[]>();
  for (const t of rp.trail) {
    if (t.reason === null || !visibleVar(L, Math.abs(t.lit))) continue;
    const from = rp.db[t.reason].filter((l) => Math.abs(l) !== Math.abs(t.lit)).map((l) => id(Math.abs(l))).filter(Boolean);
    causes.set(String(t.lit), from);
  }
  if (rp.outcome === "conflict" && rp.conflict !== null) causes.set(KAPPA, rp.db[rp.conflict].map((l) => id(Math.abs(l))).filter(Boolean));
  return { resp, L, nodes, causes };
}

export const key = (from: string, to: string) => `${from}->${to}`;

/** The edges `from->to` the run really has. */
export const truthEdges = (run: Run) => {
  const s = new Set<string>();
  run.causes.forEach((from, to) => from.forEach((f) => s.add(key(f, to))));
  return s;
};

// layout: one column per trail position, one band per decision level (in
// three staggered rows, so edges do not run through other nodes); edges
// leave a node on its right and enter on its left
const COL = 215;
const BAND = 165;
const STAGGER = 50;
const side = { sourcePosition: Position.Right, targetPosition: Position.Left };

/** The run's literals (and κ) as React Flow nodes; `extra` adds a class per node id. */
export function graphNodes(run: Run, extra: (id: string) => string): Node[] {
  const { L, nodes, causes } = run;
  const text = (id: string) => litText(L, Number(id));
  const maxLevel = Math.max(0, ...nodes.map((n) => n.level));
  const out: Node[] = nodes.map((n, i) => {
    const id = String(n.lit);
    const root = !(causes.get(id)?.length);
    return {
      id,
      position: { x: i * COL, y: n.level * BAND + (i % 3) * STAGGER },
      ...side,
      data: { label: `${text(id)} @${n.level}` },
      width: Math.max(90, (text(id).length + 4) * 10 + 24),
      height: 42,
      className: `edu-node ${n.decided ? "decided" : root ? "fact" : ""} ${extra(id)}`,
      draggable: false,
    };
  });
  if (causes.has(KAPPA))
    out.push({ id: KAPPA, position: { x: nodes.length * COL, y: maxLevel * BAND + STAGGER }, ...side, data: { label: "κ (conflict)" }, width: 130, height: 42, className: `edu-node kappa ${extra(KAPPA)}`, draggable: false });
  return out;
}

const EDGE_COLOR: Record<string, string> = { good: "#1b8a3a", bad: "#c92a2a", missing: "#7b3fc4" };

/** Edges `from->to` as React Flow edges; `cls` gives each its class (good, bad, missing or ""). */
export function graphEdges(keys: string[], cls: (k: string) => string): Edge[] {
  return keys.map((k) => {
    const [from, to] = k.split("->");
    const c = cls(k);
    return { id: k, source: from, target: to, className: `edu-edge ${c}`, markerEnd: { type: MarkerType.ArrowClosed, width: 18, height: 18, color: EDGE_COLOR[c] ?? "#374151" } };
  });
}

/** Build the implication graph of a run: for each propagated literal, click its causes. */
export function Graph({ level, onSolved }: { level: GraphLevel; onSolved: () => void }) {
  const [run, setRun] = useState<Run | null>(null);
  const [err, setErr] = useState<string | null>(null);
  const [target, setTargetState] = useState<string | null>(null);
  // React Flow may call an older click handler: read the target from a ref
  const targetRef = useRef<string | null>(null);
  const setTarget = (t: string | null) => {
    targetRef.current = t;
    setTargetState(t);
  };
  const [edges, setEdges] = useState<Set<string>>(new Set());
  const [checked, setChecked] = useState(false);
  const [solution, setSolution] = useState(false);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);

  useEffect(() => {
    setRun(null);
    setErr(null);
    runLevel(level).then(setRun, (e) => setErr((e as Error).message));
  }, [level]);

  const truth = useMemo(() => (run ? truthEdges(run) : new Set<string>()), [run]);

  if (err) return <div className="error">{err}</div>;
  if (!run) return <p className="note">Running the solver…</p>;
  const { L, nodes, causes } = run;
  const conflict = causes.has(KAPPA);
  const text = (id: string) => (id === KAPPA ? KAPPA : litText(L, Number(id)));
  const roots = new Set(nodes.filter((n) => !(causes.get(String(n.lit))?.length)).map((n) => String(n.lit)));

  const clickNode = (id: string) => {
    setMsg(null);
    const target = targetRef.current;
    if (target === null || target === id) {
      if (roots.has(id)) {
        setMsg({ ok: false, text: `${text(id)} ${nodes.find((n) => String(n.lit) === id)?.decided ? "is a decision" : "is a fact of the input (a unit clause)"}: nothing causes it, so it has no incoming edges. Pick a propagated literal${conflict ? " or κ" : ""}.` });
        return;
      }
      setTarget(target === id ? null : id);
      return;
    }
    const k = key(id, target);
    setEdges((old) => {
      const next = new Set(old);
      if (next.has(k)) next.delete(k);
      else next.add(k);
      return next;
    });
    setChecked(false);
  };

  const check = () => {
    setChecked(true);
    const wrong = [...edges].filter((e) => !truth.has(e)).length;
    const missing = [...truth].filter((e) => !edges.has(e)).length;
    if (!wrong && !missing) {
      setMsg({ ok: true, text: `Right! Every propagated literal points back to the literals of its reason clause${conflict ? ", and κ to every literal of the conflicting clause" : ""}. This is the graph conflict analysis cuts to find the First UIP.` });
      onSolved();
    } else
      setMsg({
        ok: false,
        text: [wrong ? `${wrong} edge${wrong === 1 ? " is" : "s are"} wrong (red)` : "", missing ? `${missing} edge${missing === 1 ? " is" : "s are"} missing` : ""].filter(Boolean).join(", ") + ". A propagated literal's causes are the other literals of the clause that became unit (they were all false).",
      });
  };

  const flowNodes = graphNodes(run, (id) => (target === id ? "target" : ""));
  const all = new Set([...edges, ...(solution ? truth : [])]);
  const flowEdges = graphEdges([...all], (k) => {
    const good = truth.has(k);
    const mine = edges.has(k);
    return !mine ? "missing" : checked ? (good ? "good" : "bad") : "";
  });

  return (
    <div className="edu-body graph-level">
      <div className="graph-side">
        <h4>The formula</h4>
        <div className="edu-formula small">{(run.resp.formula ?? []).map((a, i) => <div key={i} className="mono">F{i + 1}: {showAssertion(a)}</div>)}</div>
        <h4>The context after the run</h4>
        <ul className="context">
          {nodes.map((n, i) => (
            <li key={i} className={i > 0 && n.level !== nodes[i - 1].level ? "level-start" : ""}>
              {n.decided && <span className="d">d</span>}
              <span className={`chip ${n.lit > 0 ? "t" : "f"} static`}>{litText(L, n.lit)}</span>
              <span className="note">@{n.level}</span>
            </li>
          ))}
          {conflict && <li className="level-start"><b>conflict</b></li>}
        </ul>
      </div>
      <div className="graph-main">
        <p className="note">
          {target ? (
            <>Now click the literals that caused <b>{text(target)}</b> (click again to remove an edge), or click it again to finish.</>
          ) : (
            <>Click a propagated literal{conflict ? " or κ" : ""} to give it its causes.</>
          )}
        </p>
        <div className="graph edu-graph">
          <ReactFlow
            nodes={flowNodes}
            edges={flowEdges}
            onNodeClick={(_, n) => clickNode(n.id)}
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
          <button className="primary" onClick={check}>Check</button>
          <button className="ghost" onClick={() => { setEdges(new Set()); setChecked(false); setMsg(null); setTarget(null); }}>Start again</button>
          <button className="ghost" onClick={() => setSolution((s) => !s)}>{solution ? "Hide" : "Show"} the missing edges</button>
        </div>
        {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
      </div>
    </div>
  );
}

/** An assertion as text. */
export function showAssertion(n: FormulaNode): string {
  if ("const" in n) return String(n.const);
  if ("atom" in n) return n.label;
  if (n.op === "not") return `¬${"atom" in n.args[0] ? (/\s/.test(n.args[0].label) ? `(${n.args[0].label})` : n.args[0].label) : `(${showAssertion(n.args[0])})`}`;
  const sep = { and: " ∧ ", or: " ∨ ", "=>": " ⇒ ", iff: " ⇔ ", xor: " ⊕ ", ite: ", " }[n.op];
  return `(${n.args.map(showAssertion).join(sep)})`;
}
