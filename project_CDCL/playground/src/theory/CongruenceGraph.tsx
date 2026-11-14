import { useEffect, useMemo, useState } from "react";
import { Background, Handle, MarkerType, Position, ReactFlow, type BuiltInEdge, type Node, type NodeProps } from "@xyflow/react";
import dagre from "@dagrejs/dagre";
import type { DtSnapshot } from "../api";
import { litText, type Labels } from "../model";

interface Props {
  dt: DtSnapshot;
  L: Labels;
  /** the theory's message when this check ended in a conflict */
  conflict: string | null;
  shared: Set<string>;
}

const PALETTE = [
  ["#dbeafe", "#2f5bd3"],
  ["#dcfce7", "#1b8a3a"],
  ["#fef3c7", "#b7791f"],
  ["#fce7f3", "#c026d3"],
  ["#ede9fe", "#7b3fc4"],
  ["#cffafe", "#0e7490"],
  ["#ffedd5", "#d9640b"],
  ["#e0e7ff", "#4338ca"],
];

const RULE: Record<string, string> = {
  asserted: "the context says so",
  congruence: "congruence",
  injectivity: "injectivity",
  selector: "selector",
  tester: "tester",
  "last constructor": "only constructor left",
};

/** A term: arguments hang below; merges arc underneath, disequalities above. */
function TermNode({ data }: NodeProps) {
  return (
    <>
      <Handle type="target" position={Position.Top} />
      <Handle type="source" position={Position.Bottom} />
      <Handle id="eq-out" type="source" position={Position.Bottom} style={{ left: "35%" }} />
      <Handle id="eq-in" type="target" position={Position.Bottom} style={{ left: "65%" }} />
      <Handle id="ne-out" type="source" position={Position.Top} style={{ left: "35%" }} />
      <Handle id="ne-in" type="target" position={Position.Top} style={{ left: "65%" }} />
      {String(data.label)}
    </>
  );
}
const nodeTypes = { term: TermNode };

interface CStep {
  title: string;
  text: string;
  merges: number;
  diseqs: boolean;
  final?: "unsat" | "sat";
}

/**
 * Congruence closure, one merge at a time: the terms of the DT literals
 * (arrows point to arguments), coloured by equivalence class.
 */
export function CongruenceGraph({ dt, L, conflict, shared }: Props) {
  const nodesIn = dt.nodes ?? [];
  const history = dt.history ?? [];
  const diseqs = dt.diseqNodes ?? [];
  const term = (i: number) => nodesIn[i]?.term ?? "?";

  const steps = useMemo(() => {
    const out: CStep[] = [];
    out.push({
      title: "The terms",
      text:
        "Every term that occurs in a DT literal is a node; arrows go from a function application to its arguments. " +
        "At first each term is only equal to itself (grey). Congruence closure now merges terms that must be equal.",
      merges: 0,
      diseqs: false,
    });
    history.forEach((h, i) => {
      const A = term(h.a);
      const B = term(h.b);
      const lits = h.lits.map((l) => litText(L, l)).join(", ");
      const text =
        h.rule === "asserted"
          ? `The context contains ${lits || `${A} = ${B}`}: put ${A} and ${B} in one class.`
          : h.rule === "congruence"
            ? `${A} and ${B} apply the same function to arguments that are already equal, so they are equal too (congruence).`
            : h.rule === "injectivity"
              ? `Two terms built by the same constructor are equal, so their arguments must be equal: ${A} = ${B} (constructors are injective).`
              : h.rule === "selector"
                ? `${A} reads a field of a term that equals a constructor term, so it is that field: ${A} = ${B}.`
                : h.rule === "tester"
                  ? `${lits} says which constructor built it, so ${A} = ${B}.`
                  : `Every other constructor is excluded, so ${A} = ${B}.`;
      out.push({ title: `Merge ${i + 1}: ${A} = ${B}`, text, merges: i + 1, diseqs: false });
    });
    if (diseqs.length) {
      out.push({
        title: "Disequalities",
        text: `The context also says ${diseqs.map(([a, b]) => `${term(a)} ≠ ${term(b)}`).join(", ")} (red): these must stay in different classes.`,
        merges: history.length,
        diseqs: true,
      });
    }
    if (conflict) {
      out.push({ title: "DT-unsatisfiable", text: explainConflict(conflict), merges: history.length, diseqs: true, final: "unsat" });
    } else {
      out.push({
        title: "Consistent",
        text: "No two different constructors ended up in one class, no disequality is violated and no term contains itself: DT accepts the context.",
        merges: history.length,
        diseqs: true,
        final: "sat",
      });
    }
    return out;
  }, [dt, L, conflict]);

  const [k, setK] = useState(0);
  useEffect(() => setK(0), [dt]);
  const step = steps[Math.min(k, steps.length - 1)];

  const { nodes, edges } = useMemo(() => {
    // classes after the first `step.merges` merges
    const parent = nodesIn.map((_, i) => i);
    const find = (x: number): number => (parent[x] === x ? x : (parent[x] = find(parent[x])));
    history.slice(0, step.merges).forEach((h) => (parent[find(h.a)] = find(h.b)));
    const size = new Map<number, number>();
    nodesIn.forEach((_, i) => size.set(find(i), (size.get(find(i)) ?? 0) + 1));
    const color = new Map<number, number>();
    nodesIn.forEach((_, i) => {
      const r = find(i);
      if (size.get(r)! > 1 && !color.has(r)) color.set(r, color.size % PALETTE.length);
    });

    const g = new dagre.graphlib.Graph();
    g.setGraph({ rankdir: "TB", nodesep: 34, ranksep: 110, marginx: 10, marginy: 10 });
    g.setDefaultEdgeLabel(() => ({}));
    const nodes: Node[] = nodesIn.map((n, i) => {
      const w = Math.max(60, n.term.length * 10 + 30);
      g.setNode(String(i), { width: w, height: 40 });
      const c = color.get(find(i));
      const fresh = step.merges > 0 && (history[step.merges - 1].a === i || history[step.merges - 1].b === i);
      return {
        id: String(i),
        type: "term",
        data: { label: n.term },
        position: { x: 0, y: 0 },
        width: w,
        height: 40,
        className: `cnode ${n.kind} ${fresh ? "focus" : ""} ${shared.has(n.term) ? "shared" : ""}`,
        style: c === undefined ? { width: w, height: 40 } : { width: w, height: 40, background: PALETTE[c][0], borderColor: PALETTE[c][1] },
        sourcePosition: Position.Bottom,
        targetPosition: Position.Top,
        draggable: false,
      };
    });
    const edges: BuiltInEdge[] = [];
    nodesIn.forEach((n, i) =>
      n.children.forEach((c, j) => {
        g.setEdge(String(i), String(c));
        edges.push({ id: `t${i}-${j}`, source: String(i), target: String(c), className: "arg", markerEnd: { type: MarkerType.ArrowClosed, width: 14, height: 14 } });
      }),
    );
    history.slice(0, step.merges).forEach((h, i) =>
      edges.push({
        id: `m${i}`,
        source: String(h.a),
        target: String(h.b),
        sourceHandle: "eq-out",
        targetHandle: "eq-in",
        type: "smoothstep",
        pathOptions: { offset: 22 + 10 * i, borderRadius: 12 },
        label: `= ${RULE[h.rule] ?? h.rule}`,
        className: `merge ${i === step.merges - 1 ? "fresh" : ""}`,
      }),
    );
    if (step.diseqs)
      diseqs.forEach(([a, b], i) =>
        edges.push({ id: `d${i}`, source: String(a), target: String(b), sourceHandle: "ne-out", targetHandle: "ne-in", type: "smoothstep", pathOptions: { offset: 26 + 10 * i, borderRadius: 12 }, label: "≠", className: `diseq ${find(a) === find(b) ? "broken" : ""}` }),
      );
    dagre.layout(g);
    for (const n of nodes) {
      const p = g.node(n.id);
      n.position = { x: p.x - p.width / 2, y: p.y - p.height / 2 };
    }
    return { nodes, edges };
  }, [dt, step, shared]);

  if (!nodesIn.length) return <p className="empty">No datatype literal is in the context yet.</p>;
  return (
    <div className="cc">
      <div className="cc-graph">
        <ReactFlow
          key={JSON.stringify(dt.history) + nodesIn.length}
          nodes={nodes}
          edges={edges}
          nodeTypes={nodeTypes}
          fitView
          fitViewOptions={{ padding: 0.25, maxZoom: 1.3 }}
          nodesDraggable={false}
          nodesConnectable={false}
          zoomOnScroll={false}
          preventScrolling={false}
          proOptions={{ hideAttribution: true }}
        >
          <Background gap={24} color="#e7e2d6" />
        </ReactFlow>
      </div>
      <div className="plane-side">
        <div className={`plane-step ${step.final ?? ""}`}>
          <span className="step-kind">{step.title}</span>
          <p>{step.text}</p>
          <div className="mini-nav">
            <button className="ghost" onClick={() => setK((k) => Math.max(0, k - 1))} disabled={k === 0}>← Back</button>
            <span className="counter">{k + 1} / {steps.length}</span>
            <button className="primary" onClick={() => setK((k) => Math.min(steps.length - 1, k + 1))} disabled={k >= steps.length - 1}>Next →</button>
          </div>
        </div>
        <ul className="legend">
          <li><span className="sw arg" /> argument of a function</li>
          <li><span className="sw merge" /> merged: equal</li>
          <li><span className="sw diseq" /> must stay different</li>
          {shared.size > 0 && <li><span className="sw shared" /> shared with LIA (Nelson–Oppen)</li>}
        </ul>
      </div>
    </div>
  );
}

function explainConflict(msg: string): string {
  if (msg.startsWith("constructor clash")) return `Two different constructors ended up in the same class. ${cap(msg)}. A value is built by exactly one constructor, so DT answers "unsat".`;
  if (msg.includes("but congruence closure derives")) return `A disequality is violated: ${msg}. DT answers "unsat".`;
  if (msg.includes("contains itself") || msg.includes("cycl")) return `${cap(msg)}. A datatype value is finite, so no term can contain itself: DT answers "unsat".`;
  return `${cap(msg)}. DT answers "unsat".`;
}

const cap = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);
