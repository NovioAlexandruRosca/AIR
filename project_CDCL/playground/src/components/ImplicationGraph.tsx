import { useEffect, useMemo } from "react";
import { Background, Controls, MarkerType, Position, ReactFlow, useNodesInitialized, useReactFlow, type Edge, type Node } from "@xyflow/react";
import "@xyflow/react/dist/style.css";
import dagre from "@dagrejs/dagre";
import type { Lit, PlaygroundResponse } from "../api";
import { clauseInfo, litText, visibleVar, type Labels, type State, type TheoryClauseEvent } from "../model";

interface Props {
  resp: PlaygroundResponse;
  L: Labels;
  state: State;
  tcs: Map<number, TheoryClauseEvent>;
  learnedKeys: Set<string>;
  focusLits: Lit[];
}

const H = 46;
const fitOptions = { padding: 0.15, maxZoom: 1.1 };

/** Re-fit once the nodes are measured and whenever the box resizes. */
function FitView({ version }: { version: string }) {
  const { fitView } = useReactFlow();
  const ready = useNodesInitialized();
  useEffect(() => {
    if (!ready) return;
    let timer = 0;
    const fit = () => {
      clearTimeout(timer);
      timer = window.setTimeout(() => fitView({ ...fitOptions, duration: 250 }), 40);
    };
    fit();
    window.addEventListener("resize", fit);
    return () => {
      clearTimeout(timer);
      window.removeEventListener("resize", fit);
    };
  }, [ready, version, fitView]);
  return null;
}
const width = (text: string) => Math.max(70, text.length * 12 + 36);

/**
 * Implication graph of the current context: an edge a → b when a (false
 * literal of b's reason clause) helped force b. Hidden encoding variables are
 * skipped by connecting straight through them. Laid out left to right by dagre.
 */
export function ImplicationGraph({ resp, L, state, tcs, learnedKeys, focusLits }: Props) {
  const { nodes, edges } = useMemo(() => {
    const focus = new Set(focusLits.map(Math.abs));
    const entry = new Map(state.trail.map((t) => [Math.abs(t.lit), t]));
    const db = resp.replay.db;

    // visible variables a clause's other literals stand for
    const sources = (clause: number, self: number, seen = new Set<number>()): number[] => {
      const out: number[] = [];
      for (const l of db[clause] || []) {
        const v = Math.abs(l);
        if (v === self || !entry.has(v) || seen.has(v)) continue;
        seen.add(v);
        if (visibleVar(L, v)) out.push(v);
        else {
          const r = entry.get(v)!.reason;
          if (r !== null) out.push(...sources(r, v, seen));
        }
      }
      return [...new Set(out)];
    };

    const g = new dagre.graphlib.Graph();
    g.setGraph({ rankdir: "LR", nodesep: 22, ranksep: 70, marginx: 10, marginy: 10 });
    g.setDefaultEdgeLabel(() => ({}));

    const nodes: Node[] = [];
    const edges: Edge[] = [];
    const add = (id: string, label: string, cls: string) => {
      const w = width(label);
      g.setNode(id, { width: w, height: H });
      nodes.push({
        id,
        data: { label },
        position: { x: 0, y: 0 },
        className: `gnode ${cls}`,
        width: w,
        height: H,
        style: { width: w, height: H },
        sourcePosition: Position.Right,
        targetPosition: Position.Left,
        draggable: false,
        connectable: false,
      });
    };
    const link = (from: number, to: string, label?: string, cls = "") => {
      g.setEdge(`v${from}`, to);
      edges.push({
        id: `${from}->${to}`,
        source: `v${from}`,
        target: to,
        label,
        className: cls,
        markerEnd: { type: MarkerType.ArrowClosed, width: 16, height: 16 },
      });
    };

    for (const t of state.trail) {
      const v = Math.abs(t.lit);
      if (!visibleVar(L, v)) continue;
      const decision = t.reason === null;
      const tc = t.reason !== null ? tcs.get(t.reason) : undefined;
      const theory = tc && tc.kind !== "axiom";
      const cls = [decision ? "decision" : theory ? "theory" : "bcp", t.lit > 0 ? "t" : "f", focus.has(v) ? "focus" : ""].join(" ");
      add(`v${v}`, `${litText(L, t.lit)}  @${t.level}`, cls);
    }
    for (const t of state.trail) {
      const v = Math.abs(t.lit);
      if (!visibleVar(L, v) || t.reason === null) continue;
      const tc = tcs.get(t.reason);
      const theory = tc && tc.kind !== "axiom" ? tc.theory : undefined;
      const from = sources(t.reason, v);
      from.forEach((s, i) => link(s, `v${v}`, theory && i === 0 ? theory : undefined, theory ? "theory" : ""));
    }
    if (state.conflict !== null) {
      add("conflict", "✗ conflict", "conflict");
      const name = clauseInfo(resp, tcs, learnedKeys, state.conflict).name;
      sources(state.conflict, 0).forEach((s, i) => link(s, "conflict", i === 0 ? name : undefined, "to-conflict"));
    }

    dagre.layout(g);
    for (const n of nodes) {
      const p = g.node(n.id);
      n.position = { x: p.x - p.width / 2, y: p.y - p.height / 2 };
    }
    return { nodes, edges };
  }, [resp, L, state, tcs, learnedKeys, focusLits]);

  if (!nodes.length) return <p className="empty">The graph grows as literals are assigned.</p>;
  return (
    <div className="graph">
      <ReactFlow
        nodes={nodes}
        edges={edges}
        fitView
        fitViewOptions={fitOptions}
        nodesDraggable={false}
        nodesConnectable={false}
        zoomOnScroll={false}
        preventScrolling={false}
        proOptions={{ hideAttribution: true }}
        minZoom={0.2}
      >
        <Background gap={24} color="#e7e2d6" />
        <Controls showInteractive={false} />
        <FitView version={nodes.map((n) => n.id).join() + "|" + edges.length} />
      </ReactFlow>
    </div>
  );
}
