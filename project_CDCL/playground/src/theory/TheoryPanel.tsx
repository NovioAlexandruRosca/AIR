import { forwardRef, useEffect, useMemo, useState } from "react";
import type { DtSnapshot, LiaSnapshot, PlaygroundResponse } from "../api";
import type { Labels, Step } from "../model";
import { LiaView } from "./LiaView";
import { CongruenceGraph } from "./CongruenceGraph";
import { Purification } from "./Purification";
import { TheoryState } from "../components/TheoryState";

interface Props {
  resp: PlaygroundResponse;
  L: Labels;
  /** last event applied in the state shown */
  end: number;
  step: Step | null;
}

type Tab = "purify" | "LIA" | "DT";

/** The theory's last check up to event `end` (and its conflict message, if it ended in one). */
function lastCheck<T>(resp: PlaygroundResponse, theory: string, end: number): { data: T; conflict: string | null; at: number } | null {
  for (let i = Math.min(end, resp.events.length - 1); i >= 0; i--) {
    const e = resp.events[i];
    if (e.type !== "Theory" || e.theory !== theory || !e.data || (e.kind !== "state" && e.kind !== "conflict")) continue;
    let conflict = e.kind === "conflict" ? e.message : null;
    // a "state" snapshot right after a conflict belongs to the same check
    for (let j = i - 1; !conflict && j >= 0; j--) {
      const f = resp.events[j];
      if (f.type === "Decide" || f.type === "Propagate" || f.type === "Backjump") break;
      if (f.type === "Theory" && f.theory === theory && f.kind === "conflict") conflict = f.message;
    }
    return { data: e.data as T, conflict, at: i };
  }
  return null;
}

function dtSymbolsOf(dt: DtSnapshot | undefined): Set<string> {
  const out = new Set<string>();
  for (const d of dt?.datatypes ?? [])
    for (const c of d.ctors.split(" | ")) {
      const m = c.match(/^([^(]+)(?:\((.*)\))?$/);
      if (!m) continue;
      out.add(m[1].trim());
      out.add(`is-${m[1].trim()}`);
      for (const f of (m[2] ?? "").split(",")) if (f.includes(":")) out.add(f.split(":")[0].trim());
    }
  return out;
}

export const TheoryPanel = forwardRef<HTMLElement, Props>(function TheoryPanel({ resp, L, end, step }, ref) {
  const smt = resp.smt!;
  const uses = (t: string) => smt.vars.some((v) => v.theories.includes(t) && v.kind !== "aux");
  const tabs: Tab[] = [];
  if (smt.fresh.length || smt.shared.length) tabs.push("purify");
  if (uses("LIA")) tabs.push("LIA");
  if (uses("DT")) tabs.push("DT");
  const [tab, setTab] = useState<Tab>(tabs.includes("LIA") ? "LIA" : tabs[0] ?? "LIA");

  // follow the main stepper when a theory is at work
  useEffect(() => {
    const t = step?.theory as Tab | undefined;
    if (t && tabs.includes(t) && (step?.kind === "invoke" || step?.kind === "theory-unsat" || step?.kind === "derive")) setTab(t);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [step]);
  useEffect(() => {
    if (!tabs.includes(tab) && tabs.length) setTab(tabs[0]);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [resp]);

  const lia = useMemo(() => lastCheck<LiaSnapshot>(resp, "LIA", end), [resp, end]);
  const dt = useMemo(() => lastCheck<DtSnapshot>(resp, "DT", end), [resp, end]);
  const dtSymbols = useMemo(() => {
    let any = resp.replay.theories?.DT;
    for (const e of resp.events) if (!any && e.type === "Theory" && e.theory === "DT" && e.data) any = e.data as DtSnapshot;
    return dtSymbolsOf(any);
  }, [resp]);
  const shared = useMemo(() => new Set(smt.shared.map((s) => s.name)), [smt]);

  if (!tabs.length) return null;
  const name: Record<Tab, string> = { purify: "Purification", LIA: "LIA · Simplex", DT: "DT · congruence closure" };
  return (
    <section className="card theory-panel" ref={ref}>
      <div className="tp-head">
        <h2>Inside the theory solvers</h2>
        <div className="tabs" role="tablist">
          {tabs.map((t) => (
            <button key={t} role="tab" aria-selected={tab === t} className={tab === t ? "tab on" : "tab"} onClick={() => setTab(t)}>
              {name[t]}
            </button>
          ))}
        </div>
      </div>
      {tab === "purify" && <Purification resp={resp} dtSymbols={dtSymbols} />}
      {tab === "LIA" &&
        (lia?.data.check ? (
          <>
            <p className="tp-when">LIA's most recent check at this point of the run{lia.conflict ? " — it found a conflict" : ""}. Step through it with its own Next button.</p>
            <LiaView check={lia.data.check} L={L} />
          </>
        ) : (
          <p className="empty">LIA has not been asked yet. It is invoked once the context contains arithmetic literals.</p>
        ))}
      {tab === "DT" &&
        (dt?.data.nodes ? (
          <>
            <p className="tp-when">DT's most recent check at this point of the run{dt.conflict ? " — it found a conflict" : ""}.</p>
            <CongruenceGraph dt={dt.data} L={L} conflict={dt.conflict} shared={shared} />
          </>
        ) : (
          <p className="empty">DT has not been asked yet. It is invoked once the context contains datatype literals.</p>
        ))}
      <TheoryState resp={resp} L={L} />
    </section>
  );
});
