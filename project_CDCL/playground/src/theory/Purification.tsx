import { useEffect, useMemo, useState } from "react";
import type { PlaygroundResponse } from "../api";

interface Props {
  resp: PlaygroundResponse;
  /** DT function symbols (constructors, selectors, testers) */
  dtSymbols: Set<string>;
}

type Owner = "LIA" | "DT" | "both" | "none";

const LIA_OPS = new Set(["+", "-", "−", "*", "·", "<", ">", "≤", "≥", "<=", ">="]);

/** Split a printed term into tokens, keeping identifiers like is-cons whole. */
const tokens = (s: string) => s.match(/is-[A-Za-z_]\w*|[A-Za-z_][\w.']*|\d+|<=|>=|\s+|./g) ?? [];

interface PStep {
  title: string;
  text: string;
  rows: { before?: string; after: string; highlight?: string; fresh?: string }[];
  split?: boolean;
}

/**
 * Purification step by step: which theory owns which symbol, how alien
 * subterms are replaced by fresh constants, and which constants end up
 * shared (the ones Nelson–Oppen exchanges equalities about).
 */
export function Purification({ resp, dtSymbols }: Props) {
  const smt = resp.smt!;
  const tokOwner = (t: string): Owner => {
    if (dtSymbols.has(t)) return "DT";
    if (LIA_OPS.has(t) || /^\d+$/.test(t)) return "LIA";
    return "none";
  };
  const litOwner = (lit: string): Owner => {
    const o = new Set(tokens(lit).map(tokOwner).filter((x) => x !== "none"));
    return o.size === 2 ? "both" : o.size === 1 ? ([...o][0] as Owner) : "both";
  };

  const steps = useMemo(() => {
    const defs = smt.definitions.map((d) => {
      const i = d.indexOf(" = ");
      return { k: d.slice(0, i), t: d.slice(i + 3), text: d };
    });
    const out: PStep[] = [];
    out.push({
      title: "Who understands what",
      text:
        `Each theory solver only understands its own symbols. LIA: numbers, +, −, ·, <, ≤, >, ≥. DT: ${[...dtSymbols].filter((s) => !s.startsWith("is-")).join(", ")} and the testers is-… . ` +
        "Equality = and the constants (variables) can be used by both. A literal that mixes the symbols of two theories cannot be given to either one.",
      rows: smt.assertions.map((a) => ({ after: a })),
    });
    const pure: number[] = [];
    smt.assertions.forEach((a, i) => {
      const p = smt.purified[i];
      if (p === a) {
        pure.push(i);
        return;
      }
      const def = defs.find((d) => p.includes(d.k) && a.includes(d.t));
      const alienOwner = def ? litOwner(def.t) : "both";
      const host = alienOwner === "DT" ? "LIA" : "DT";
      out.push({
        title: `Purify assertion ${i + 1}`,
        text: def
          ? `${def.t} is a ${alienOwner} term inside a ${host} literal, so ${host} could not read this assertion. ` +
            `Replace it by a fresh constant ${def.k} and remember ${def.k} = ${def.t} separately. Now every literal belongs to one theory.`
          : `Mixed symbols are replaced by fresh constants.`,
        rows: [{ before: a, after: p, highlight: def?.t, fresh: def?.k }],
      });
    });
    if (pure.length) {
      out.splice(1, 0, {
        title: "Already pure",
        text:
          pure.length === smt.assertions.length
            ? "Every assertion uses the symbols of one theory only, so there is nothing to replace."
            : `${pure.length === 1 ? "This assertion uses" : "These assertions use"} the symbols of one theory only: nothing to replace.`,
        rows: pure.map((i) => ({ after: smt.assertions[i] })),
      });
    }
    if (defs.length) {
      out.push({
        title: "Definitions of the fresh constants",
        text:
          "Each fresh constant gets its defining equation. The equation is a literal of the theory that owns the term; the constant itself is an ordinary variable that the other theory can use.",
        rows: defs.map((d) => ({ after: d.text, fresh: d.k })),
      });
    }
    out.push({
      title: "What each theory sees",
      text: "After purification every literal goes to exactly one theory solver (an equality between plain constants can go to both).",
      rows: [],
      split: true,
    });
    if (smt.shared.length) {
      const pairs = smt.interface.map((p) => `${p.x} = ${p.y}`);
      out.push({
        title: "Shared constants",
        text:
          `${smt.shared.map((s) => s.name).join(", ")} occur in both theories. These are the only things the two solvers have in common, ` +
          "so Nelson–Oppen only has to make them agree on which shared constants are equal" +
          (pairs.length ? `: ${pairs.join(", ")} — each is propagated by one theory or decided by the SAT solver.` : "."),
        rows: [],
        split: true,
      });
    }
    return out;
  }, [resp, dtSymbols]);

  const [k, setK] = useState(0);
  useEffect(() => setK(0), [resp.smt]);
  const step = steps[Math.min(k, steps.length - 1)];
  const sharedNames = new Set(smt.shared.map((s) => s.name));

  const paint = (s: string, highlight?: string, fresh?: string) => {
    const parts: React.ReactNode[] = [];
    const hl = highlight ? s.indexOf(highlight) : -1;
    const seg = (text: string, key: string, extra = "") =>
      tokens(text).map((t, i) => {
        const o = tokOwner(t);
        const cls = [o === "DT" ? "tok-dt" : o === "LIA" ? "tok-lia" : "", t === fresh ? "tok-fresh" : "", sharedNames.has(t) && step.title === "Shared constants" ? "tok-shared" : "", extra].join(" ");
        return <span key={`${key}${i}`} className={cls}>{t}</span>;
      });
    if (hl >= 0) {
      parts.push(...seg(s.slice(0, hl), "a"));
      parts.push(<span key="h" className="alien">{seg(highlight!, "h")}</span>);
      parts.push(...seg(s.slice(hl + highlight!.length), "b"));
    } else parts.push(...seg(s, "a"));
    return parts;
  };

  const split = () => {
    const lits = smt.purified.flatMap((p) => p.split(/ ∨ | ∧ /)).concat(smt.definitions);
    const by: Record<"LIA" | "DT", string[]> = { LIA: [], DT: [] };
    for (const l of new Set(lits)) {
      const o = litOwner(l);
      if (o === "LIA" || o === "both") by.LIA.push(l);
      if (o === "DT" || o === "both") by.DT.push(l);
    }
    return (
      <div className="sees">
        {(["LIA", "DT"] as const).map((t) => (
          <div key={t} className={`sees-col ${t === "LIA" ? "lia" : "dt"}`}>
            <h5>{t} sees</h5>
            {by[t].map((l) => <div key={l} className="mono">{paint(l)}</div>)}
          </div>
        ))}
      </div>
    );
  };

  return (
    <div className="purify">
      <div className="plane-step">
        <span className="step-kind">{step.title}</span>
        <p>{step.text}</p>
        <div className="mini-nav">
          <button className="ghost" onClick={() => setK((k) => Math.max(0, k - 1))} disabled={k === 0}>← Back</button>
          <span className="counter">{k + 1} / {steps.length}</span>
          <button className="primary" onClick={() => setK((k) => Math.min(steps.length - 1, k + 1))} disabled={k >= steps.length - 1}>Next →</button>
        </div>
      </div>
      <div className="purify-body">
        {step.rows.map((r, i) => (
          <div key={i} className="purify-row">
            {r.before && (
              <>
                <div className="mono before">{paint(r.before, r.highlight)}</div>
                <div className="becomes">becomes</div>
              </>
            )}
            <div className="mono after">{paint(r.after, undefined, r.fresh)}</div>
          </div>
        ))}
        {step.split && split()}
        <div className="legend inline">
          <span className="tok-lia">LIA symbol</span>
          <span className="tok-dt">DT symbol</span>
          {smt.fresh.length > 0 && <span className="tok-fresh">fresh constant</span>}
        </div>
      </div>
    </div>
  );
}
