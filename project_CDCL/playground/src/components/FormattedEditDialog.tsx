import { useMemo, useState } from "react";
import { FormulaError, toSmtLib } from "../formulaText";

interface Props {
  onCancel: () => void;
  onUse: (smtlib: string) => void;
}

const SAMPLE = "(x + 1 > 0 or x + y > 0) and (x < 0 or x + y > 4) and not (x + y > 0)";

/** Type a formula the way you would write it on paper; it is turned into SMT-LIB. */
export function FormattedEditDialog({ onCancel, onUse }: Props) {
  const [text, setText] = useState(() => {
    try {
      return localStorage.getItem("playground.formatted") ?? SAMPLE;
    } catch {
      return SAMPLE;
    }
  });
  const result = useMemo(() => {
    try {
      return { smt: toSmtLib(text), error: null };
    } catch (e) {
      if (e instanceof FormulaError) {
        const before = text.slice(0, e.pos);
        const line = before.split("\n").length;
        const col = before.length - before.lastIndexOf("\n");
        return { smt: null, error: `line ${line}, column ${col}: ${e.message}` };
      }
      throw e;
    }
  }, [text]);
  const use = () => {
    if (!result.smt) return;
    try {
      localStorage.setItem("playground.formatted", text);
    } catch {
      /* not essential */
    }
    onUse(result.smt);
  };

  return (
    <div className="modal-back" onMouseDown={(e) => e.target === e.currentTarget && onCancel()}>
      <div className="modal wide">
        <h2>Write a formula</h2>
        <p className="note">
          Write it as on paper: <code>and</code> <code>or</code> <code>not</code> <code>-&gt;</code> <code>&lt;-&gt;</code> (or <code>/\</code> <code>\/</code> <code>!</code>,{" "}
          <code>\and</code> <code>\or</code> <code>\not</code>, <code>∧ ∨ ¬</code>), comparisons <code>&lt; &lt;= &gt; &gt;= = !=</code>, sums and numbers times a variable
          (<code>2*x</code> or <code>2x</code>). A name you compare is an integer, a name used on its own is true/false. Every line is a separate assertion.
        </p>
        <div className="formatted">
          <div>
            <h5>Your formula</h5>
            <textarea value={text} onChange={(e) => setText(e.target.value)} spellCheck={false} autoFocus className="readable" />
          </div>
          <div>
            <h5>What the solver reads (SMT-LIB)</h5>
            {result.smt ? <pre className="smt-out">{result.smt}</pre> : <p className="parse-error">{result.error}</p>}
          </div>
        </div>
        <div className="row end">
          <button className="ghost" onClick={onCancel}>Cancel</button>
          <button className="primary" onClick={use} disabled={!result.smt}>Use this formula</button>
        </div>
      </div>
    </div>
  );
}
