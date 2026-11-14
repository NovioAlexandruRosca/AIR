import { useState } from "react";

interface Props {
  initial: string;
  onCancel: () => void;
  onUse: (text: string) => void;
}

export function EditDialog({ initial, onCancel, onUse }: Props) {
  const [text, setText] = useState(initial);
  return (
    <div className="modal-back" onMouseDown={(e) => e.target === e.currentTarget && onCancel()}>
      <div className="modal">
        <h2>Edit the formula</h2>
        <p className="note">SMT-LIB (<code>declare-fun</code>, <code>declare-datatypes</code>, <code>assert</code>) or DIMACS CNF.</p>
        <textarea value={text} onChange={(e) => setText(e.target.value)} spellCheck={false} autoFocus />
        <div className="row end">
          <button className="ghost" onClick={onCancel}>Cancel</button>
          <button className="primary" onClick={() => onUse(text)}>Use this formula</button>
        </div>
      </div>
    </div>
  );
}
