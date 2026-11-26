//! Solver trace: the contract between the solver and the playground.
//!
//! Every event carries enough data for the UI to rebuild the full state by
//! replaying events from the start (see README, "Trace format").
//! Literals are DIMACS integers, variables are 1-based, clause ids are
//! 0-based indices into the solver's clause database (originals first,
//! learned clauses appended in learning order).

export class MomsCandidate {
  var: number;
  pos: number;
  neg: number;
  score: number;
  constructor(init?: Partial<MomsCandidate>) {
    this.var = init?.var ?? 0;
    this.pos = init?.pos ?? 0;
    this.neg = init?.neg ?? 0;
    this.score = init?.score ?? 0;
  }
}

/// Who made a decision that MOMS did not pick: a theory asking for a case
/// split ("LIA", "DT", "Nelson–Oppen") or the user in the playground.
export class DecisionOrigin {
  by: string;
  why: string;
  constructor(init?: Partial<DecisionOrigin>) {
    this.by = init?.by ?? "";
    this.why = init?.why ?? "";
  }
}

export type Event =
  | {
      kind: "Decide";
      lit: number;
      level: number;
      min_size: number;
      candidates: MomsCandidate[];
      /** None for an ordinary MOMS decision. */
      origin: DecisionOrigin | null;
    }
  | { kind: "Propagate"; lit: number; reason: number; level: number }
  | { kind: "Conflict"; clause: number; level: number }
  | {
      kind: "Resolve";
      /** The clause being resolved (conflict clause on the first step,
       * otherwise the previous resolvent). */
      clause_a: number[];
      /** Clause id of `clause_a` when it is a stored clause (first step). */
      clause_a_id: number | null;
      /** Reason clause of the pivot variable. */
      clause_b: number;
      pivot: number;
      resolvent: number[];
    }
  | {
      kind: "Learn";
      clause: number;
      lits: number[];
      uip: number;
      /** Variables resolved away (conflict side of the cut, besides κ). */
      conflict_side: number[];
      /** Variables of the learned clause (reason side of the cut). */
      reason_side: number[];
      backjump_level: number;
    }
  | { kind: "Backjump"; from: number; to: number; unassigned: number[] }
  | { kind: "Result"; status: string; model: number[] }
  /** A clause added during search by a theory: an explanation for a
   * theory propagation, a conflict, a lemma or an axiom for a new atom. */
  | {
      kind: "TheoryClause";
      clause: number;
      lits: number[];
      /** "explanation" | "conflict" | "lemma" | "axiom" */
      kind_: string;
      theory: string;
      why: string;
    }
  /** A Boolean variable created during search (e.g. a branch-and-bound
   * bound or a split atom). `var` is 1-based. */
  | {
      kind: "NewVar";
      var: number;
      label: string;
      /** Rendering of the negated atom (e.g. "x > 3" for "x ≤ 3"). */
      neg: string;
      kind_: string;
      /** Comma-separated theory names. */
      theories: string;
    }
  /** Free-form theory reasoning step for the UI. `data` is a JSON value
   * (theory state snapshot or details), inserted verbatim. */
  | {
      kind: "Theory";
      theory: string;
      kind_: string;
      message: string;
      lits: number[];
      data: string;
    };

// NOTE: the Rust variants TheoryClause / NewVar / Theory have a field named
// `kind`, which collides with the discriminant; it is called `kind_` here.

export class Tracer {
  enabled: boolean;
  limit: number;
  events: Event[];
  truncated: boolean;

  constructor(enabled: boolean, limit: number) {
    this.enabled = enabled;
    this.limit = limit;
    this.events = [];
    this.truncated = false;
  }

  static disabled(): Tracer {
    return new Tracer(false, 0);
  }

  static with_limit(limit: number): Tracer {
    return new Tracer(true, limit);
  }

  /// Record an event. The closure is only evaluated while tracing, so the
  /// untraced solver pays nothing for building event payloads.
  push(make: () => Event): void {
    if (!this.enabled) {
      return;
    }
    if (this.events.length >= this.limit) {
      this.truncated = true;
      this.enabled = false;
      return;
    }
    this.events.push(make());
  }
}

// ---------------------------------------------------------------- JSON output

function ints(out: { v: string }, xs: number[]): void {
  out.v += "[";
  for (let i = 0; i < xs.length; i++) {
    if (i > 0) {
      out.v += ",";
    }
    out.v += String(xs[i]);
  }
  out.v += "]";
}

export function json_string(out: { v: string }, s: string): void {
  let r = '"';
  for (const ch of s) {
    switch (ch) {
      case '"':
        r += '\\"';
        break;
      case "\\":
        r += "\\\\";
        break;
      case "\n":
        r += "\\n";
        break;
      case "\r":
        r += "\\r";
        break;
      case "\t":
        r += "\\t";
        break;
      default: {
        const c = ch.codePointAt(0)!;
        if (c < 0x20) {
          r += "\\u" + c.toString(16).padStart(4, "0");
        } else {
          r += ch;
        }
      }
    }
  }
  r += '"';
  out.v += r;
}

/** `Event::write_json` */
export function Event_write_json(e: Event, out: { v: string }): void {
  switch (e.kind) {
    case "Decide": {
      out.v += `{"type":"Decide","lit":${e.lit},"level":${e.level},"min_size":${e.min_size},"candidates":[`;
      e.candidates.forEach((c, i) => {
        if (i > 0) {
          out.v += ",";
        }
        out.v += `{"var":${c.var},"pos":${c.pos},"neg":${c.neg},"score":${c.score}}`;
      });
      out.v += "]";
      if (e.origin !== null) {
        out.v += `,"origin":{"by":`;
        json_string(out, e.origin.by);
        out.v += `,"why":`;
        json_string(out, e.origin.why);
        out.v += "}";
      }
      out.v += "}";
      break;
    }
    case "Propagate":
      out.v += `{"type":"Propagate","lit":${e.lit},"reason":${e.reason},"level":${e.level}}`;
      break;
    case "Conflict":
      out.v += `{"type":"Conflict","clause":${e.clause},"level":${e.level}}`;
      break;
    case "Resolve":
      out.v += `{"type":"Resolve","clause_a":`;
      ints(out, e.clause_a);
      if (e.clause_a_id !== null) {
        out.v += `,"clause_a_id":${e.clause_a_id}`;
      } else {
        out.v += `,"clause_a_id":null`;
      }
      out.v += `,"clause_b":${e.clause_b},"pivot":${e.pivot},"resolvent":`;
      ints(out, e.resolvent);
      out.v += "}";
      break;
    case "Learn":
      out.v += `{"type":"Learn","clause":${e.clause},"lits":`;
      ints(out, e.lits);
      out.v += `,"uip":${e.uip},"conflict_side":`;
      ints(out, e.conflict_side);
      out.v += `,"reason_side":`;
      ints(out, e.reason_side);
      out.v += `,"backjump_level":${e.backjump_level}}`;
      break;
    case "Backjump":
      out.v += `{"type":"Backjump","from":${e.from},"to":${e.to},"unassigned":`;
      ints(out, e.unassigned);
      out.v += "}";
      break;
    case "Result":
      out.v += `{"type":"Result","status":"${e.status}","model":`;
      ints(out, e.model);
      out.v += "}";
      break;
    case "TheoryClause":
      out.v += `{"type":"TheoryClause","clause":${e.clause},"lits":`;
      ints(out, e.lits);
      out.v += `,"kind":"${e.kind_}","theory":`;
      json_string(out, e.theory);
      out.v += `,"why":`;
      json_string(out, e.why);
      out.v += "}";
      break;
    case "NewVar":
      out.v += `{"type":"NewVar","var":${e.var},"label":`;
      json_string(out, e.label);
      out.v += `,"neg":`;
      json_string(out, e.neg);
      out.v += `,"kind":"${e.kind_}","theories":`;
      json_string(out, e.theories);
      out.v += "}";
      break;
    case "Theory":
      out.v += `{"type":"Theory","theory":`;
      json_string(out, e.theory);
      out.v += `,"kind":"${e.kind_}","message":`;
      json_string(out, e.message);
      out.v += `,"lits":`;
      ints(out, e.lits);
      out.v += `,"data":`;
      out.v += e.data.length === 0 ? "null" : e.data;
      out.v += "}";
      break;
  }
}
