//! Solver trace: the contract between the solver and the visualizer.
//!
//! Every event carries enough data for the UI to rebuild the full state by
//! replaying events from the start (see README, "Trace format").
//! Literals are DIMACS integers, variables are 1-based, clause ids are
//! 0-based indices into the solver's clause database (originals first,
//! learned clauses appended in learning order).

use std::fmt::Write;

#[derive(Debug, Clone, PartialEq)]
pub struct MomsCandidate {
    pub var: usize,
    pub pos: u32,
    pub neg: u32,
    pub score: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Event {
    Decide {
        lit: i64,
        level: usize,
        min_size: usize,
        candidates: Vec<MomsCandidate>,
    },
    Propagate {
        lit: i64,
        reason: usize,
        level: usize,
    },
    Conflict {
        clause: usize,
        level: usize,
    },
    Resolve {
        /// The clause being resolved (conflict clause on the first step,
        /// otherwise the previous resolvent).
        clause_a: Vec<i64>,
        /// Clause id of `clause_a` when it is a stored clause (first step).
        clause_a_id: Option<usize>,
        /// Reason clause of the pivot variable.
        clause_b: usize,
        pivot: usize,
        resolvent: Vec<i64>,
    },
    Learn {
        clause: usize,
        lits: Vec<i64>,
        uip: i64,
        /// Variables resolved away (conflict side of the cut, besides κ).
        conflict_side: Vec<usize>,
        /// Variables of the learned clause (reason side of the cut).
        reason_side: Vec<usize>,
        backjump_level: usize,
    },
    Backjump {
        from: usize,
        to: usize,
        unassigned: Vec<i64>,
    },
    Result {
        status: &'static str,
        model: Vec<i64>,
    },
}

pub struct Tracer {
    pub enabled: bool,
    pub limit: usize,
    pub events: Vec<Event>,
    pub truncated: bool,
}

impl Tracer {
    pub fn disabled() -> Tracer {
        Tracer {
            enabled: false,
            limit: 0,
            events: Vec::new(),
            truncated: false,
        }
    }

    pub fn with_limit(limit: usize) -> Tracer {
        Tracer {
            enabled: true,
            limit,
            events: Vec::new(),
            truncated: false,
        }
    }

    /// Record an event. The closure is only evaluated while tracing, so the
    /// untraced solver pays nothing for building event payloads.
    pub fn push(&mut self, make: impl FnOnce() -> Event) {
        if !self.enabled {
            return;
        }
        if self.events.len() >= self.limit {
            self.truncated = true;
            self.enabled = false;
            return;
        }
        self.events.push(make());
    }
}

// ---------------------------------------------------------------- JSON output

fn ints<T: std::fmt::Display>(out: &mut String, xs: &[T]) {
    out.push('[');
    for (i, x) in xs.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{x}");
    }
    out.push(']');
}

pub fn json_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

impl Event {
    pub fn write_json(&self, out: &mut String) {
        match self {
            Event::Decide {
                lit,
                level,
                min_size,
                candidates,
            } => {
                let _ = write!(
                    out,
                    r#"{{"type":"Decide","lit":{lit},"level":{level},"min_size":{min_size},"candidates":["#
                );
                for (i, c) in candidates.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    let _ = write!(
                        out,
                        r#"{{"var":{},"pos":{},"neg":{},"score":{}}}"#,
                        c.var, c.pos, c.neg, c.score
                    );
                }
                out.push_str("]}");
            }
            Event::Propagate { lit, reason, level } => {
                let _ = write!(
                    out,
                    r#"{{"type":"Propagate","lit":{lit},"reason":{reason},"level":{level}}}"#
                );
            }
            Event::Conflict { clause, level } => {
                let _ = write!(
                    out,
                    r#"{{"type":"Conflict","clause":{clause},"level":{level}}}"#
                );
            }
            Event::Resolve {
                clause_a,
                clause_a_id,
                clause_b,
                pivot,
                resolvent,
            } => {
                out.push_str(r#"{"type":"Resolve","clause_a":"#);
                ints(out, clause_a);
                match clause_a_id {
                    Some(id) => {
                        let _ = write!(out, r#","clause_a_id":{id}"#);
                    }
                    None => out.push_str(r#","clause_a_id":null"#),
                }
                let _ = write!(out, r#","clause_b":{clause_b},"pivot":{pivot},"resolvent":"#);
                ints(out, resolvent);
                out.push('}');
            }
            Event::Learn {
                clause,
                lits,
                uip,
                conflict_side,
                reason_side,
                backjump_level,
            } => {
                let _ = write!(out, r#"{{"type":"Learn","clause":{clause},"lits":"#);
                ints(out, lits);
                let _ = write!(out, r#","uip":{uip},"conflict_side":"#);
                ints(out, conflict_side);
                out.push_str(r#","reason_side":"#);
                ints(out, reason_side);
                let _ = write!(out, r#","backjump_level":{backjump_level}}}"#);
            }
            Event::Backjump {
                from,
                to,
                unassigned,
            } => {
                let _ = write!(out, r#"{{"type":"Backjump","from":{from},"to":{to},"unassigned":"#);
                ints(out, unassigned);
                out.push('}');
            }
            Event::Result { status, model } => {
                let _ = write!(out, r#"{{"type":"Result","status":"{status}","model":"#);
                ints(out, model);
                out.push('}');
            }
        }
    }
}
