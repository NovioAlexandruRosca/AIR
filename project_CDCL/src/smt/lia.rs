//! Linear Integer Arithmetic.
//!
//! - Atoms `t ⋈ c` are normalised to bounds on a single column: an input
//!   variable, or a slack variable `s = Σ aᵢxᵢ` for a linear form. Integer
//!   coefficients are divided by their gcd and the bound rounded
//!   (`2x - 2y ≤ 1` becomes `x - y ≤ 0`), which is how the GCD test shows up.
//! - `a = b` is defined by axioms over the two bound atoms `a ≤ b`, `a ≥ b`
//!   so that disequalities (non-convex) are handled by the SAT solver.
//! - Consistency of the asserted bounds over ℚ: general Simplex
//!   (Dutertre & de Moura) with Bland's rule; an infeasible row yields the
//!   bounds of that row as the explanation (a Farkas certificate).
//! - Integrality: branch and bound via splitting on demand: the final check
//!   asks the SAT solver to decide a new atom `x ≤ ⌊v⌋`.
//! - Bound propagation: a new bound on a column implies or refutes other
//!   atoms on the same column (`x ≤ 3` implies `x ≤ 5`).
//! - Nelson–Oppen: if both sides of an equality atom are fixed by bounds,
//!   the equality (or disequality) is propagated; `eq_hint` reports
//!   equalities in the current Simplex model to guide arrangement splits.

use super::rat::{div_ceil, div_floor, gcd, Rat};
use super::term::{Op, TermId, Terms, TheoryId, Value, BOOL};
use super::theory::{Check, Ctx, Implied, Inconsistent, Theory};
use crate::lit::Lit;
use crate::trace::json_string;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write;

const MAX_BRANCHES: usize = 5_000;
const MAX_PIVOTS_PER_CHECK: usize = 100_000;
const SNAPSHOT_COLS: usize = 200;
/// Limits of the per-check record shown by the playground.
const RECORD_CONSTRAINTS: usize = 60;
const RECORD_STEPS: usize = 40;

#[derive(Clone, Copy, Debug)]
struct Bound {
    val: Rat,
    lit: Lit,
    level: usize,
}

struct Col {
    name: String,
    /// Input (or purification) variable; None for slack columns.
    term: Option<TermId>,
    value: Rat,
    lower: Option<Bound>,
    upper: Option<Bound>,
    /// Row index when the column is basic.
    row: Option<usize>,
}

/// `basic = Σ coeffs[j] · x_j` over non-basic columns.
struct Row {
    basic: usize,
    coeffs: BTreeMap<usize, Rat>,
}

enum Atom {
    /// `col ≤ k` (upper) or `col ≥ k` (lower).
    Bound {
        var: usize,
        col: usize,
        upper: bool,
        k: i128,
    },
    /// `a = b`; its meaning is given by axioms. Columns kept when both
    /// sides are variables, for Nelson–Oppen equality propagation.
    Eq {
        var: usize,
        cols: Option<(usize, usize)>,
    },
    /// Variable-free atom, fixed by an axiom.
    Const,
}

enum Undo {
    Bound {
        level: usize,
        col: usize,
        upper: bool,
        old: Option<Bound>,
    },
    Assign {
        level: usize,
        atom: usize,
    },
}

impl Undo {
    fn level(&self) -> usize {
        match self {
            Undo::Bound { level, .. } | Undo::Assign { level, .. } => *level,
        }
    }
}

struct PendingProp {
    implied: Lit,
    because: Lit,
    level: usize,
}

/// What one check did, for the playground's picture of Simplex: the
/// asserted bounds in order, and after every pivot the values of the input
/// variables and the whole tableau.
#[derive(Default)]
struct CheckRecord {
    /// (literal, column, is_upper, bound)
    constraints: Vec<(Lit, usize, bool, i128)>,
    steps: Vec<RecStep>,
    conflict: Option<Inconsistent>,
    /// basic variable of the row Simplex got stuck on
    stuck: Option<String>,
}

struct RecStep {
    note: String,
    /// values of the input columns
    values: Vec<Rat>,
    /// the pivot that led here: (leaving basic variable, entering variable)
    pivot: Option<(String, String)>,
    /// rows `basic = expr`
    rows: Vec<(String, String)>,
    cols: Vec<RecCol>,
}

/// A tableau column at one recorded step: (name, value, lower, upper, basic).
type RecCol = (String, Rat, Option<Rat>, Option<Rat>, bool);

struct PendingConflict {
    lits: Vec<Lit>,
    why: String,
    level: usize,
}

pub struct Lia {
    me: TheoryId,
    int: usize,
    atoms: Vec<Atom>,
    atom_of_var: HashMap<usize, usize>,
    term_of_var: HashMap<usize, TermId>,
    assigned: Vec<Option<bool>>,
    cols: Vec<Col>,
    rows: Vec<Row>,
    col_of_term: HashMap<TermId, usize>,
    slack_of_form: HashMap<Vec<(usize, i128)>, usize>,
    col_atoms: Vec<Vec<usize>>,
    undo: Vec<Undo>,
    pending_conflict: Option<PendingConflict>,
    pending_props: Vec<PendingProp>,
    branches: usize,
    changed: bool,
    /// Last conflict explanation, for the snapshot.
    last_event: Option<String>,
    /// Slack column -> its linear form over input columns.
    form_of_slack: HashMap<usize, Vec<(usize, i128)>>,
    /// Record checks (only while tracing).
    record: bool,
    last_check: Option<CheckRecord>,
}

impl Default for Lia {
    fn default() -> Self {
        Lia::new()
    }
}

impl Lia {
    pub fn new() -> Lia {
        Lia {
            me: 0,
            int: 0,
            atoms: Vec::new(),
            atom_of_var: HashMap::new(),
            term_of_var: HashMap::new(),
            assigned: Vec::new(),
            cols: Vec::new(),
            rows: Vec::new(),
            col_of_term: HashMap::new(),
            slack_of_form: HashMap::new(),
            col_atoms: Vec::new(),
            undo: Vec::new(),
            pending_conflict: None,
            pending_props: Vec::new(),
            branches: 0,
            changed: true,
            last_event: None,
            form_of_slack: HashMap::new(),
            record: false,
            last_check: None,
        }
    }

    fn lit_label(&self, terms: &Terms, l: Lit) -> String {
        match self.term_of_var.get(&l.var()) {
            Some(&t) if l.is_positive() => terms.display(t),
            Some(&t) => terms.display_neg(t),
            None => format!("literal {l}"),
        }
    }

    fn col_for_term(&mut self, terms: &Terms, t: TermId) -> usize {
        if let Some(&c) = self.col_of_term.get(&t) {
            return c;
        }
        let c = self.new_col(terms.display(t), Some(t));
        self.col_of_term.insert(t, c);
        c
    }

    fn new_col(&mut self, name: String, term: Option<TermId>) -> usize {
        self.cols.push(Col {
            name,
            term,
            value: Rat::ZERO,
            lower: None,
            upper: None,
            row: None,
        });
        self.col_atoms.push(Vec::new());
        self.cols.len() - 1
    }

    /// Slack column for `Σ a·x` (form sorted by column).
    fn slack_for(&mut self, form: Vec<(usize, i128)>) -> usize {
        if let Some(&s) = self.slack_of_form.get(&form) {
            return s;
        }
        let mut name = String::new();
        for (i, &(c, a)) in form.iter().enumerate() {
            let v = &self.cols[c].name;
            match (i, a) {
                (0, 1) => name.push_str(v),
                (0, -1) => {
                    let _ = write!(name, "-{v}");
                }
                (0, a) => {
                    let _ = write!(name, "{a}·{v}");
                }
                (_, 1) => {
                    let _ = write!(name, " + {v}");
                }
                (_, -1) => {
                    let _ = write!(name, " - {v}");
                }
                (_, a) if a < 0 => {
                    let _ = write!(name, " - {}·{v}", -a);
                }
                (_, a) => {
                    let _ = write!(name, " + {a}·{v}");
                }
            }
        }
        // Express the form over the current non-basic columns.
        let mut coeffs: BTreeMap<usize, Rat> = BTreeMap::new();
        let mut value = Rat::ZERO;
        for &(c, a) in &form {
            let a = Rat::int(a);
            value = value + a * self.cols[c].value;
            match self.cols[c].row {
                Some(r) => {
                    for (&m, &b) in &self.rows[r].coeffs {
                        let e = coeffs.entry(m).or_insert(Rat::ZERO);
                        *e = *e + a * b;
                    }
                }
                None => {
                    let e = coeffs.entry(c).or_insert(Rat::ZERO);
                    *e = *e + a;
                }
            }
        }
        coeffs.retain(|_, v| !v.is_zero());
        let s = self.new_col(name, None);
        self.cols[s].value = value;
        self.cols[s].row = Some(self.rows.len());
        self.rows.push(Row { basic: s, coeffs });
        self.form_of_slack.insert(s, form.clone());
        self.slack_of_form.insert(form, s);
        s
    }

    fn push_atom(&mut self, var: usize, atom: Atom) -> usize {
        let idx = self.atoms.len();
        if let Atom::Bound { col, .. } = atom {
            self.col_atoms[col].push(idx);
        }
        self.atoms.push(atom);
        self.assigned.push(None);
        self.atom_of_var.insert(var, idx);
        idx
    }

    // ------------------------------------------------------------ bounds

    fn conflict(&mut self, lits: Vec<Lit>, why: String, level: usize) {
        if self.pending_conflict.is_none() {
            self.pending_conflict = Some(PendingConflict { lits, why, level });
        }
    }

    fn assert_upper(&mut self, col: usize, v: Rat, lit: Lit, level: usize) {
        if self.cols[col].upper.is_some_and(|u| u.val <= v) {
            return;
        }
        if let Some(l) = self.cols[col].lower {
            if v < l.val {
                let why = format!(
                    "{} cannot be ≤ {v} and ≥ {} at the same time",
                    self.cols[col].name, l.val
                );
                self.conflict(vec![lit, l.lit], why, level.max(l.level));
                return;
            }
        }
        let old = self.cols[col].upper;
        self.undo.push(Undo::Bound {
            level,
            col,
            upper: true,
            old,
        });
        self.cols[col].upper = Some(Bound { val: v, lit, level });
        if self.cols[col].row.is_none() && self.cols[col].value > v {
            self.update(col, v);
        }
    }

    fn assert_lower(&mut self, col: usize, v: Rat, lit: Lit, level: usize) {
        if self.cols[col].lower.is_some_and(|l| l.val >= v) {
            return;
        }
        if let Some(u) = self.cols[col].upper {
            if v > u.val {
                let why = format!(
                    "{} cannot be ≥ {v} and ≤ {} at the same time",
                    self.cols[col].name, u.val
                );
                self.conflict(vec![lit, u.lit], why, level.max(u.level));
                return;
            }
        }
        let old = self.cols[col].lower;
        self.undo.push(Undo::Bound {
            level,
            col,
            upper: false,
            old,
        });
        self.cols[col].lower = Some(Bound { val: v, lit, level });
        if self.cols[col].row.is_none() && self.cols[col].value < v {
            self.update(col, v);
        }
    }

    /// Atoms on the same column decided by the new bound `col ≤ b` / `col ≥ b`.
    fn unate(&mut self, col: usize, is_upper: bool, b: i128, lit: Lit, level: usize, me: usize) {
        for &j in &self.col_atoms[col] {
            if j == me || self.assigned[j].is_some() {
                continue;
            }
            if let Atom::Bound { var, upper, k, .. } = self.atoms[j] {
                let implied = match (is_upper, upper) {
                    (true, true) if b <= k => Some(true),
                    (true, false) if b < k => Some(false),
                    (false, false) if b >= k => Some(true),
                    (false, true) if b > k => Some(false),
                    _ => None,
                };
                if let Some(v) = implied {
                    self.pending_props.push(PendingProp {
                        implied: Lit::new(var, v),
                        because: lit,
                        level,
                    });
                }
            }
        }
    }

    // ------------------------------------------------------------ simplex

    fn update(&mut self, j: usize, v: Rat) {
        let delta = v - self.cols[j].value;
        for r in 0..self.rows.len() {
            if let Some(&a) = self.rows[r].coeffs.get(&j) {
                let b = self.rows[r].basic;
                self.cols[b].value = self.cols[b].value + a * delta;
            }
        }
        self.cols[j].value = v;
    }

    fn pivot_and_update(&mut self, r: usize, j: usize, v: Rat) {
        let i = self.rows[r].basic;
        let a_ij = self.rows[r].coeffs[&j];
        let theta = (v - self.cols[i].value) / a_ij;
        self.cols[i].value = v;
        self.cols[j].value = self.cols[j].value + theta;
        for k in 0..self.rows.len() {
            if k == r {
                continue;
            }
            if let Some(&a) = self.rows[k].coeffs.get(&j) {
                let b = self.rows[k].basic;
                self.cols[b].value = self.cols[b].value + a * theta;
            }
        }
        self.pivot(r, j);
    }

    /// Make `j` basic in row `r` (whose basic variable leaves).
    fn pivot(&mut self, r: usize, j: usize) {
        let i = self.rows[r].basic;
        let mut coeffs = std::mem::take(&mut self.rows[r].coeffs);
        let a = coeffs.remove(&j).expect("entering column is in the row");
        // i = a·j + Σ c·k   ⇒   j = (1/a)·i - Σ (c/a)·k
        let mut new: BTreeMap<usize, Rat> = BTreeMap::new();
        new.insert(i, Rat::ONE / a);
        for (k, c) in coeffs {
            new.insert(k, -(c / a));
        }
        for k in 0..self.rows.len() {
            if k == r {
                continue;
            }
            if let Some(c) = self.rows[k].coeffs.remove(&j) {
                for (&m, &b) in &new {
                    let e = self.rows[k].coeffs.entry(m).or_insert(Rat::ZERO);
                    *e = *e + c * b;
                }
                self.rows[k].coeffs.retain(|_, v| !v.is_zero());
            }
        }
        self.rows[r] = Row {
            basic: j,
            coeffs: new,
        };
        self.cols[i].row = None;
        self.cols[j].row = Some(r);
    }

    /// Bland-rule Simplex. Err(conflict) when the bounds are infeasible over ℚ.
    fn simplex(&mut self, terms: &Terms) -> Result<(), Inconsistent> {
        for _ in 0..MAX_PIVOTS_PER_CHECK {
            let mut viol: Option<(usize, usize, bool)> = None;
            for (r, row) in self.rows.iter().enumerate() {
                let i = row.basic;
                let c = &self.cols[i];
                let below = c.lower.is_some_and(|l| c.value < l.val);
                let above = c.upper.is_some_and(|u| c.value > u.val);
                if (below || above) && viol.is_none_or(|(vi, _, _)| i < vi) {
                    viol = Some((i, r, below));
                }
            }
            let Some((i, r, below)) = viol else {
                return Ok(());
            };
            let mut entering = None;
            for (&j, &a) in &self.rows[r].coeffs {
                let cj = &self.cols[j];
                let can_inc = cj.upper.is_none_or(|u| cj.value < u.val);
                let can_dec = cj.lower.is_none_or(|l| cj.value > l.val);
                let positive = a > Rat::ZERO;
                let ok = if below {
                    (positive && can_inc) || (!positive && can_dec)
                } else {
                    (!positive && can_inc) || (positive && can_dec)
                };
                if ok {
                    entering = Some(j);
                    break;
                }
            }
            match entering {
                None => {
                    let stuck = self.cols[i].name.clone();
                    if let Some(rec) = &mut self.last_check {
                        rec.stuck = Some(stuck);
                    }
                    return Err(self.explain_row(terms, r, below));
                }
                Some(j) => {
                    let target = if below {
                        self.cols[i].lower.unwrap().val
                    } else {
                        self.cols[i].upper.unwrap().val
                    };
                    let note = self.record.then(|| {
                        format!(
                            "{} = {} but must be {} {target}: change {} until it is (pivot)",
                            self.col_ref(i),
                            self.cols[i].value,
                            if below { "≥" } else { "≤" },
                            self.cols[j].name
                        )
                    });
                    let pivot = (self.cols[i].name.clone(), self.cols[j].name.clone());
                    self.pivot_and_update(r, j, target);
                    if let Some(note) = note {
                        self.record_step(note, Some(pivot));
                    }
                }
            }
        }
        Ok(())
    }

    /// Row `r` cannot reach its bound: the bound of the basic variable and
    /// the blocking bounds of the row's variables are jointly infeasible.
    fn explain_row(&self, terms: &Terms, r: usize, below: bool) -> Inconsistent {
        let row = &self.rows[r];
        let i = row.basic;
        let own = if below {
            self.cols[i].lower.unwrap()
        } else {
            self.cols[i].upper.unwrap()
        };
        let mut lits = vec![own.lit];
        let mut extreme = Rat::ZERO;
        let mut used = Vec::new();
        for (n, (&j, &a)) in row.coeffs.iter().enumerate() {
            let b = if below == (a > Rat::ZERO) {
                self.cols[j].upper.unwrap()
            } else {
                self.cols[j].lower.unwrap()
            };
            extreme = extreme + a * b.val;
            if !lits.contains(&b.lit) {
                lits.push(b.lit);
            }
            used.push(self.lit_label(terms, b.lit));
            let _ = n;
        }
        let expr = self.row_expr(&row.coeffs);
        let why = if below {
            format!(
                "Simplex row {} = {expr}: it must be ≥ {} (from {}), but with {} it is at most {extreme}",
                self.col_ref(i),
                own.val,
                self.lit_label(terms, own.lit),
                used.join(", ")
            )
        } else {
            format!(
                "Simplex row {} = {expr}: it must be ≤ {} (from {}), but with {} it is at least {extreme}",
                self.col_ref(i),
                own.val,
                self.lit_label(terms, own.lit),
                used.join(", ")
            )
        };
        Inconsistent { lits, why }
    }

    /// Column name, parenthesised when it is a slack (a linear form).
    fn col_ref(&self, j: usize) -> String {
        if self.cols[j].term.is_none() {
            format!("({})", self.cols[j].name)
        } else {
            self.cols[j].name.clone()
        }
    }

    /// `Σ a·x` with readable signs: `x - (y - z) + 1/2·w`.
    fn row_expr(&self, coeffs: &BTreeMap<usize, Rat>) -> String {
        let mut out = String::new();
        for (n, (&j, &a)) in coeffs.iter().enumerate() {
            let neg = a < Rat::ZERO;
            let mag = if neg { -a } else { a };
            match (n, neg) {
                (0, true) => out.push('-'),
                (0, false) => {}
                (_, true) => out.push_str(" - "),
                (_, false) => out.push_str(" + "),
            }
            if mag != Rat::ONE {
                let _ = write!(out, "{mag}·");
            }
            out.push_str(&self.col_ref(j));
        }
        out
    }

    fn input_values(&self) -> Vec<Rat> {
        self.cols
            .iter()
            .filter(|c| c.term.is_some())
            .map(|c| c.value)
            .collect()
    }

    fn record_step(&mut self, note: String, pivot: Option<(String, String)>) {
        if self.last_check.as_ref().is_none_or(|rec| rec.steps.len() >= RECORD_STEPS) {
            return;
        }
        let values = self.input_values();
        let rows = self
            .rows
            .iter()
            .take(SNAPSHOT_COLS)
            .map(|r| (self.cols[r.basic].name.clone(), self.row_expr(&r.coeffs)))
            .collect();
        let cols = self
            .cols
            .iter()
            .take(SNAPSHOT_COLS)
            .map(|c| (c.name.clone(), c.value, c.lower.map(|b| b.val), c.upper.map(|b| b.val), c.row.is_some()))
            .collect();
        if let Some(rec) = &mut self.last_check {
            rec.steps.push(RecStep { note, values, pivot, rows, cols });
        }
    }

    /// Start the record of a check: the asserted bounds, in assertion order.
    fn start_record(&mut self) {
        let mut rec = CheckRecord::default();
        for u in &self.undo {
            let Undo::Assign { atom, .. } = *u else {
                continue;
            };
            let (Atom::Bound { var, col, upper, k }, Some(value)) =
                (&self.atoms[atom], self.assigned[atom])
            else {
                continue;
            };
            let (is_upper, b) = match (*upper, value) {
                (true, true) => (true, *k),
                (true, false) => (false, k + 1),
                (false, true) => (false, *k),
                (false, false) => (true, k - 1),
            };
            if rec.constraints.len() < RECORD_CONSTRAINTS {
                rec.constraints
                    .push((Lit::new(*var, value), *col, is_upper, b));
            }
        }
        self.last_check = Some(rec);
        self.record_step("start: the current values".into(), None);
    }

    fn record_json(&self, terms: &Terms, s: &mut String) {
        let Some(rec) = &self.last_check else {
            s.push_str("null");
            return;
        };
        s.push_str("{\"vars\":[");
        for (i, c) in self.cols.iter().filter(|c| c.term.is_some()).enumerate() {
            if i > 0 {
                s.push(',');
            }
            json_string(s, &c.name);
        }
        s.push_str("],\"constraints\":[");
        for (i, &(lit, col, upper, b)) in rec.constraints.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let _ = write!(s, "{{\"lit\":{},\"label\":", lit.to_dimacs());
            json_string(s, &self.lit_label(terms, lit));
            s.push_str(",\"form\":[");
            let form = match self.form_of_slack.get(&col) {
                Some(f) => f.clone(),
                None => vec![(col, 1)],
            };
            for (j, (c, a)) in form.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                s.push('[');
                json_string(s, &self.cols[*c].name);
                let _ = write!(s, ",{a}]");
            }
            let _ = write!(
                s,
                "],\"op\":\"{}\",\"bound\":{b}}}",
                if upper { "<=" } else { ">=" }
            );
        }
        s.push_str("],\"steps\":[");
        for (i, st) in rec.steps.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            s.push_str("{\"note\":");
            json_string(s, &st.note);
            s.push_str(",\"values\":[");
            for (j, v) in st.values.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                let _ = write!(s, "\"{v}\"");
            }
            s.push_str("],\"pivot\":");
            match &st.pivot {
                Some((leave, enter)) => {
                    s.push('[');
                    json_string(s, leave);
                    s.push(',');
                    json_string(s, enter);
                    s.push(']');
                }
                None => s.push_str("null"),
            }
            s.push_str(",\"rows\":[");
            for (j, (basic, expr)) in st.rows.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                s.push('[');
                json_string(s, basic);
                s.push(',');
                json_string(s, expr);
                s.push(']');
            }
            s.push_str("],\"cols\":[");
            for (j, (name, value, lo, hi, basic)) in st.cols.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                s.push_str("{\"name\":");
                json_string(s, name);
                let opt = |r: &Option<Rat>| r.map_or("null".to_string(), |v| format!("\"{v}\""));
                let _ = write!(s, ",\"value\":\"{value}\",\"lo\":{},\"hi\":{},\"basic\":{basic}}}", opt(lo), opt(hi));
            }
            s.push_str("]}");
        }
        s.push_str("],\"stuck\":");
        match &rec.stuck {
            Some(b) => json_string(s, b),
            None => s.push_str("null"),
        }
        s.push_str(",\"conflict\":");
        match &rec.conflict {
            Some(c) => {
                s.push_str("{\"lits\":[");
                for (j, l) in c.lits.iter().enumerate() {
                    if j > 0 {
                        s.push(',');
                    }
                    let _ = write!(s, "{}", l.to_dimacs());
                }
                s.push_str("],\"why\":");
                json_string(s, &c.why);
                s.push('}');
            }
            None => s.push_str("null"),
        }
        s.push('}');
    }

    fn fixed(&self, c: usize) -> Option<(Rat, Lit, Lit)> {
        let col = &self.cols[c];
        match (col.lower, col.upper) {
            (Some(l), Some(u)) if l.val == u.val => Some((l.val, l.lit, u.lit)),
            _ => None,
        }
    }
}

/// Integer value of a variable-free term, if it is one.
fn const_value(terms: &Terms, t: TermId) -> Option<i128> {
    let n = terms.node(t);
    match &n.op {
        Op::Num(v) => Some(*v),
        Op::App(s) => {
            let vals: Option<Vec<i128>> = n.args.iter().map(|&a| const_value(terms, a)).collect();
            let vals = vals?;
            match s.as_str() {
                "+" => vals.iter().try_fold(0i128, |acc, v| acc.checked_add(*v)),
                "*" => vals.iter().try_fold(1i128, |acc, v| acc.checked_mul(*v)),
                "-" if vals.len() == 1 => vals[0].checked_neg(),
                "-" => vals[1..]
                    .iter()
                    .try_fold(vals[0], |acc, v| acc.checked_sub(*v)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Add `c · t` to the linear form `acc + k`.
fn linearize(
    terms: &Terms,
    t: TermId,
    c: i128,
    acc: &mut BTreeMap<TermId, i128>,
    k: &mut i128,
) -> Result<(), String> {
    let overflow = || "integer overflow while normalising a linear term".to_string();
    let n = terms.node(t);
    match &n.op {
        Op::Num(v) => {
            *k = k
                .checked_add(c.checked_mul(*v).ok_or_else(overflow)?)
                .ok_or_else(overflow)?
        }
        Op::App(s) if s == "+" => {
            for &a in &n.args {
                linearize(terms, a, c, acc, k)?;
            }
        }
        Op::App(s) if s == "-" => {
            if n.args.len() == 1 {
                linearize(terms, n.args[0], -c, acc, k)?;
            } else {
                linearize(terms, n.args[0], c, acc, k)?;
                for &a in &n.args[1..] {
                    linearize(terms, a, -c, acc, k)?;
                }
            }
        }
        Op::App(s) if s == "*" => {
            let mut factor = c;
            let mut var_part = None;
            for &a in &n.args {
                match const_value(terms, a) {
                    Some(v) => factor = factor.checked_mul(v).ok_or_else(overflow)?,
                    None if var_part.is_none() => var_part = Some(a),
                    None => {
                        return Err(format!(
                            "non-linear term {}: LIA only allows multiplication by constants",
                            terms.display(t)
                        ))
                    }
                }
            }
            match var_part {
                None => *k = k.checked_add(factor).ok_or_else(overflow)?,
                Some(a) => linearize(terms, a, factor, acc, k)?,
            }
        }
        // Constants, and alien terms (which purification replaced by
        // constants anyway), are columns.
        _ => {
            let e = acc.entry(t).or_insert(0);
            *e = e.checked_add(c).ok_or_else(overflow)?;
        }
    }
    Ok(())
}

impl Theory for Lia {
    fn name(&self) -> &'static str {
        "LIA"
    }

    fn init(&mut self, terms: &mut Terms, me: TheoryId) {
        self.me = me;
        self.int = terms.add_sort("Int", Some(me));
        for s in ["+", "-", "*", "<=", "<", ">=", ">"] {
            terms.add_fun(s, me);
        }
    }

    fn mk_app(&self, sym: &str, args: Vec<TermId>, terms: &mut Terms) -> Result<TermId, String> {
        for &a in &args {
            if terms.sort(a) != self.int {
                return Err(format!(
                    "'{sym}' expects Int arguments, got {} : {}",
                    terms.display(a),
                    terms.sort_name(terms.sort(a))
                ));
            }
        }
        match sym {
            "+" | "*" if args.len() >= 2 => Ok(terms.app(sym, args, self.int)),
            "-" if !args.is_empty() => {
                // Fold negative numerals: (- 3) is the literal -3.
                if args.len() == 1 {
                    if let Op::Num(v) = terms.node(args[0]).op {
                        return Ok(terms.num(-v, self.int));
                    }
                }
                Ok(terms.app(sym, args, self.int))
            }
            "<=" | "<" | ">=" | ">" if args.len() == 2 => Ok(terms.app(sym, args, BOOL)),
            "<=" | "<" | ">=" | ">" => Err(format!("'{sym}' takes exactly two arguments")),
            _ => Err(format!("'{sym}' needs at least two arguments")),
        }
    }

    fn register_atom(&mut self, var: usize, atom: TermId, ctx: &mut Ctx) -> Result<(), String> {
        let node = ctx.terms.node(atom).clone();
        let sym = match &node.op {
            Op::App(s) if node.args.len() == 2 => s.clone(),
            _ => return Err(format!("LIA cannot interpret {}", ctx.terms.display(atom))),
        };
        let (a, b) = (node.args[0], node.args[1]);
        let mut acc = BTreeMap::new();
        let mut k = 0i128;
        linearize(ctx.terms, a, 1, &mut acc, &mut k)?;
        linearize(ctx.terms, b, -1, &mut acc, &mut k)?;
        acc.retain(|_, c| *c != 0);
        self.term_of_var.insert(var, atom);
        self.changed = true;
        let label = ctx.terms.display(atom);

        if sym == "=" {
            if acc.is_empty() {
                self.push_atom(var, Atom::Const);
                let truth = k == 0;
                ctx.axiom(
                    vec![Lit::new(var, truth)],
                    "LIA",
                    format!("{label} is {truth} (no variables)"),
                );
                return Ok(());
            }
            let le_t = ctx.terms.app("<=", vec![a, b], BOOL);
            let ge_t = ctx.terms.app(">=", vec![a, b], BOOL);
            let le = Lit::new(ctx.atom(le_t), true);
            let ge = Lit::new(ctx.atom(ge_t), true);
            let e = Lit::new(var, true);
            let why = format!(
                "LIA definition: {label} ⇔ {} ∧ {}",
                ctx.terms.display(le_t),
                ctx.terms.display(ge_t)
            );
            ctx.axiom(vec![!e, le], "LIA", why.clone());
            ctx.axiom(vec![!e, ge], "LIA", why.clone());
            ctx.axiom(vec![e, !le, !ge], "LIA", why);
            let cols = if ctx.terms.is_var(a) && ctx.terms.is_var(b) {
                Some((
                    self.col_for_term(ctx.terms, a),
                    self.col_for_term(ctx.terms, b),
                ))
            } else {
                None
            };
            self.push_atom(var, Atom::Eq { var, cols });
            return Ok(());
        }

        // Σ acc·x + k ⋈ 0  ⇒  Σ acc·x ≤ bound (upper) or ≥ bound (lower)
        let (upper, bound) = match sym.as_str() {
            "<=" => (true, -k),
            "<" => (true, -k - 1),
            ">=" => (false, -k),
            ">" => (false, -k + 1),
            _ => return Err(format!("LIA cannot interpret {label}")),
        };
        if acc.is_empty() {
            self.push_atom(var, Atom::Const);
            let truth = if upper { 0 <= bound } else { 0 >= bound };
            ctx.axiom(
                vec![Lit::new(var, truth)],
                "LIA",
                format!("{label} is {truth} (no variables)"),
            );
            return Ok(());
        }
        // Divide by the gcd of the coefficients and round the bound
        // (sound over the integers: the left side is a multiple of g).
        let g = acc.values().fold(0, |g, &c| gcd(g, c));
        let mut form: Vec<(TermId, i128)> = acc.into_iter().map(|(t, c)| (t, c / g)).collect();
        let mut bound = if upper {
            div_floor(bound, g)
        } else {
            div_ceil(bound, g)
        };
        let mut upper = upper;
        if form[0].1 < 0 {
            for e in form.iter_mut() {
                e.1 = -e.1;
            }
            upper = !upper;
            bound = -bound;
        }
        let col = if form.len() == 1 {
            self.col_for_term(ctx.terms, form[0].0)
        } else {
            let mut by_col: Vec<(usize, i128)> = form
                .iter()
                .map(|&(t, c)| (self.col_for_term(ctx.terms, t), c))
                .collect();
            by_col.sort();
            self.slack_for(by_col)
        };
        self.push_atom(
            var,
            Atom::Bound {
                var,
                col,
                upper,
                k: bound,
            },
        );
        Ok(())
    }

    fn assert_lit(&mut self, var: usize, value: bool, level: usize) {
        let Some(&idx) = self.atom_of_var.get(&var) else {
            return;
        };
        if self.assigned[idx].is_some() {
            return;
        }
        self.assigned[idx] = Some(value);
        self.undo.push(Undo::Assign { level, atom: idx });
        self.changed = true;
        if let Atom::Bound { col, upper, k, .. } = self.atoms[idx] {
            let lit = Lit::new(var, value);
            // A false atom is the integer complement: ¬(x ≤ k) is x ≥ k+1.
            let (is_upper, b) = match (upper, value) {
                (true, true) => (true, k),
                (true, false) => (false, k + 1),
                (false, true) => (false, k),
                (false, false) => (true, k - 1),
            };
            if is_upper {
                self.assert_upper(col, Rat::int(b), lit, level);
            } else {
                self.assert_lower(col, Rat::int(b), lit, level);
            }
            self.unate(col, is_upper, b, lit, level, idx);
        }
    }

    fn backtrack(&mut self, level: usize) {
        while let Some(u) = self.undo.last() {
            if u.level() <= level {
                break;
            }
            match self.undo.pop().unwrap() {
                Undo::Bound {
                    col, upper, old, ..
                } => {
                    if upper {
                        self.cols[col].upper = old;
                    } else {
                        self.cols[col].lower = old;
                    }
                }
                Undo::Assign { atom, .. } => self.assigned[atom] = None,
            }
        }
        if self
            .pending_conflict
            .as_ref()
            .is_some_and(|c| c.level > level)
        {
            self.pending_conflict = None;
        }
        self.pending_props.retain(|p| p.level <= level);
        self.changed = true;
    }

    fn check(&mut self, ctx: &mut Ctx, final_check: bool) -> Check {
        let mut out = Check::default();
        if self.record {
            self.start_record();
        }
        if let Some(c) = &self.pending_conflict {
            self.last_event = Some(c.why.clone());
            let conflict = Inconsistent {
                lits: c.lits.clone(),
                why: c.why.clone(),
            };
            if let Some(rec) = &mut self.last_check {
                rec.conflict = Some(conflict.clone());
            }
            out.conflict = Some(conflict);
            return out;
        }
        if let Err(conflict) = self.simplex(ctx.terms) {
            self.last_event = Some(conflict.why.clone());
            if let Some(rec) = &mut self.last_check {
                rec.conflict = Some(conflict.clone());
            }
            out.conflict = Some(conflict);
            return out;
        }

        for p in std::mem::take(&mut self.pending_props) {
            let idx = self.atom_of_var[&p.implied.var()];
            if self.assigned[idx].is_some() {
                continue;
            }
            let (from, to) = (
                self.lit_label(ctx.terms, p.because),
                self.lit_label(ctx.terms, p.implied),
            );
            let why = if from == to {
                format!("bound propagation: {from} — another atom states the same bound, so it gets the same value")
            } else {
                format!("bound propagation: {from} implies {to}")
            };
            out.propagations.push(Implied {
                implied: p.implied,
                because: vec![p.because],
                why,
            });
        }

        // Nelson–Oppen: equalities between variables fixed by their bounds.
        for idx in 0..self.atoms.len() {
            if self.assigned[idx].is_some() {
                continue;
            }
            if let Atom::Eq {
                var,
                cols: Some((ca, cb)),
            } = self.atoms[idx]
            {
                if let (Some((va, la, ua)), Some((vb, lb, ub))) = (self.fixed(ca), self.fixed(cb)) {
                    let mut because = vec![la, ua, lb, ub];
                    because.dedup();
                    because.sort();
                    because.dedup();
                    let why = format!(
                        "{} and {} are fixed to {va} and {vb} by their bounds, so {}",
                        self.cols[ca].name,
                        self.cols[cb].name,
                        self.lit_label(ctx.terms, Lit::new(var, va == vb))
                    );
                    out.propagations.push(Implied {
                        implied: Lit::new(var, va == vb),
                        because,
                        why,
                    });
                }
            }
        }
        if !out.propagations.is_empty() || !final_check {
            return out;
        }

        // Branch and bound: the first input column with a fractional value.
        let frac = self
            .cols
            .iter()
            .position(|c| c.term.is_some() && !c.value.is_int());
        if let Some(c) = frac {
            if self.branches >= MAX_BRANCHES {
                out.unknown = Some(format!(
                    "LIA: gave up after {MAX_BRANCHES} branch-and-bound splits"
                ));
                return out;
            }
            self.branches += 1;
            let v = self.cols[c].value;
            let t = self.cols[c].term.unwrap();
            let k = ctx.terms.num(v.floor(), self.int);
            let atom = ctx.terms.app("<=", vec![t, k], BOOL);
            let lit = ctx.lit(atom, true);
            let why = format!(
                "branch and bound: the rational solution has {} = {v}, which is not an integer; every integer solution has {} ≤ {} or {} ≥ {}",
                self.cols[c].name,
                self.cols[c].name,
                v.floor(),
                self.cols[c].name,
                v.ceil()
            );
            self.last_event = Some(why.clone());
            out.split = Some((lit, why));
        }
        out
    }

    fn eq_hint(&self, a: TermId, b: TermId) -> Option<bool> {
        let ca = *self.col_of_term.get(&a)?;
        let cb = *self.col_of_term.get(&b)?;
        Some(self.cols[ca].value == self.cols[cb].value)
    }

    fn model(&mut self, _terms: &mut Terms, known: &mut HashMap<TermId, Value>) {
        for c in &self.cols {
            if let Some(t) = c.term {
                known.insert(t, Value::Int(c.value.floor()));
            }
        }
    }

    fn snapshot(&self, terms: &Terms) -> String {
        let mut s = String::from("{\"cols\":[");
        for (i, c) in self.cols.iter().take(SNAPSHOT_COLS).enumerate() {
            if i > 0 {
                s.push(',');
            }
            s.push_str("{\"name\":");
            json_string(&mut s, &c.name);
            let _ = write!(
                s,
                ",\"slack\":{},\"basic\":{},\"value\":\"{}\",\"int\":{}",
                c.term.is_none(),
                c.row.is_some(),
                c.value,
                c.value.is_int()
            );
            match c.lower {
                Some(b) => {
                    let _ = write!(s, ",\"lo\":\"{}\",\"loLit\":{}", b.val, b.lit.to_dimacs());
                }
                None => s.push_str(",\"lo\":null,\"loLit\":null"),
            }
            match c.upper {
                Some(b) => {
                    let _ = write!(s, ",\"hi\":\"{}\",\"hiLit\":{}", b.val, b.lit.to_dimacs());
                }
                None => s.push_str(",\"hi\":null,\"hiLit\":null"),
            }
            s.push('}');
        }
        s.push_str("],\"rows\":[");
        for (i, r) in self.rows.iter().enumerate().take(SNAPSHOT_COLS) {
            if i > 0 {
                s.push(',');
            }
            let expr = self.row_expr(&r.coeffs);
            s.push_str("{\"basic\":");
            json_string(&mut s, &self.cols[r.basic].name);
            s.push_str(",\"expr\":");
            json_string(&mut s, &expr);
            s.push('}');
        }
        let _ = write!(s, "],\"branches\":{},\"check\":", self.branches);
        self.record_json(terms, &mut s);
        s.push_str(",\"last\":");
        match &self.last_event {
            Some(e) => json_string(&mut s, e),
            None => s.push_str("null"),
        }
        s.push('}');
        s
    }

    fn eval_app(&self, sym: &str, args: &[Value], _terms: &Terms) -> Option<Value> {
        let ints: Option<Vec<i128>> = args
            .iter()
            .map(|v| {
                if let Value::Int(i) = v {
                    Some(*i)
                } else {
                    None
                }
            })
            .collect();
        let a = ints?;
        Some(match sym {
            "+" => Value::Int(a.iter().try_fold(0i128, |s, x| s.checked_add(*x))?),
            "*" => Value::Int(a.iter().try_fold(1i128, |s, x| s.checked_mul(*x))?),
            "-" if a.len() == 1 => Value::Int(a[0].checked_neg()?),
            "-" => Value::Int(a[1..].iter().try_fold(a[0], |s, x| s.checked_sub(*x))?),
            "<=" => Value::Bool(a[0] <= a[1]),
            "<" => Value::Bool(a[0] < a[1]),
            ">=" => Value::Bool(a[0] >= a[1]),
            ">" => Value::Bool(a[0] > a[1]),
            _ => return None,
        })
    }

    fn default_value(&self, _sort: usize, _terms: &Terms) -> Option<Value> {
        Some(Value::Int(0))
    }

    fn take_changed(&mut self) -> bool {
        std::mem::replace(&mut self.changed, false)
    }

    fn set_recording(&mut self, on: bool) {
        self.record = on;
        if !on {
            self.last_check = None;
        }
    }
}
