//! Nelson–Oppen combination of the registered theories, exposed to the SAT
//! solver as a single [`TheoryHook`].
//!
//! After purification every atom belongs to one theory, except equalities
//! between two shared constants, which every interested theory receives.
//! For every pair of shared constants of the same sort an *interface
//! equality* atom `x = y` exists. The combination then works as follows:
//! - deterministic exchange: a theory that derives `x = y` (or `x ≠ y`)
//!   propagates the interface atom, the SAT solver assigns it, and every
//!   other theory sees it as an ordinary literal;
//! - non-convex case: on the final check, any interface atom still
//!   unassigned is decided by a split (guessing the arrangement), guided by
//!   the theories' candidate models (`eq_hint`);
//! - when all theories accept a complete arrangement, the combined
//!   assignment is satisfiable (the theories are stably infinite on Int and
//!   share no function symbols).

use super::term::{Op, TermId, Terms, TheoryId, Value};
use super::theory::{Check, Ctx, Theory};
use crate::lit::Lit;
use crate::solver::{Solver, TheoryClause, TheoryHook, TheoryResponse};
use crate::trace::{json_string, Event};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
    /// Theory atom from the input.
    Atom,
    /// Purification definition `k = t`.
    Definition,
    /// Interface equality between shared constants (Nelson–Oppen).
    Interface,
    /// Atom created by a theory (definitions, branch and bound, splits).
    TheoryAtom,
    /// Declared Bool constant.
    Bool,
    /// Tseitin auxiliary variable.
    Aux,
    /// The constant `true`.
    True,
}

impl VarKind {
    pub fn as_str(self) -> &'static str {
        match self {
            VarKind::Atom => "atom",
            VarKind::Definition => "definition",
            VarKind::Interface => "interface",
            VarKind::TheoryAtom => "theory",
            VarKind::Bool => "bool",
            VarKind::Aux => "aux",
            VarKind::True => "true",
        }
    }
}

#[derive(Debug, Clone)]
pub struct VarInfo {
    pub label: String,
    pub neg: String,
    pub kind: VarKind,
    pub theories: Vec<String>,
    /// For Tseitin variables: the subformula they stand for.
    pub def: Option<String>,
    pub term: Option<TermId>,
}

impl VarInfo {
    pub fn write_json(&self, var: usize, out: &mut String) {
        out.push_str(&format!("{{\"var\":{},\"label\":", var + 1));
        json_string(out, &self.label);
        out.push_str(",\"neg\":");
        json_string(out, &self.neg);
        out.push_str(&format!(
            ",\"kind\":\"{}\",\"theories\":[",
            self.kind.as_str()
        ));
        for (i, t) in self.theories.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            json_string(out, t);
        }
        out.push_str("],\"def\":");
        match &self.def {
            Some(d) => json_string(out, d),
            None => out.push_str("null"),
        }
        out.push('}');
    }
}

pub struct Combination {
    pub terms: Terms,
    pub theories: Vec<Box<dyn Theory>>,
    pub atom_of: HashMap<TermId, usize>,
    atom_theories: HashMap<usize, Vec<TheoryId>>,
    pub vars: Vec<VarInfo>,
    /// Theories using each constant after purification.
    pub uses: HashMap<TermId, Vec<TheoryId>>,
    pub shared: Vec<TermId>,
    /// (x, y, var of `x = y`)
    pub interface: Vec<(TermId, TermId, usize)>,
    fed: usize,
    pub model: HashMap<TermId, Value>,
    pub model_ready: bool,
    /// Pass theory propagations to the SAT solver. When off, theories only
    /// check (conflicts and splits) and only interface equalities are still
    /// propagated; this is the plain DPLL(T) of textbooks, used by the playground.
    pub theory_propagation: bool,
}

impl Combination {
    pub fn new(theories: Vec<Box<dyn Theory>>) -> Combination {
        let mut c = Combination {
            terms: Terms::new(),
            theories,
            atom_of: HashMap::new(),
            atom_theories: HashMap::new(),
            vars: Vec::new(),
            uses: HashMap::new(),
            shared: Vec::new(),
            interface: Vec::new(),
            fed: 0,
            model: HashMap::new(),
            model_ready: false,
            theory_propagation: true,
        };
        for (i, t) in c.theories.iter_mut().enumerate() {
            t.init(&mut c.terms, i);
        }
        c
    }

    pub fn theory_name(&self, t: TheoryId) -> &'static str {
        self.theories[t].name()
    }

    /// Theories that must interpret an atom term.
    pub fn theories_for_atom(&self, t: TermId) -> Vec<TheoryId> {
        let terms = &self.terms;
        let args = terms.args(t);
        if terms.sym(t) == Some("=") && args.len() == 2 {
            let (a, b) = (args[0], args[1]);
            let mut owners: Vec<TheoryId> = [terms.owner(a), terms.owner(b)]
                .into_iter()
                .flatten()
                .collect();
            owners.dedup();
            if !owners.is_empty() {
                return owners;
            }
            // constant = constant: the sort's theory and every user
            let mut out: Vec<TheoryId> = terms.sort_owner(terms.sort(a)).into_iter().collect();
            for x in [a, b] {
                for &u in self.uses.get(&x).map(|v| v.as_slice()).unwrap_or(&[]) {
                    if !out.contains(&u) {
                        out.push(u);
                    }
                }
            }
            out.sort();
            return out;
        }
        terms.owner(t).into_iter().collect()
    }

    pub fn set_var(&mut self, var: usize, info: VarInfo) {
        while self.vars.len() <= var {
            self.vars.push(VarInfo {
                label: String::new(),
                neg: String::new(),
                kind: VarKind::Aux,
                theories: Vec::new(),
                def: None,
                term: None,
            });
        }
        self.vars[var] = info;
    }

    fn atom_info(&self, term: TermId, kind: VarKind, theories: &[TheoryId]) -> VarInfo {
        VarInfo {
            label: self.terms.display(term),
            neg: self.terms.display_neg(term),
            kind,
            theories: theories
                .iter()
                .map(|&t| self.theory_name(t).to_string())
                .collect(),
            def: None,
            term: Some(term),
        }
    }

    /// Register atoms with their theories. Theories may create further
    /// atoms (registered in turn) and definitional axioms (returned).
    pub fn register_all(
        &mut self,
        pending: Vec<(usize, TermId, VarKind)>,
        alloc: &mut dyn FnMut() -> usize,
    ) -> Result<Vec<TheoryClause>, String> {
        let mut queue: std::collections::VecDeque<_> = pending.into();
        let mut axioms = Vec::new();
        while let Some((var, term, kind)) = queue.pop_front() {
            let ths = self.theories_for_atom(term);
            if ths.is_empty() {
                return Err(format!(
                    "no theory can interpret {}",
                    self.terms.display(term)
                ));
            }
            let info = self.atom_info(term, kind, &ths);
            self.set_var(var, info);
            self.atom_of.insert(term, var);
            self.atom_theories.insert(var, ths.clone());
            for tid in ths {
                let mut ctx = Ctx::new(&mut self.terms, &mut self.atom_of, &mut *alloc);
                self.theories[tid].register_atom(var, term, &mut ctx)?;
                let Ctx {
                    new_atoms,
                    axioms: ax,
                    ..
                } = ctx;
                for (v, t) in new_atoms {
                    queue.push_back((v, t, VarKind::TheoryAtom));
                }
                axioms.extend(ax);
            }
        }
        Ok(axioms)
    }

    /// Run one theory check with on-demand atom creation; new variables are
    /// announced in the trace before anything refers to them.
    fn run_theory(
        &mut self,
        tid: TheoryId,
        sat: &mut Solver,
        final_check: bool,
        axioms: &mut Vec<TheoryClause>,
    ) -> Result<Check, String> {
        let before = sat.num_vars();
        let recording = sat.tracer.enabled;
        let (check, new_atoms, ax) = {
            let mut alloc = || sat.new_var();
            let mut ctx = Ctx::new(&mut self.terms, &mut self.atom_of, &mut alloc);
            self.theories[tid].set_recording(recording);
            let check = self.theories[tid].check(&mut ctx, final_check);
            let Ctx {
                new_atoms, axioms, ..
            } = ctx;
            (check, new_atoms, axioms)
        };
        axioms.extend(ax);
        if !new_atoms.is_empty() {
            let pending = new_atoms
                .into_iter()
                .map(|(v, t)| (v, t, VarKind::TheoryAtom))
                .collect();
            let mut alloc = || sat.new_var();
            let more = self.register_all(pending, &mut alloc)?;
            axioms.extend(more);
        }
        for v in before..sat.num_vars() {
            let info = self.vars[v].clone();
            sat.tracer.push(|| Event::NewVar {
                var: v + 1,
                label: info.label.clone(),
                neg: info.neg.clone(),
                kind: info.kind.as_str(),
                theories: info.theories.join(","),
            });
        }
        Ok(check)
    }

    fn label(&self, l: Lit) -> String {
        match self.vars.get(l.var()) {
            Some(v) if l.is_positive() => v.label.clone(),
            Some(v) => v.neg.clone(),
            None => l.to_string(),
        }
    }

    fn is_interface(&self, var: usize) -> bool {
        self.vars
            .get(var)
            .is_some_and(|v| v.kind == VarKind::Interface)
    }

    /// Translate a theory's answer into clauses for the SAT solver.
    fn absorb(&mut self, tid: TheoryId, check: Check, sat: &mut Solver, resp: &mut TheoryResponse) {
        let name = self.theory_name(tid).to_string();
        for (kind, message, lits) in check.notes {
            sat.tracer.push(|| Event::Theory {
                theory: name.clone(),
                kind,
                message,
                lits: lits.iter().map(|l| l.to_dimacs()).collect(),
                data: String::new(),
            });
        }
        if let Some(c) = check.conflict {
            let data = if sat.tracer.enabled {
                self.theories[tid].snapshot(&self.terms)
            } else {
                String::new()
            };
            let lits: Vec<i64> = c.lits.iter().map(|l| l.to_dimacs()).collect();
            let why = c.why.clone();
            sat.tracer.push(|| Event::Theory {
                theory: name.clone(),
                kind: "conflict",
                message: why,
                lits,
                data,
            });
            resp.conflict = Some(TheoryClause {
                lits: c.lits.iter().map(|&l| !l).collect(),
                theory: name.clone(),
                why: c.why,
            });
            return;
        }
        for p in check.propagations {
            if !self.theory_propagation && !self.is_interface(p.implied.var()) {
                continue;
            }
            let mut why = p.why;
            if self.is_interface(p.implied.var()) {
                let others: Vec<&str> = self.atom_theories[&p.implied.var()]
                    .iter()
                    .filter(|&&t| t != tid)
                    .map(|&t| self.theory_name(t))
                    .collect();
                let msg = format!(
                    "Nelson–Oppen: {name} derives {} between shared constants and passes it to {}",
                    self.label(p.implied),
                    if others.is_empty() {
                        "the other theories".to_string()
                    } else {
                        others.join(", ")
                    }
                );
                let because: Vec<i64> = p.because.iter().map(|l| l.to_dimacs()).collect();
                let lits = std::iter::once(p.implied.to_dimacs())
                    .chain(because)
                    .collect();
                let m = msg.clone();
                sat.tracer.push(|| Event::Theory {
                    theory: name.clone(),
                    kind: "nelson-oppen",
                    message: m,
                    lits,
                    data: String::new(),
                });
                why = format!("{msg}. {why}");
            }
            let mut lits = vec![p.implied];
            lits.extend(p.because.iter().map(|&l| !l));
            resp.propagations.push(TheoryClause {
                lits,
                theory: name.clone(),
                why,
            });
        }
        if resp.split.is_none() {
            if let Some((lit, why)) = check.split {
                resp.split = Some((lit, name.clone(), why));
            }
        }
        if resp.unknown.is_none() {
            resp.unknown = check.unknown.map(|u| format!("{name}: {u}"));
        }
    }

    fn snapshots(&mut self, sat: &mut Solver) {
        if !sat.tracer.enabled {
            return;
        }
        for tid in 0..self.theories.len() {
            if self.theories[tid].take_changed() {
                let data = self.theories[tid].snapshot(&self.terms);
                let name = self.theory_name(tid).to_string();
                sat.tracer.push(|| Event::Theory {
                    theory: name,
                    kind: "state",
                    message: String::new(),
                    lits: Vec::new(),
                    data,
                });
            }
        }
    }

    pub fn snapshot_all(&self) -> String {
        let mut s = String::from("{");
        for (i, t) in self.theories.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            json_string(&mut s, t.name());
            s.push(':');
            s.push_str(&t.snapshot(&self.terms));
        }
        s.push('}');
        s
    }

    pub fn check(&mut self, sat: &mut Solver, final_check: bool) -> TheoryResponse {
        // Feed newly assigned atoms to their theories.
        let trail_len = sat.trail().len();
        for i in self.fed..trail_len {
            let lit = sat.trail()[i];
            if let Some(ths) = self.atom_theories.get(&lit.var()) {
                let level = sat.var_level(lit.var());
                for &tid in ths {
                    self.theories[tid].assert_lit(lit.var(), lit.is_positive(), level);
                }
            }
        }
        self.fed = trail_len;
        self.model_ready = false;

        let mut resp = TheoryResponse::default();
        let mut axioms = Vec::new();
        // Partial check of every theory.
        for tid in 0..self.theories.len() {
            match self.run_theory(tid, sat, false, &mut axioms) {
                Ok(check) => self.absorb(tid, check, sat, &mut resp),
                Err(e) => resp.unknown = Some(e),
            }
            if resp.conflict.is_some() || resp.unknown.is_some() {
                break;
            }
        }
        resp.axioms = axioms;
        if !final_check
            || resp.conflict.is_some()
            || !resp.propagations.is_empty()
            || !resp.axioms.is_empty()
            || resp.unknown.is_some()
        {
            self.snapshots(sat);
            return resp;
        }

        // Final check: theory-specific completeness work (splits).
        let mut axioms = Vec::new();
        for tid in 0..self.theories.len() {
            match self.run_theory(tid, sat, true, &mut axioms) {
                Ok(check) => self.absorb(tid, check, sat, &mut resp),
                Err(e) => resp.unknown = Some(e),
            }
            if resp.conflict.is_some()
                || !resp.propagations.is_empty()
                || resp.split.is_some()
                || resp.unknown.is_some()
            {
                break;
            }
        }
        resp.axioms = axioms;
        if resp.conflict.is_some()
            || !resp.propagations.is_empty()
            || resp.split.is_some()
            || resp.unknown.is_some()
            || !resp.axioms.is_empty()
        {
            self.snapshots(sat);
            return resp;
        }

        // Nelson–Oppen: every pair of shared constants must be arranged.
        for &(x, y, var) in &self.interface {
            if sat.value(Lit::new(var, true)).is_some() {
                continue;
            }
            let hint = self.theories.iter().find_map(|t| t.eq_hint(x, y));
            let eq = hint.unwrap_or(false);
            let users: Vec<&str> = self.atom_theories[&var]
                .iter()
                .map(|&t| self.theory_name(t))
                .collect();
            let (xs, ys) = (self.terms.display(x), self.terms.display(y));
            let why = format!(
                "Nelson–Oppen arrangement: {xs} and {ys} are shared by {}, which must agree on whether {xs} = {ys}; no theory implies either, so guess it ({}): try {}",
                users.join(" and "),
                match hint {
                    Some(true) => "they are equal in the current LIA model".to_string(),
                    Some(false) => "they differ in the current LIA model".to_string(),
                    None => "no model hint".to_string(),
                },
                if eq { format!("{xs} = {ys}") } else { format!("{xs} ≠ {ys}") }
            );
            resp.split = Some((Lit::new(var, eq), "Nelson–Oppen".into(), why));
            self.snapshots(sat);
            return resp;
        }

        // Consistent and complete: record the model.
        let mut known: HashMap<TermId, Value> = HashMap::new();
        for tid in 0..self.theories.len() {
            self.theories[tid].model(&mut self.terms, &mut known);
        }
        self.model = known;
        self.model_ready = true;
        self.snapshots(sat);
        resp
    }

    pub fn backjump(&mut self, level: usize, trail_len: usize) {
        for t in self.theories.iter_mut() {
            t.backtrack(level);
        }
        self.fed = self.fed.min(trail_len);
    }

    /// Evaluate a term under the model (for verification). `bools` gives
    /// the values of Bool constants.
    pub fn eval(&self, t: TermId, bools: &dyn Fn(TermId) -> Option<bool>) -> Option<Value> {
        let terms = &self.terms;
        let node = terms.node(t);
        let b = |t: TermId| -> Option<bool> {
            match self.eval(t, bools)? {
                Value::Bool(x) => Some(x),
                _ => None,
            }
        };
        match &node.op {
            Op::True => Some(Value::Bool(true)),
            Op::False => Some(Value::Bool(false)),
            Op::Num(n) => Some(Value::Int(*n)),
            Op::Var(_) => {
                if node.sort == super::term::BOOL {
                    return bools(t).map(Value::Bool);
                }
                self.model
                    .get(&t)
                    .cloned()
                    .or_else(|| self.default_value(node.sort))
            }
            Op::App(sym) => match sym.as_str() {
                "not" => Some(Value::Bool(!b(node.args[0])?)),
                "and" => {
                    let mut r = true;
                    for &a in &node.args {
                        r &= b(a)?;
                    }
                    Some(Value::Bool(r))
                }
                "or" => {
                    let mut r = false;
                    for &a in &node.args {
                        r |= b(a)?;
                    }
                    Some(Value::Bool(r))
                }
                "=>" => Some(Value::Bool(!b(node.args[0])? || b(node.args[1])?)),
                "xor" => Some(Value::Bool(b(node.args[0])? != b(node.args[1])?)),
                "ite" => {
                    if b(node.args[0])? {
                        self.eval(node.args[1], bools)
                    } else {
                        self.eval(node.args[2], bools)
                    }
                }
                "=" => Some(Value::Bool(
                    self.eval(node.args[0], bools)? == self.eval(node.args[1], bools)?,
                )),
                _ => {
                    let owner = terms.fun_owner(sym)?;
                    let args: Option<Vec<Value>> =
                        node.args.iter().map(|&a| self.eval(a, bools)).collect();
                    let args = args?;
                    self.theories[owner]
                        .eval_app(sym, &args, terms)
                        .or_else(|| self.model.get(&t).cloned())
                        .or_else(|| self.default_value(node.sort))
                }
            },
        }
    }

    fn default_value(&self, sort: usize) -> Option<Value> {
        if sort == super::term::BOOL {
            return Some(Value::Bool(false));
        }
        let owner = self.terms.sort_owner(sort)?;
        self.theories[owner].default_value(sort, &self.terms)
    }
}

/// The SAT solver owns the hook; the SMT driver keeps a handle to the same
/// combination to read the model and the variable table afterwards.
pub struct HookAdapter(pub Rc<RefCell<Combination>>);

impl TheoryHook for HookAdapter {
    fn check(&mut self, sat: &mut Solver, final_check: bool) -> TheoryResponse {
        self.0.borrow_mut().check(sat, final_check)
    }

    fn backjump(&mut self, level: usize, trail_len: usize) {
        self.0.borrow_mut().backjump(level, trail_len);
    }
}
