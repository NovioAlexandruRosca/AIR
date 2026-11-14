//! From assertions to CNF:
//! 1. **Purification** (Nelson–Oppen input separation): every atom must
//!    belong to a single theory. An "alien" subterm, owned by another
//!    theory than its context, is replaced by a fresh constant `kᵢ`, and
//!    the definition `kᵢ = t` is asserted. `head(l) = x + 1` becomes
//!    `k1 = x + 1` (LIA) with `k1 = head(l)` (DT).
//! 2. **Shared constants**: constants used by two theories; every pair of
//!    shared constants of the same sort gets an interface equality atom.
//! 3. **Tseitin** encoding of the Boolean structure; atoms become Boolean
//!    variables.
//! 4. **Registration**: each atom is handed to its theories, which may add
//!    definitional axioms (e.g. LIA's `a = b ⇔ a ≤ b ∧ a ≥ b`).

use super::combine::{Combination, VarInfo, VarKind};
use super::parser::Problem;
use super::sexp::SmtError;
use super::term::{Op, TermId, Terms, TheoryId, BOOL};
use crate::dimacs::Cnf;
use crate::lit::Lit;
use std::collections::HashMap;

const CONNECTIVES: &[&str] = &["and", "or", "not", "=>", "xor", "ite"];

pub struct Prep {
    pub cnf: Cnf,
    /// Why each original clause exists.
    pub clause_origin: Vec<String>,
    pub assertions: Vec<String>,
    pub purified: Vec<String>,
    /// Purification definitions `k = t` (atom terms).
    pub definitions: Vec<TermId>,
    pub fresh: Vec<TermId>,
    /// Bool constant -> SAT variable.
    pub bool_vars: HashMap<TermId, usize>,
    /// Input atom -> its purified atom (for showing the formula as written).
    pub atom_map: HashMap<TermId, TermId>,
}

struct Purifier<'a> {
    terms: &'a mut Terms,
    alien: HashMap<TermId, TermId>,
    atom_map: HashMap<TermId, TermId>,
    defs: Vec<TermId>,
    fresh: Vec<TermId>,
}

fn mk_eq(terms: &mut Terms, a: TermId, b: TermId) -> TermId {
    let (a, b) = if terms.is_var(a) && terms.is_var(b) && b < a {
        (b, a)
    } else {
        (a, b)
    };
    terms.app("=", vec![a, b], BOOL)
}

fn is_connective(terms: &Terms, t: TermId) -> bool {
    match terms.sym(t) {
        Some(s) if CONNECTIVES.contains(&s) => true,
        Some("=") => terms.sort(terms.args(t)[0]) == BOOL,
        _ => false,
    }
}

impl<'a> Purifier<'a> {
    fn formula(&mut self, t: TermId) -> TermId {
        let node = self.terms.node(t).clone();
        match &node.op {
            Op::True | Op::False | Op::Var(_) | Op::Num(_) => t,
            Op::App(_) if is_connective(self.terms, t) => {
                let args: Vec<TermId> = node.args.iter().map(|&a| self.formula(a)).collect();
                self.terms.mk(node.op.clone(), args, BOOL)
            }
            Op::App(_) => {
                let p = self.atom(t);
                self.atom_map.insert(t, p);
                p
            }
        }
    }

    fn atom(&mut self, t: TermId) -> TermId {
        let node = self.terms.node(t).clone();
        if self.terms.sym(t) == Some("=") {
            let (a, b) = (node.args[0], node.args[1]);
            let th = self.terms.owner(a).or(self.terms.owner(b));
            let a2 = self.term(a, th);
            let b2 = self.term(b, th);
            return mk_eq(self.terms, a2, b2);
        }
        let th = self.terms.owner(t);
        let args: Vec<TermId> = node.args.iter().map(|&a| self.term(a, th)).collect();
        self.terms.mk(node.op.clone(), args, BOOL)
    }

    /// Purify `t` occurring in a context owned by theory `ctx`.
    fn term(&mut self, t: TermId, ctx: Option<TheoryId>) -> TermId {
        if self.terms.is_var(t) {
            return t;
        }
        let own = self.terms.owner(t);
        let node = self.terms.node(t).clone();
        let args: Vec<TermId> = node.args.iter().map(|&a| self.term(a, own)).collect();
        let t2 = self.terms.mk(node.op.clone(), args, node.sort);
        if ctx.is_some() && own != ctx {
            return self.alien(t2);
        }
        t2
    }

    fn alien(&mut self, t: TermId) -> TermId {
        if let Some(&v) = self.alien.get(&t) {
            return v;
        }
        let v = self.terms.fresh_var("k", self.terms.sort(t));
        let def = self.terms.app("=", vec![v, t], BOOL);
        self.alien.insert(t, v);
        self.defs.push(def);
        self.fresh.push(v);
        v
    }
}

fn collect_atoms(terms: &Terms, t: TermId, out: &mut Vec<TermId>) {
    match &terms.node(t).op {
        Op::True | Op::False | Op::Var(_) | Op::Num(_) => {}
        Op::App(_) if is_connective(terms, t) => {
            for &a in terms.args(t) {
                collect_atoms(terms, a, out);
            }
        }
        Op::App(_) => {
            if !out.contains(&t) {
                out.push(t);
            }
        }
    }
}

struct Cnfer<'a> {
    comb: &'a mut Combination,
    clauses: Vec<Vec<Lit>>,
    origin: Vec<String>,
    memo: HashMap<TermId, Lit>,
    num_vars: usize,
    pending: Vec<(usize, TermId, VarKind)>,
    true_lit: Option<Lit>,
    bool_vars: HashMap<TermId, usize>,
}

impl<'a> Cnfer<'a> {
    fn new_var(&mut self, info: VarInfo) -> usize {
        let v = self.num_vars;
        self.num_vars += 1;
        self.comb.set_var(v, info);
        v
    }

    fn clause(&mut self, lits: Vec<Lit>, origin: String) {
        self.clauses.push(lits);
        self.origin.push(origin);
    }

    fn atom_var(&mut self, t: TermId, kind: VarKind) -> usize {
        if let Some(&v) = self.comb.atom_of.get(&t) {
            return v;
        }
        let info = VarInfo {
            label: self.comb.terms.display(t),
            neg: self.comb.terms.display_neg(t),
            kind,
            theories: Vec::new(),
            def: None,
            term: Some(t),
        };
        let v = self.new_var(info);
        self.comb.atom_of.insert(t, v);
        self.pending.push((v, t, kind));
        v
    }

    fn true_lit(&mut self) -> Lit {
        if let Some(l) = self.true_lit {
            return l;
        }
        let v = self.new_var(VarInfo {
            label: "true".into(),
            neg: "false".into(),
            kind: VarKind::True,
            theories: Vec::new(),
            def: None,
            term: None,
        });
        let l = Lit::new(v, true);
        self.clause(vec![l], "the constant true".into());
        self.true_lit = Some(l);
        l
    }

    fn lit(&mut self, t: TermId) -> Lit {
        if let Some(&l) = self.memo.get(&t) {
            return l;
        }
        let terms = &self.comb.terms;
        let node = terms.node(t).clone();
        let l = match &node.op {
            Op::True => self.true_lit(),
            Op::False => !self.true_lit(),
            Op::Var(name) => {
                let v = self.new_var(VarInfo {
                    label: name.clone(),
                    neg: format!("¬{name}"),
                    kind: VarKind::Bool,
                    theories: Vec::new(),
                    def: None,
                    term: Some(t),
                });
                self.bool_vars.insert(t, v);
                Lit::new(v, true)
            }
            Op::Num(_) => unreachable!("numeral in Boolean position"),
            Op::App(sym) if is_connective(terms, t) => {
                if sym == "not" {
                    let a = self.lit(node.args[0]);
                    self.memo.insert(t, !a);
                    return !a;
                }
                let args: Vec<Lit> = node.args.iter().map(|&a| self.lit(a)).collect();
                let def = self.comb.terms.display(t);
                let v = self.num_vars;
                let label = format!("t{}", v + 1);
                self.new_var(VarInfo {
                    label: label.clone(),
                    neg: format!("¬{label}"),
                    kind: VarKind::Aux,
                    theories: Vec::new(),
                    def: Some(def.clone()),
                    term: Some(t),
                });
                let x = Lit::new(v, true);
                let why = format!("Tseitin: {label} ⇔ {def}");
                match sym.as_str() {
                    "and" => {
                        for &a in &args {
                            self.clause(vec![!x, a], why.clone());
                        }
                        let mut c = vec![x];
                        c.extend(args.iter().map(|&a| !a));
                        self.clause(c, why);
                    }
                    "or" | "=>" => {
                        let args: Vec<Lit> = if sym == "=>" {
                            vec![!args[0], args[1]]
                        } else {
                            args
                        };
                        let mut c = vec![!x];
                        c.extend(args.iter().copied());
                        self.clause(c, why.clone());
                        for &a in &args {
                            self.clause(vec![x, !a], why.clone());
                        }
                    }
                    "xor" => {
                        let (a, b) = (args[0], args[1]);
                        self.clause(vec![!x, a, b], why.clone());
                        self.clause(vec![!x, !a, !b], why.clone());
                        self.clause(vec![x, !a, b], why.clone());
                        self.clause(vec![x, a, !b], why);
                    }
                    "=" => {
                        let (a, b) = (args[0], args[1]);
                        self.clause(vec![!x, !a, b], why.clone());
                        self.clause(vec![!x, a, !b], why.clone());
                        self.clause(vec![x, a, b], why.clone());
                        self.clause(vec![x, !a, !b], why);
                    }
                    "ite" => {
                        let (c, a, b) = (args[0], args[1], args[2]);
                        self.clause(vec![!x, !c, a], why.clone());
                        self.clause(vec![!x, c, b], why.clone());
                        self.clause(vec![x, !c, !a], why.clone());
                        self.clause(vec![x, c, !b], why);
                    }
                    _ => unreachable!(),
                }
                x
            }
            Op::App(_) => Lit::new(self.atom_var(t, VarKind::Atom), true),
        };
        self.memo.insert(t, l);
        l
    }

    /// Clauses for a top-level assertion, avoiding Tseitin variables for the
    /// outermost conjunctions and disjunctions.
    fn assert_top(&mut self, t: TermId, origin: &str) {
        let terms = &self.comb.terms;
        let node = terms.node(t).clone();
        match (&node.op, terms.sym(t)) {
            (Op::True, _) => {}
            (Op::False, _) => self.clause(Vec::new(), format!("{origin} (false)")),
            (_, Some("and")) => {
                for &a in &node.args {
                    self.assert_top(a, origin);
                }
            }
            (_, Some("not")) => {
                let inner = node.args[0];
                let inode = self.comb.terms.node(inner).clone();
                match self.comb.terms.sym(inner) {
                    Some("not") => self.assert_top(inode.args[0], origin),
                    Some("or") => {
                        for &a in &inode.args {
                            let na = self.comb.terms.app("not", vec![a], BOOL);
                            self.assert_top(na, origin);
                        }
                    }
                    _ => {
                        let l = self.lit(t);
                        self.clause(vec![l], origin.to_string());
                    }
                }
            }
            (_, Some("or")) => {
                let lits: Vec<Lit> = node.args.iter().map(|&a| self.lit(a)).collect();
                self.clause(lits, origin.to_string());
            }
            (_, Some("=>")) => {
                let a = self.lit(node.args[0]);
                let b = self.lit(node.args[1]);
                self.clause(vec![!a, b], origin.to_string());
            }
            _ => {
                let l = self.lit(t);
                self.clause(vec![l], origin.to_string());
            }
        }
    }
}

pub fn preprocess(problem: &Problem, comb: &mut Combination) -> Result<Prep, SmtError> {
    let assertions: Vec<String> = problem
        .assertions
        .iter()
        .map(|&a| comb.terms.display(a))
        .collect();

    // 1. purification
    let mut p = Purifier {
        terms: &mut comb.terms,
        alien: HashMap::new(),
        atom_map: HashMap::new(),
        defs: Vec::new(),
        fresh: Vec::new(),
    };
    let pure: Vec<TermId> = problem.assertions.iter().map(|&a| p.formula(a)).collect();
    let (defs, fresh, atom_map) = (p.defs, p.fresh, p.atom_map);
    let purified: Vec<String> = pure.iter().map(|&a| comb.terms.display(a)).collect();

    // 2. which theory uses which constant; shared constants
    let mut atoms = Vec::new();
    for &a in pure.iter().chain(defs.iter()) {
        collect_atoms(&comb.terms, a, &mut atoms);
    }
    let var_var = |terms: &Terms, t: TermId| {
        terms.sym(t) == Some("=") && terms.args(t).iter().all(|&x| terms.is_var(x))
    };
    for pass in 0..2 {
        for &a in &atoms {
            if var_var(&comb.terms, a) != (pass == 1) {
                continue;
            }
            let ths = comb.theories_for_atom(a);
            let mut vars = Vec::new();
            comb.terms.vars_in(a, &mut vars);
            for v in vars {
                let e = comb.uses.entry(v).or_default();
                for &th in &ths {
                    if !e.contains(&th) {
                        e.push(th);
                    }
                }
            }
        }
    }
    let mut shared: Vec<TermId> = comb
        .uses
        .iter()
        .filter(|(_, u)| u.len() >= 2)
        .map(|(&v, _)| v)
        .collect();
    shared.sort();
    comb.shared = shared.clone();

    // 3. Tseitin
    let mut c = Cnfer {
        comb,
        clauses: Vec::new(),
        origin: Vec::new(),
        memo: HashMap::new(),
        num_vars: 0,
        pending: Vec::new(),
        true_lit: None,
        bool_vars: HashMap::new(),
    };
    for (i, &a) in pure.iter().enumerate() {
        let origin = format!("assert #{}: {}", i + 1, assertions[i]);
        c.assert_top(a, &origin);
    }
    for &d in &defs {
        let v = c.atom_var(d, VarKind::Definition);
        let origin = format!("purification: {}", c.comb.terms.display(d));
        c.clause(vec![Lit::new(v, true)], origin);
    }
    let mut interface = Vec::new();
    for i in 0..shared.len() {
        for j in i + 1..shared.len() {
            let (x, y) = (shared[i], shared[j]);
            if c.comb.terms.sort(x) != c.comb.terms.sort(y) {
                continue;
            }
            let eq = mk_eq(&mut c.comb.terms, x, y);
            let v = c.atom_var(eq, VarKind::Interface);
            interface.push((x, y, v));
        }
    }
    c.comb.interface = interface;

    // 4. registration with the theories
    let pending = std::mem::take(&mut c.pending);
    let mut next = c.num_vars;
    let axioms = {
        let mut alloc = || {
            next += 1;
            next - 1
        };
        c.comb
            .register_all(pending, &mut alloc)
            .map_err(|m| SmtError {
                line: 0,
                message: m,
            })?
    };
    c.num_vars = next;
    for ax in axioms {
        let origin = format!("axiom ({}): {}", ax.theory, ax.why);
        c.clause(ax.lits, origin);
    }

    let Cnfer {
        clauses,
        origin,
        num_vars,
        bool_vars,
        ..
    } = c;
    Ok(Prep {
        cnf: Cnf {
            num_vars,
            clauses,
            warnings: Vec::new(),
        },
        clause_origin: origin,
        assertions,
        purified,
        definitions: defs,
        fresh,
        bool_vars,
        atom_map,
    })
}
