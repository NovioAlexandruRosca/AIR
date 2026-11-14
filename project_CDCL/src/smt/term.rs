//! Hash-consed terms, sorts and the signature (which theory owns which
//! sort and function symbol). Formulas are Bool-sorted terms.

use std::collections::{HashMap, HashSet};
use std::fmt;

pub type TermId = usize;
pub type SortId = usize;
pub type TheoryId = usize;

/// The only built-in sort: everything else is provided by a theory.
pub const BOOL: SortId = 0;

/// Core (theory-independent) Boolean symbols.
pub const CORE_SYMBOLS: &[&str] = &["and", "or", "not", "=>", "xor", "=", "distinct", "ite"];

#[derive(Debug, Clone)]
pub struct SortInfo {
    pub name: String,
    /// Theory that owns the sort (None for Bool).
    pub theory: Option<TheoryId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    /// Uninterpreted constant (declared, or created by purification).
    Var(String),
    /// Integer numeral.
    Num(i128),
    True,
    False,
    /// Application of a core or theory symbol.
    App(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Node {
    pub op: Op,
    pub args: Vec<TermId>,
    pub sort: SortId,
}

/// Term bank + signature.
#[derive(Debug, Clone)]
pub struct Terms {
    nodes: Vec<Node>,
    map: HashMap<Node, TermId>,
    pub sorts: Vec<SortInfo>,
    sort_by_name: HashMap<String, SortId>,
    /// Function symbol -> owning theory.
    fun_owner: HashMap<String, TheoryId>,
    /// Names of declared constants (to keep fresh names unique).
    names: HashSet<String>,
    fresh_counter: usize,
}

impl Default for Terms {
    fn default() -> Self {
        Terms::new()
    }
}

impl Terms {
    pub fn new() -> Terms {
        let mut t = Terms {
            nodes: Vec::new(),
            map: HashMap::new(),
            sorts: Vec::new(),
            sort_by_name: HashMap::new(),
            fun_owner: HashMap::new(),
            names: HashSet::new(),
            fresh_counter: 0,
        };
        t.add_sort("Bool", None);
        t
    }

    // ------------------------------------------------------------ signature

    pub fn add_sort(&mut self, name: &str, theory: Option<TheoryId>) -> SortId {
        let id = self.sorts.len();
        self.sorts.push(SortInfo {
            name: name.to_string(),
            theory,
        });
        self.sort_by_name.insert(name.to_string(), id);
        id
    }

    pub fn sort_named(&self, name: &str) -> Option<SortId> {
        self.sort_by_name.get(name).copied()
    }

    pub fn sort_name(&self, s: SortId) -> &str {
        &self.sorts[s].name
    }

    pub fn sort_owner(&self, s: SortId) -> Option<TheoryId> {
        self.sorts[s].theory
    }

    pub fn add_fun(&mut self, name: &str, theory: TheoryId) {
        self.fun_owner.insert(name.to_string(), theory);
    }

    pub fn fun_owner(&self, name: &str) -> Option<TheoryId> {
        self.fun_owner.get(name).copied()
    }

    pub fn is_declared(&self, name: &str) -> bool {
        self.names.contains(name) || self.fun_owner.contains_key(name)
    }

    // ------------------------------------------------------------ terms

    pub fn mk(&mut self, op: Op, args: Vec<TermId>, sort: SortId) -> TermId {
        let node = Node { op, args, sort };
        if let Some(&id) = self.map.get(&node) {
            return id;
        }
        let id = self.nodes.len();
        self.nodes.push(node.clone());
        self.map.insert(node, id);
        id
    }

    pub fn var(&mut self, name: &str, sort: SortId) -> TermId {
        self.names.insert(name.to_string());
        self.mk(Op::Var(name.to_string()), Vec::new(), sort)
    }

    pub fn num(&mut self, n: i128, sort: SortId) -> TermId {
        self.mk(Op::Num(n), Vec::new(), sort)
    }

    pub fn app(&mut self, sym: &str, args: Vec<TermId>, sort: SortId) -> TermId {
        self.mk(Op::App(sym.to_string()), args, sort)
    }

    pub fn bool_const(&mut self, b: bool) -> TermId {
        self.mk(if b { Op::True } else { Op::False }, Vec::new(), BOOL)
    }

    /// A fresh constant named `{prefix}{n}` that clashes with no declared name.
    pub fn fresh_var(&mut self, prefix: &str, sort: SortId) -> TermId {
        loop {
            self.fresh_counter += 1;
            let name = format!("{prefix}{}", self.fresh_counter);
            if !self.is_declared(&name) {
                return self.var(&name, sort);
            }
        }
    }

    pub fn node(&self, t: TermId) -> &Node {
        &self.nodes[t]
    }

    pub fn sort(&self, t: TermId) -> SortId {
        self.nodes[t].sort
    }

    pub fn args(&self, t: TermId) -> &[TermId] {
        &self.nodes[t].args
    }

    pub fn is_var(&self, t: TermId) -> bool {
        matches!(self.nodes[t].op, Op::Var(_))
    }

    /// Symbol of an application, if `t` is one.
    pub fn sym(&self, t: TermId) -> Option<&str> {
        match &self.nodes[t].op {
            Op::App(s) => Some(s),
            _ => None,
        }
    }

    pub fn var_name(&self, t: TermId) -> Option<&str> {
        match &self.nodes[t].op {
            Op::Var(s) => Some(s),
            _ => None,
        }
    }

    /// Theory owning the term's top symbol. Constants belong to no theory
    /// (they can be shared); numerals belong to the owner of their sort.
    pub fn owner(&self, t: TermId) -> Option<TheoryId> {
        let n = &self.nodes[t];
        match &n.op {
            Op::Var(_) | Op::True | Op::False => None,
            Op::Num(_) => self.sort_owner(n.sort),
            Op::App(s) => self.fun_owner(s),
        }
    }

    /// All constants occurring in `t`.
    pub fn vars_in(&self, t: TermId, out: &mut Vec<TermId>) {
        if self.is_var(t) {
            if !out.contains(&t) {
                out.push(t);
            }
            return;
        }
        for &a in &self.nodes[t].args {
            self.vars_in(a, out);
        }
    }

    // ------------------------------------------------------------ printing

    /// Human-readable infix rendering (`x + 2·y ≤ 3`, `head(l) = k1`).
    pub fn display(&self, t: TermId) -> String {
        let mut s = String::new();
        self.fmt_term(t, 0, &mut s);
        s
    }

    /// Rendering of the negation of an atom (`x > 3` for `x ≤ 3`).
    pub fn display_neg(&self, t: TermId) -> String {
        let n = &self.nodes[t];
        if let Op::App(sym) = &n.op {
            if n.args.len() == 2 {
                let flip = match sym.as_str() {
                    "=" => Some("≠"),
                    "<=" => Some(">"),
                    "<" => Some("≥"),
                    ">=" => Some("<"),
                    ">" => Some("≤"),
                    _ => None,
                };
                if let Some(op) = flip {
                    let mut s = String::new();
                    self.fmt_term(n.args[0], 3, &mut s);
                    s.push_str(&format!(" {op} "));
                    self.fmt_term(n.args[1], 3, &mut s);
                    return s;
                }
            }
        }
        let mut s = String::from("¬");
        self.fmt_term(t, 9, &mut s);
        s
    }

    /// SMT-LIB rendering, e.g. `(<= (+ x 1) 3)`.
    pub fn to_smtlib(&self, t: TermId) -> String {
        let n = &self.nodes[t];
        match &n.op {
            Op::Var(s) => s.clone(),
            Op::Num(v) if *v < 0 => format!("(- {})", -v),
            Op::Num(v) => v.to_string(),
            Op::True => "true".into(),
            Op::False => "false".into(),
            Op::App(sym) => {
                if n.args.is_empty() {
                    return sym.clone();
                }
                let head = match sym.strip_prefix("is-") {
                    Some(c) if self.fun_owner(sym).is_some() => format!("(_ is {c})"),
                    _ => sym.clone(),
                };
                let args: Vec<String> = n.args.iter().map(|&a| self.to_smtlib(a)).collect();
                format!("({head} {})", args.join(" "))
            }
        }
    }

    fn fmt_term(&self, t: TermId, parent_prec: u8, out: &mut String) {
        let n = &self.nodes[t];
        let sym = match &n.op {
            Op::Var(s) => {
                out.push_str(s);
                return;
            }
            Op::Num(v) => {
                if *v < 0 && parent_prec > 0 {
                    out.push_str(&format!("({v})"));
                } else {
                    out.push_str(&v.to_string());
                }
                return;
            }
            Op::True => {
                out.push_str("true");
                return;
            }
            Op::False => {
                out.push_str("false");
                return;
            }
            Op::App(s) => s.as_str(),
        };
        // (infix symbol, precedence)
        let infix = match sym {
            "=>" => Some(("⇒", 1)),
            "or" => Some(("∨", 2)),
            "xor" => Some(("⊕", 2)),
            "and" => Some(("∧", 3)),
            "=" => Some(("=", 4)),
            "<=" => Some(("≤", 4)),
            "<" => Some(("<", 4)),
            ">=" => Some(("≥", 4)),
            ">" => Some((">", 4)),
            "+" => Some(("+", 5)),
            "-" if n.args.len() >= 2 => Some(("-", 5)),
            "*" => Some(("·", 6)),
            _ => None,
        };
        if let Some((op, prec)) = infix {
            let paren = prec <= parent_prec && parent_prec != 0;
            if paren {
                out.push('(');
            }
            for (i, &a) in n.args.iter().enumerate() {
                if i > 0 {
                    if op == "·" {
                        out.push('·');
                    } else {
                        out.push_str(&format!(" {op} "));
                    }
                }
                // Right operands of non-associative operators need parentheses
                // at equal precedence; left operands do not.
                let p = if i == 0 { prec - 1 } else { prec };
                self.fmt_term(a, p.max(1), out);
            }
            if paren {
                out.push(')');
            }
            return;
        }
        match sym {
            "not" => {
                out.push('¬');
                self.fmt_term(n.args[0], 9, out);
            }
            "-" => {
                out.push('-');
                self.fmt_term(n.args[0], 9, out);
            }
            _ => {
                out.push_str(sym);
                if !n.args.is_empty() {
                    out.push('(');
                    for (i, &a) in n.args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.fmt_term(a, 0, out);
                    }
                    out.push(')');
                }
            }
        }
    }
}

/// A value in a model.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Int(i128),
    /// Constructor application.
    Dt(String, Vec<Value>),
}

impl fmt::Display for Value {
    /// SMT-LIB syntax: `3`, `(- 3)`, `nil`, `(cons 1 nil)`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Int(v) if *v < 0 => write!(f, "(- {})", -v),
            Value::Int(v) => write!(f, "{v}"),
            Value::Dt(c, args) if args.is_empty() => write!(f, "{c}"),
            Value::Dt(c, args) => {
                write!(f, "({c}")?;
                for a in args {
                    write!(f, " {a}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_consing_and_display() {
        let mut t = Terms::new();
        let int = t.add_sort("Int", Some(0));
        let x = t.var("x", int);
        let y = t.var("y", int);
        let two = t.num(2, int);
        let m = t.app("*", vec![two, y], int);
        let s1 = t.app("+", vec![x, m], int);
        let s2 = t.app("+", vec![x, m], int);
        assert_eq!(s1, s2);
        let three = t.num(3, int);
        let le = t.app("<=", vec![s1, three], BOOL);
        assert_eq!(t.display(le), "x + 2·y ≤ 3");
        assert_eq!(t.display_neg(le), "x + 2·y > 3");
        assert_eq!(t.to_smtlib(le), "(<= (+ x (* 2 y)) 3)");
        let d = t.app("-", vec![x, s1], int);
        assert_eq!(t.display(d), "x - (x + 2·y)");
    }

    #[test]
    fn fresh_names_avoid_declared_ones() {
        let mut t = Terms::new();
        let int = t.add_sort("Int", Some(0));
        t.var("k1", int);
        let f = t.fresh_var("k", int);
        assert_eq!(t.var_name(f), Some("k2"));
    }
}
