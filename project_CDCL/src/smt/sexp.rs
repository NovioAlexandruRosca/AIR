//! S-expression reader for SMT-LIB input.

use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Sexp {
    /// Symbol, numeral, keyword or string literal, with its line number.
    Atom(String, usize),
    List(Vec<Sexp>, usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for SmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            write!(f, "{}", self.message)
        } else {
            write!(f, "line {}: {}", self.line, self.message)
        }
    }
}

impl std::error::Error for SmtError {}

pub fn err<T>(line: usize, message: impl Into<String>) -> Result<T, SmtError> {
    Err(SmtError {
        line,
        message: message.into(),
    })
}

impl Sexp {
    pub fn line(&self) -> usize {
        match self {
            Sexp::Atom(_, l) | Sexp::List(_, l) => *l,
        }
    }

    pub fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(s, _) => Some(s),
            Sexp::List(..) => None,
        }
    }

    pub fn list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(v, _) => Some(v),
            Sexp::Atom(..) => None,
        }
    }

    /// The head symbol of a list, e.g. `assert` for `(assert ...)`.
    pub fn head(&self) -> Option<&str> {
        self.list().and_then(|l| l.first()).and_then(|h| h.atom())
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(s, _) => write!(f, "{s}"),
            Sexp::List(items, _) => {
                write!(f, "(")?;
                for (i, x) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Parse every top-level s-expression. `;` starts a comment.
pub fn parse_all(text: &str) -> Result<Vec<Sexp>, SmtError> {
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut line = 1;
    let mut stack: Vec<(Vec<Sexp>, usize)> = Vec::new();
    let mut top = Vec::new();

    let push = |stack: &mut Vec<(Vec<Sexp>, usize)>, top: &mut Vec<Sexp>, e: Sexp| match stack
        .last_mut()
    {
        Some((items, _)) => items.push(e),
        None => top.push(e),
    };

    while i < chars.len() {
        let c = chars[i];
        match c {
            '\n' => {
                line += 1;
                i += 1;
            }
            c if c.is_whitespace() => i += 1,
            ';' => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '(' => {
                stack.push((Vec::new(), line));
                i += 1;
            }
            ')' => {
                let (items, l) = match stack.pop() {
                    Some(x) => x,
                    None => return err(line, "unexpected ')'"),
                };
                push(&mut stack, &mut top, Sexp::List(items, l));
                i += 1;
            }
            '"' => {
                let start_line = line;
                let mut s = String::from("\"");
                i += 1;
                loop {
                    if i >= chars.len() {
                        return err(start_line, "unterminated string literal");
                    }
                    let ch = chars[i];
                    i += 1;
                    if ch == '\n' {
                        line += 1;
                    }
                    if ch == '"' {
                        // "" is an escaped quote in SMT-LIB 2.6
                        if i < chars.len() && chars[i] == '"' {
                            s.push('"');
                            i += 1;
                            continue;
                        }
                        break;
                    }
                    s.push(ch);
                }
                s.push('"');
                push(&mut stack, &mut top, Sexp::Atom(s, start_line));
            }
            '|' => {
                let start_line = line;
                let mut s = String::new();
                i += 1;
                loop {
                    if i >= chars.len() {
                        return err(start_line, "unterminated |quoted symbol|");
                    }
                    let ch = chars[i];
                    i += 1;
                    if ch == '\n' {
                        line += 1;
                    }
                    if ch == '|' {
                        break;
                    }
                    s.push(ch);
                }
                push(&mut stack, &mut top, Sexp::Atom(s, start_line));
            }
            _ => {
                let mut s = String::new();
                while i < chars.len() {
                    let ch = chars[i];
                    if ch.is_whitespace()
                        || ch == '('
                        || ch == ')'
                        || ch == ';'
                        || ch == '"'
                        || ch == '|'
                    {
                        break;
                    }
                    s.push(ch);
                    i += 1;
                }
                push(&mut stack, &mut top, Sexp::Atom(s, line));
            }
        }
    }
    if let Some((_, l)) = stack.last() {
        return err(*l, "unclosed '(' (missing ')')");
    }
    Ok(top)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_nested_lists_comments_and_strings() {
        let s =
            parse_all("; hello\n(assert (<= x 3)) ; tail\n(set-info :source \"a \"\"b\"\"\")\n")
                .unwrap();
        assert_eq!(s.len(), 2);
        assert_eq!(s[0].head(), Some("assert"));
        assert_eq!(s[0].to_string(), "(assert (<= x 3))");
        assert_eq!(s[1].list().unwrap()[2].atom(), Some("\"a \"b\"\""));
        assert_eq!(s[1].line(), 3);
    }

    #[test]
    fn reports_unbalanced_parentheses() {
        assert_eq!(parse_all("(a (b)").unwrap_err().line, 1);
        assert!(parse_all("a)").unwrap_err().message.contains("unexpected"));
    }
}
