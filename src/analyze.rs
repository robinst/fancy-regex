// Copyright 2016 Google Inc. All rights reserved.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

//! Analysis of regex expressions.

use bit_set::BitSet;
use std::cmp::min;
use std::usize;

use Expr;
use Error;
use Result;

#[derive(Debug)]
pub struct AnalyzedExpr<'a> {
    pub expr: &'a Expr,
    pub children: Vec<AnalyzedExpr<'a>>,
    pub start_group: usize,
    pub end_group: usize,
    pub min_size: usize,
    pub const_size: bool,
    pub hard: bool,
    pub looks_left: bool,
}

impl<'a> AnalyzedExpr<'a> {
    pub fn is_literal(&self) -> bool {
        match *self.expr {
            Expr::Literal { casei, .. } => !casei,
            Expr::Concat(_) => {
                self.children.iter().all(|child| child.is_literal())
            }
            _ => false
        }
    }

    pub fn push_literal(&self, buf: &mut String) {
        match *self.expr {
            // could be more paranoid about checking casei
            Expr::Literal { ref val, .. } => buf.push_str(val),
            Expr::Concat(_) => {
                for child in &self.children {
                    child.push_literal(buf);
                }
            }
            _ => panic!("push_literal called on non-literal")
        }
    }
}

struct Analyzer<'a> {
    backrefs: &'a BitSet,
    group_ix: usize,
}

impl<'a> Analyzer<'a> {
    fn visit(&mut self, expr: &'a Expr) -> Result<AnalyzedExpr<'a>> {
        let start_group = self.group_ix;
        let mut children = Vec::new();
        let mut min_size = 0;
        let mut const_size = false;
        let mut hard = false;
        let mut looks_left = false;
        match *expr {
            Expr::Empty | Expr::EndText | Expr::EndLine => {
                const_size = true;
            }
            Expr::Any { .. } => {
                min_size = 1;
                const_size = true;
            }
            Expr::Literal { ref val, casei } => {
                // right now each character in a literal gets its own node, that might change
                min_size = 1;
                const_size = literal_const_size(val, casei);
            }
            Expr::StartText | Expr::StartLine => {
                const_size = true;
                looks_left = true;
            }
            Expr::Concat(ref v) => {
                const_size = true;
                for child in v {
                    let analyzed_child = self.visit(child)?;
                    looks_left |= analyzed_child.looks_left && min_size == 0;
                    min_size += analyzed_child.min_size;
                    const_size &= analyzed_child.const_size;
                    hard |= analyzed_child.hard;
                    children.push(analyzed_child);
                }
            }
            Expr::Alt(ref v) => {
                let analyzed_child = self.visit(&v[0])?;
                min_size = analyzed_child.min_size;
                const_size = analyzed_child.const_size;
                hard = analyzed_child.hard;
                children.push(analyzed_child);
                for child in &v[1..] {
                    let analyzed_child = self.visit(child)?;
                    const_size &= analyzed_child.const_size && min_size == analyzed_child.min_size;
                    min_size = min(min_size, analyzed_child.min_size);
                    hard |= analyzed_child.hard;
                    looks_left |= analyzed_child.looks_left;
                    children.push(analyzed_child);
                }
            }
            Expr::Group(ref child) => {
                let group = self.group_ix;
                self.group_ix += 1;
                let analyzed_child = self.visit(child)?;
                min_size = analyzed_child.min_size;
                const_size = analyzed_child.const_size;
                looks_left = analyzed_child.looks_left;
                hard = analyzed_child.hard | self.backrefs.contains(group);
                children.push(analyzed_child);
            }
            Expr::LookAround(ref child, _) => {
                let analyzed_child = self.visit(child)?;
                // min_size = 0
                const_size = true;
                hard = true;
                looks_left = analyzed_child.looks_left;
                children.push(analyzed_child);
            }
            Expr::Repeat { ref child, lo, hi, .. } => {
                let analyzed_child = self.visit(child)?;
                min_size = analyzed_child.min_size * lo;
                const_size = analyzed_child.const_size && lo == hi;
                hard = analyzed_child.hard;
                looks_left = analyzed_child.looks_left;
                children.push(analyzed_child);
            }
            Expr::Delegate { size, .. } => {
                // currently only used for empty and single-char matches
                min_size = size;
                const_size = true;
                looks_left = size == 0;  // TODO: conservative for \z
            }
            Expr::Backref(group) => {
                if group >= self.group_ix {
                    return Err(Error::InvalidBackref);
                }
                hard = true;
            }
            Expr::AtomicGroup(ref child) => {
                let analyzed_child = self.visit(child)?;
                min_size = analyzed_child.min_size;
                const_size = analyzed_child.const_size;
                looks_left = analyzed_child.looks_left;
                hard = true;  // TODO: possibly could weaken
                children.push(analyzed_child);
            }
        };

        let analyzed_expr = AnalyzedExpr {
            expr: expr,
            children: children,
            start_group: start_group,
            end_group: self.group_ix,
            min_size: min_size,
            const_size: const_size,
            hard: hard,
            looks_left: looks_left,
        };
        Ok(analyzed_expr)
    }
}

fn literal_const_size(_: &str, _: bool) -> bool {
    // Right now, regex doesn't do sophisticated case folding,
    // test below will fail when that changes, then we need to
    // do something fancier here.
    true
}

pub fn analyze<'a>(expr: &'a Expr, backrefs: &'a BitSet) -> Result<AnalyzedExpr<'a>> {
    let mut analyzer = Analyzer {
        backrefs: backrefs,
        group_ix: 0,
    };

    analyzer.visit(expr)
}


#[cfg(test)]
mod tests {
    use regex;
    use Expr;
    use super::analyze;
    use super::literal_const_size;

    #[test]
    fn case_folding_safe() {
        let re = regex::Regex::new("(?i:ß)").unwrap();
        if re.is_match("SS") {
            assert!(!literal_const_size("ß", true));
        }

        // Another tricky example, Armenian ECH YIWN
        let re = regex::Regex::new("(?i:\\x{0587})").unwrap();
        if re.is_match("\u{0565}\u{0582}") {
            assert!(!literal_const_size("\u{0587}", true));
        }
    }

    #[test]
    fn invalid_backref_1() {
        let (e, backrefs) = Expr::parse(".\\0").unwrap();
        assert!(analyze(&e, &backrefs).is_err());
    }

    #[test]
    fn invalid_backref_2() {
        let (e, backrefs) = Expr::parse("(.\\1)").unwrap();
        assert!(analyze(&e, &backrefs).is_err());
    }

    #[test]
    fn invalid_backref_3() {
        let (e, backrefs) = Expr::parse("\\1(.)").unwrap();
        assert!(analyze(&e, &backrefs).is_err());
    }

    #[test]
    fn is_literal() {
        let (e, backrefs) = Expr::parse("abc").unwrap();
        let analyzed_expr = analyze(&e, &backrefs).unwrap();
        assert_eq!(analyzed_expr.is_literal(), true);
    }

    #[test]
    fn is_literal_with_repeat() {
        let (e, backrefs) = Expr::parse("abc*").unwrap();
        let analyzed_expr = analyze(&e, &backrefs).unwrap();
        assert_eq!(analyzed_expr.is_literal(), false);
    }
}
