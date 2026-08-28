//! Integer ranges and sequence objects.

use crate::prelude::*;

#[derive(Clone)]
pub struct Range {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

#[derive(Clone)]
pub struct ClosedRange {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

/// Set of functions `fn(x N+: x <= n) s` (Lit surface syntax: keyword `finite_seq(s, n)`).
#[derive(Clone)]
pub struct FiniteSeqSet {
    pub set: Box<Obj>,
    pub n: Box<Obj>,
}

/// `seq(s)` — functions `fn(x N+) s` (no length bound; surface: keyword `seq(s)`).
#[derive(Clone)]
pub struct SeqSet {
    pub set: Box<Obj>,
}

/// Literal `[a, b, ...]` as a finite sequence value (for membership in `finite_seq(s, n)`).
#[derive(Clone)]
pub struct FiniteSeqListObj {
    pub objs: Vec<Box<Obj>>,
}

impl Range {
    pub fn new(start: Obj, end: Obj) -> Self {
        Range {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl ClosedRange {
    pub fn new(start: Obj, end: Obj) -> Self {
        ClosedRange {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl FiniteSeqSet {
    pub fn new(set: Obj, n: Obj) -> Self {
        FiniteSeqSet {
            set: Box::new(set),
            n: Box::new(n),
        }
    }
}

impl SeqSet {
    pub fn new(set: Obj) -> Self {
        SeqSet { set: Box::new(set) }
    }
}

impl FiniteSeqListObj {
    pub fn new(objs: Vec<Obj>) -> Self {
        FiniteSeqListObj {
            objs: objs.into_iter().map(Box::new).collect(),
        }
    }
}
