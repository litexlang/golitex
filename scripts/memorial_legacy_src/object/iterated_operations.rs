//! Indexed and finite-set folds, sums, and products.

use crate::prelude::*;

#[derive(Clone)]
pub struct Sum {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct SumOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct Product {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct ProductOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

/// An ascending left fold over the closed integer interval `[start, end]`.
/// The empty interval evaluates to `seed`.
#[derive(Clone)]
pub struct Reduce {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

/// An order-independent fold over a finite set. Well-definedness requires
/// `op` to be associative and commutative on its carrier.
#[derive(Clone)]
pub struct FiniteSetReduce {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

impl Sum {
    pub fn new(start: Obj, end: Obj, func: Obj) -> Self {
        Sum {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
        }
    }
}

impl SumOfFiniteSet {
    pub fn new(set: Obj, func: Obj) -> Self {
        SumOfFiniteSet {
            set: Box::new(set),
            func: Box::new(func),
        }
    }
}

impl Product {
    pub fn new(start: Obj, end: Obj, func: Obj) -> Self {
        Product {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
        }
    }
}

impl ProductOfFiniteSet {
    pub fn new(set: Obj, func: Obj) -> Self {
        ProductOfFiniteSet {
            set: Box::new(set),
            func: Box::new(func),
        }
    }
}

impl Reduce {
    pub fn new(start: Obj, end: Obj, func: Obj, op: Obj, seed: Obj) -> Self {
        Reduce {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
            op: Box::new(op),
            seed: Box::new(seed),
        }
    }
}

impl FiniteSetReduce {
    pub fn new(set: Obj, func: Obj, op: Obj, seed: Obj) -> Self {
        FiniteSetReduce {
            set: Box::new(set),
            func: Box::new(func),
            op: Box::new(op),
            seed: Box::new(seed),
        }
    }
}
