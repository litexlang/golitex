//! Matrix values, carriers, and matrix operations.

use crate::prelude::*;

#[derive(Clone)]
pub struct MatrixAdd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixSub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixMul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixScalarMul {
    pub scalar: Box<Obj>,
    pub matrix: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixPow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixSet {
    pub set: Box<Obj>,
    pub row_len: Box<Obj>,
    pub col_len: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixListObj {
    pub rows: Vec<Vec<Box<Obj>>>,
}

impl MatrixSet {
    pub fn new(set: Obj, row_len: Obj, col_len: Obj) -> Self {
        MatrixSet {
            set: Box::new(set),
            row_len: Box::new(row_len),
            col_len: Box::new(col_len),
        }
    }
}

impl MatrixListObj {
    pub fn new(rows: Vec<Vec<Obj>>) -> Self {
        MatrixListObj {
            rows: rows
                .into_iter()
                .map(|row| row.into_iter().map(Box::new).collect())
                .collect(),
        }
    }
}

impl MatrixAdd {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixAdd {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixSub {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixSub {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixMul {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixMul {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixScalarMul {
    pub fn new(scalar: Obj, matrix: Obj) -> Self {
        MatrixScalarMul {
            scalar: Box::new(scalar),
            matrix: Box::new(matrix),
        }
    }
}

impl MatrixPow {
    pub fn new(base: Obj, exponent: Obj) -> Self {
        MatrixPow {
            base: Box::new(base),
            exponent: Box::new(exponent),
        }
    }
}
