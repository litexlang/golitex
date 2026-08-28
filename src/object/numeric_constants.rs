//! Numeric literals and mathematical constants.

use crate::prelude::*;

#[derive(Clone)]
pub struct Number {
    pub normalized_value: String,
}

#[derive(Clone)]
pub struct ImaginaryUnit;

#[derive(Clone)]
pub struct EulerNumber;

#[derive(Clone)]
pub struct Pi;

impl Number {
    pub fn new(value: String) -> Self {
        Number {
            normalized_value: normalize_decimal_number_string(&value),
        }
    }
}

impl ImaginaryUnit {
    pub fn new() -> Self {
        ImaginaryUnit
    }
}

impl EulerNumber {
    pub fn new() -> Self {
        EulerNumber
    }
}

impl Pi {
    pub fn new() -> Self {
        Pi
    }
}
