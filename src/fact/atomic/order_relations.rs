//! Strict and non-strict order relation facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct LessFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotLessFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct GreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotGreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct LessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotLessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct GreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotGreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

impl LessFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        LessFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotLessFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotLessFact {
            left,
            right,
            line_file,
        }
    }
}

impl GreaterFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        GreaterFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotGreaterFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotGreaterFact {
            left,
            right,
            line_file,
        }
    }
}

impl LessEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        LessEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotLessEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotLessEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl GreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        GreaterEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotGreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotGreaterEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl fmt::Display for LessFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, LESS, self.right)
    }
}

impl fmt::Display for NotLessFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {} {}", NOT, self.left, LESS, self.right)
    }
}

impl fmt::Display for GreaterFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, GREATER, self.right)
    }
}

impl fmt::Display for NotGreaterFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {} {}", NOT, self.left, GREATER, self.right)
    }
}

impl fmt::Display for LessEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, LESS_EQUAL, self.right)
    }
}

impl fmt::Display for NotLessEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {} {}", NOT, self.left, LESS_EQUAL, self.right)
    }
}

impl fmt::Display for GreaterEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, GREATER_EQUAL, self.right)
    }
}

impl fmt::Display for NotGreaterEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {} {}", NOT, self.left, GREATER_EQUAL, self.right)
    }
}
