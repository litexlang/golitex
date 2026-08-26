use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByClosedRangeAsCasesStmt {
    pub element: Obj,
    pub closed_range: ClosedRange,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct ByEnumerateRangeStmt {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub line_file: LineFile,
}

impl fmt::Display for ByEnumerateRangeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let keyword = match &self.range {
            ClosedRangeOrRange::ClosedRange(_) => CLOSED_RANGE,
            ClosedRangeOrRange::Range(_) => RANGE,
        };
        write!(
            f,
            "{} {} {}{} {} {}{} {}",
            BY, ENUMERATE, keyword, COLON, self.element, FACT_PREFIX, IN, self.range
        )
    }
}

impl ByEnumerateRangeStmt {
    pub fn new(element: Obj, range: ClosedRangeOrRange, line_file: LineFile) -> Self {
        ByEnumerateRangeStmt {
            element,
            range,
            line_file,
        }
    }
}

impl fmt::Display for ByClosedRangeAsCasesStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {} {}{} {} {}{} {}",
            BY,
            CLOSED_RANGE,
            AS,
            CASES,
            COLON,
            self.element,
            FACT_PREFIX,
            IN,
            Obj::ClosedRange(self.closed_range.clone())
        )
    }
}

impl ByClosedRangeAsCasesStmt {
    pub fn new(element: Obj, closed_range: ClosedRange, line_file: LineFile) -> Self {
        ByClosedRangeAsCasesStmt {
            element,
            closed_range,
            line_file,
        }
    }
}
