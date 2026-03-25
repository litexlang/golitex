use crate::common::helper::{
    add_four_spaces_at_beginning, braced_vec_to_string,
    to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_with_sep,
};
use crate::common::keywords::{ALGO, CASE, COLON};
use crate::fact::AndChainAtomicFact;
use crate::obj::Obj;
use std::fmt;

// algo f(a, b):
//     case a > b: a
//     case a <= b: b
#[derive(Clone)]
pub struct DefAlgoStmt {
    pub name: String,
    pub params: Vec<String>,
    pub return_or_algo_case: Vec<AlgoReturnOrAlgoCase>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct AlgoReturn {
    pub value: Obj,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct AlgoCase {
    pub condition: AndChainAtomicFact,
    pub return_stmt: AlgoReturn,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub enum AlgoReturnOrAlgoCase {
    AlgoReturn(AlgoReturn),
    AlgoCase(AlgoCase),
}

impl DefAlgoStmt {
    pub fn new(
        name: String,
        params: Vec<String>,
        return_or_algo_case: Vec<AlgoReturnOrAlgoCase>,
        line_file: (usize, usize),
    ) -> Self {
        DefAlgoStmt {
            name,
            params,
            return_or_algo_case,
            line_file,
        }
    }
}

impl fmt::Display for AlgoReturnOrAlgoCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AlgoReturnOrAlgoCase::AlgoReturn(algo_return) => write!(f, "{}", algo_return),
            AlgoReturnOrAlgoCase::AlgoCase(algo_case) => write!(f, "{}", algo_case),
        }
    }
}

impl fmt::Display for AlgoReturn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", (&self.value))
    }
}

impl fmt::Display for AlgoCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{} {}",
            CASE,
            self.condition,
            COLON,
            add_four_spaces_at_beginning(self.return_stmt.to_string(), 1)
        )
    }
}

impl fmt::Display for DefAlgoStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}\n{}",
            ALGO,
            self.name,
            braced_vec_to_string(&self.params),
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &vec_to_string_with_sep(&self.return_or_algo_case, "\n".to_string()),
                1
            )
        )
    }
}

impl AlgoReturn {
    pub fn new(value: Obj, line_file: (usize, usize)) -> Self {
        AlgoReturn { value, line_file }
    }
}

impl AlgoCase {
    pub fn new(
        condition: AndChainAtomicFact,
        return_stmt: AlgoReturn,
        line_file: (usize, usize),
    ) -> Self {
        AlgoCase {
            condition,
            return_stmt,
            line_file,
        }
    }
}

impl AlgoReturnOrAlgoCase {
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            AlgoReturnOrAlgoCase::AlgoReturn(algo_return) => algo_return.line_file,
            AlgoReturnOrAlgoCase::AlgoCase(algo_case) => algo_case.line_file,
        }
    }
}
