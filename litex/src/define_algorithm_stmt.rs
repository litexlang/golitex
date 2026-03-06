use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::obj::Obj;
use crate::helper::{add_four_spaces_at_beginning, vec_to_string_with_sep, to_string_and_add_four_spaces_at_beginning_of_each_line, braced_vec_to_string};
use crate::keywords::{RETURN, IF, COLON, ALGO};
use std::fmt;

#[derive(Clone)]
pub struct DefAlgoStmt {
    pub name: String,
    pub params: Vec<String>,
    pub return_or_algo_if: Vec<AlgoReturnOrAlgoIf>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct AlgoReturn {
    pub value: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct AlgoIf {
    pub condition: AndFactOrSpecFact,
    pub return_stmt: AlgoReturn,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub enum AlgoReturnOrAlgoIf {
    AlgoReturn(AlgoReturn),
    AlgoIf(AlgoIf),
}

impl DefAlgoStmt {
    pub fn new(name: String, params: Vec<String>, return_or_algo_if: Vec<AlgoReturnOrAlgoIf>, line_file_index: Option<(usize, usize)>) -> Self {
        DefAlgoStmt { name, params, return_or_algo_if, line_file_index }
    }
}

impl fmt::Display for AlgoReturnOrAlgoIf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AlgoReturnOrAlgoIf::AlgoReturn(algo_return) => write!(f, "{}", algo_return),
            AlgoReturnOrAlgoIf::AlgoIf(algo_if) => write!(f, "{}", algo_if),
        }
    }
}

impl fmt::Display for AlgoReturn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", RETURN, (&self.value))
    }
}

impl fmt::Display for AlgoIf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}\n{}", IF, self.condition, COLON, add_four_spaces_at_beginning(&self.return_stmt.to_string(), 1))
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
            to_string_and_add_four_spaces_at_beginning_of_each_line(&vec_to_string_with_sep(&self.return_or_algo_if, "\n"), 1)
        )
    }
}

impl AlgoReturn {
    pub fn new(value: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        AlgoReturn { value, line_file_index }
    }
}

impl AlgoIf {
    pub fn new(condition: AndFactOrSpecFact, return_stmt: AlgoReturn, line_file_index: Option<(usize, usize)>) -> Self {
        AlgoIf { condition, return_stmt, line_file_index }
    }
}

impl AlgoReturnOrAlgoIf {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            AlgoReturnOrAlgoIf::AlgoReturn(algo_return) => algo_return.line_file_index,
            AlgoReturnOrAlgoIf::AlgoIf(algo_if) => algo_if.line_file_index,
        }
    }
}