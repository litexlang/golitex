use crate::prelude::*;
use std::fmt;

// algo f(a, b):
//     case a > b: a
//     case a <= b: b
#[derive(Clone)]
pub struct DefAlgoStmt {
    pub name: String,
    pub params: Vec<String>,
    pub default_return: Option<AlgoReturn>,
    pub cases: Vec<AlgoCase>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct AlgoReturn {
    pub value: Obj,
    pub line_file: LineFile,
}
#[derive(Clone)]
pub struct AlgoCase {
    pub condition: AtomicFact, // 只有 atomic fact 能reverse，而 algo case 有可能需要被reverse掉（处理 default_return 的时候）。
    pub return_stmt: AlgoReturn,
    pub line_file: LineFile,
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
        cases: Vec<AlgoCase>,
        default_return: Option<AlgoReturn>,
        line_file: LineFile,
    ) -> Self {
        DefAlgoStmt {
            name,
            params,
            default_return,
            cases,
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
        if let Some(default_return) = &self.default_return {
            write!(
                f,
                "{} {}{}{}\n{}\n{}",
                ALGO,
                self.name,
                braced_vec_to_string(&self.params),
                COLON,
                to_string_and_add_four_spaces_at_beginning_of_each_line(
                    &vec_to_string_with_sep(&self.cases, "\n".to_string()),
                    1
                ),
                default_return
            )
        } else {
            write!(
                f,
                "{} {}{}{}\n{}",
                ALGO,
                self.name,
                braced_vec_to_string(&self.params),
                COLON,
                to_string_and_add_four_spaces_at_beginning_of_each_line(
                    &vec_to_string_with_sep(&self.cases, "\n".to_string()),
                    1
                )
            )
        }
    }
}

impl AlgoReturn {
    pub fn new(value: Obj, line_file: LineFile) -> Self {
        AlgoReturn { value, line_file }
    }
}

impl AlgoCase {
    pub fn new(condition: AtomicFact, return_stmt: AlgoReturn, line_file: LineFile) -> Self {
        AlgoCase {
            condition,
            return_stmt,
            line_file,
        }
    }
}

impl AlgoReturnOrAlgoCase {
    pub fn line_file(&self) -> LineFile {
        match self {
            AlgoReturnOrAlgoCase::AlgoReturn(algo_return) => algo_return.line_file.clone(),
            AlgoReturnOrAlgoCase::AlgoCase(algo_case) => algo_case.line_file.clone(),
        }
    }
}
