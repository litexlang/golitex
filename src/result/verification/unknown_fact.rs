//! Structured unknown outcomes for fact verification.

use crate::prelude::*;
use std::fmt;

#[derive(Debug, Clone)]
pub struct UnknownFactParam {
    pub name: String,
    pub type_text: String,
}

#[derive(Debug, Clone)]
pub struct UnknownFactPart {
    pub index: usize,
    pub count: usize,
    pub stmt: Fact,
    pub unknown: Option<Box<UnknownFactResult>>,
}

#[derive(Debug, Clone)]
pub struct UnknownAtomicFactResult {
    pub goal: Fact,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownExistFactResult {
    pub goal: Fact,
    pub witness_params: Vec<UnknownFactParam>,
    pub body: Vec<Fact>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownOrFactResult {
    pub goal: Fact,
    pub branches: Vec<Fact>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownAndFactResult {
    pub goal: Fact,
    pub failed_part: Option<UnknownFactPart>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownChainFactResult {
    pub goal: Fact,
    pub failed_part: Option<UnknownFactPart>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownForallFactResult {
    pub goal: Fact,
    pub params: Vec<UnknownFactParam>,
    pub requirements: Vec<Fact>,
    pub failed_prove: Option<UnknownFactPart>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownForallFactWithIffResult {
    pub goal: Fact,
    pub params: Vec<UnknownFactParam>,
    pub requirements: Vec<Fact>,
    pub failed_direction: Option<String>,
    pub child_unknown: Option<Box<UnknownFactResult>>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct UnknownNotForallFactResult {
    pub goal: Fact,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub enum UnknownFactResult {
    AtomicFact(Box<UnknownAtomicFactResult>),
    ExistFact(Box<UnknownExistFactResult>),
    OrFact(Box<UnknownOrFactResult>),
    AndFact(Box<UnknownAndFactResult>),
    ChainFact(Box<UnknownChainFactResult>),
    ForallFact(Box<UnknownForallFactResult>),
    ForallFactWithIff(Box<UnknownForallFactWithIffResult>),
    NotForall(Box<UnknownNotForallFactResult>),
}

impl fmt::Display for UnknownFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", UNKNOWN_COLON)?;
        let goal = self.goal().to_string();
        if !goal.is_empty() {
            write!(f, " {}", goal)?;
        }
        if let Some(detail_lines) = self.detail() {
            if !detail_lines.is_empty() {
                write!(f, "\n{}", detail_lines.join("\n"))?;
            }
        }
        Ok(())
    }
}

impl UnknownFactParam {
    pub fn new(name: String, type_text: String) -> Self {
        Self { name, type_text }
    }
}

impl UnknownFactPart {
    pub fn new(index: usize, count: usize, stmt: Fact, unknown: Option<UnknownFactResult>) -> Self {
        UnknownFactPart {
            index,
            count,
            stmt,
            unknown: unknown.map(Box::new),
        }
    }
}

impl UnknownFactResult {
    pub fn new(goal: Fact) -> Self {
        Self::new_with_detail_lines(goal, vec![])
    }

    pub fn from_stmt_unknown(goal: Fact, unknown: UnknownGenericStmtResult) -> Self {
        Self::new_with_detail_lines(goal, unknown.detail.unwrap_or_default())
    }

    pub fn new_with_detail_lines(goal: Fact, detail_lines: Vec<String>) -> Self {
        let detail = normalize_detail_lines(detail_lines);
        match goal.clone() {
            Fact::AtomicFact(_) => {
                UnknownFactResult::AtomicFact(Box::new(UnknownAtomicFactResult { goal, detail }))
            }
            Fact::ExistFact(exist_fact) => {
                UnknownFactResult::ExistFact(Box::new(UnknownExistFactResult {
                    goal,
                    witness_params: params_for_output(exist_fact.params_def_with_type()),
                    body: exist_fact
                        .facts()
                        .iter()
                        .map(QuantifierFreeFact::from_ref_to_cloned_fact)
                        .collect(),
                    detail,
                }))
            }
            Fact::OrFact(or_fact) => UnknownFactResult::OrFact(Box::new(UnknownOrFactResult {
                goal,
                branches: or_fact
                    .facts
                    .iter()
                    .map(|fact| fact.clone().into())
                    .collect(),
                detail,
            })),
            Fact::AndFact(_) => UnknownFactResult::AndFact(Box::new(UnknownAndFactResult {
                goal,
                failed_part: None,
                detail,
            })),
            Fact::ChainFact(_) => UnknownFactResult::ChainFact(Box::new(UnknownChainFactResult {
                goal,
                failed_part: None,
                detail,
            })),
            Fact::ForallFact(forall_fact) => {
                UnknownFactResult::ForallFact(Box::new(UnknownForallFactResult {
                    goal,
                    params: params_for_output(&forall_fact.params_def_with_type),
                    requirements: forall_fact.dom_facts.clone(),
                    failed_prove: None,
                    detail,
                }))
            }
            Fact::ForallFactWithIff(forall_iff) => {
                UnknownFactResult::ForallFactWithIff(Box::new(UnknownForallFactWithIffResult {
                    goal,
                    params: params_for_output(&forall_iff.forall_fact.params_def_with_type),
                    requirements: forall_iff.forall_fact.dom_facts.clone(),
                    failed_direction: None,
                    child_unknown: None,
                    detail,
                }))
            }
            Fact::NotForall(_) => {
                UnknownFactResult::NotForall(Box::new(UnknownNotForallFactResult { goal, detail }))
            }
        }
    }

    pub fn and_with_failed_part(
        and_fact: AndFact,
        index: usize,
        count: usize,
        stmt: Fact,
        child_unknown: Option<UnknownFactResult>,
    ) -> Self {
        UnknownFactResult::AndFact(Box::new(UnknownAndFactResult {
            goal: and_fact.into(),
            failed_part: Some(UnknownFactPart::new(index, count, stmt, child_unknown)),
            detail: None,
        }))
    }

    pub fn chain_with_failed_part(
        chain_fact: ChainFact,
        index: usize,
        count: usize,
        stmt: Fact,
        child_unknown: Option<UnknownFactResult>,
        detail_lines: Vec<String>,
    ) -> Self {
        UnknownFactResult::ChainFact(Box::new(UnknownChainFactResult {
            goal: chain_fact.into(),
            failed_part: Some(UnknownFactPart::new(index, count, stmt, child_unknown)),
            detail: normalize_detail_lines(detail_lines),
        }))
    }

    pub fn forall_with_failed_prove(
        forall_fact: ForallFact,
        index: usize,
        count: usize,
        stmt: Fact,
        child_unknown: Option<UnknownFactResult>,
        detail_lines: Vec<String>,
    ) -> Self {
        UnknownFactResult::ForallFact(Box::new(UnknownForallFactResult {
            goal: forall_fact.clone().into(),
            params: params_for_output(&forall_fact.params_def_with_type),
            requirements: forall_fact.dom_facts.clone(),
            failed_prove: Some(UnknownFactPart::new(index, count, stmt, child_unknown)),
            detail: normalize_detail_lines(detail_lines),
        }))
    }

    pub fn forall_iff_with_failed_direction(
        forall_iff: ForallFactWithIff,
        failed_direction: String,
        child_unknown: Option<UnknownFactResult>,
    ) -> Self {
        UnknownFactResult::ForallFactWithIff(Box::new(UnknownForallFactWithIffResult {
            goal: forall_iff.clone().into(),
            params: params_for_output(&forall_iff.forall_fact.params_def_with_type),
            requirements: forall_iff.forall_fact.dom_facts.clone(),
            failed_direction: Some(failed_direction),
            child_unknown: child_unknown.map(Box::new),
            detail: None,
        }))
    }

    pub fn goal(&self) -> &Fact {
        match self {
            UnknownFactResult::AtomicFact(x) => &x.goal,
            UnknownFactResult::ExistFact(x) => &x.goal,
            UnknownFactResult::OrFact(x) => &x.goal,
            UnknownFactResult::AndFact(x) => &x.goal,
            UnknownFactResult::ChainFact(x) => &x.goal,
            UnknownFactResult::ForallFact(x) => &x.goal,
            UnknownFactResult::ForallFactWithIff(x) => &x.goal,
            UnknownFactResult::NotForall(x) => &x.goal,
        }
    }

    pub fn detail(&self) -> Option<&Vec<String>> {
        match self {
            UnknownFactResult::AtomicFact(x) => x.detail.as_ref(),
            UnknownFactResult::ExistFact(x) => x.detail.as_ref(),
            UnknownFactResult::OrFact(x) => x.detail.as_ref(),
            UnknownFactResult::AndFact(x) => x.detail.as_ref(),
            UnknownFactResult::ChainFact(x) => x.detail.as_ref(),
            UnknownFactResult::ForallFact(x) => x.detail.as_ref(),
            UnknownFactResult::ForallFactWithIff(x) => x.detail.as_ref(),
            UnknownFactResult::NotForall(x) => x.detail.as_ref(),
        }
    }
}

fn params_for_output(param_defs: &ParamDefWithType) -> Vec<UnknownFactParam> {
    let mut params = Vec::new();
    for (name, param_type) in param_defs.collect_param_names_with_types() {
        params.push(UnknownFactParam::new(name, param_type.to_string()));
    }
    params
}

fn normalize_detail_lines(detail_lines: Vec<String>) -> Option<Vec<String>> {
    if detail_lines.is_empty() {
        None
    } else {
        Some(detail_lines)
    }
}
