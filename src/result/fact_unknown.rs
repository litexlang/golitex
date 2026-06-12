use crate::prelude::*;
use std::fmt;

#[derive(Debug, Clone)]
pub struct FactUnknownParam {
    pub name: String,
    pub type_text: String,
}

#[derive(Debug, Clone)]
pub struct FactUnknownPart {
    pub index: usize,
    pub count: usize,
    pub stmt: Fact,
    pub unknown: Option<Box<FactUnknown>>,
}

#[derive(Debug, Clone)]
pub struct AtomicFactUnknown {
    pub goal: Fact,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct ExistFactUnknown {
    pub goal: Fact,
    pub witness_params: Vec<FactUnknownParam>,
    pub body: Vec<Fact>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct OrFactUnknown {
    pub goal: Fact,
    pub branches: Vec<Fact>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct AndFactUnknown {
    pub goal: Fact,
    pub failed_part: Option<FactUnknownPart>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct ChainFactUnknown {
    pub goal: Fact,
    pub failed_part: Option<FactUnknownPart>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct ForallFactUnknown {
    pub goal: Fact,
    pub params: Vec<FactUnknownParam>,
    pub requirements: Vec<Fact>,
    pub failed_prove: Option<FactUnknownPart>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct ForallFactWithIffUnknown {
    pub goal: Fact,
    pub params: Vec<FactUnknownParam>,
    pub requirements: Vec<Fact>,
    pub failed_direction: Option<String>,
    pub child_unknown: Option<Box<FactUnknown>>,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub struct NotForallUnknown {
    pub goal: Fact,
    pub detail: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub enum FactUnknown {
    AtomicFact(Box<AtomicFactUnknown>),
    ExistFact(Box<ExistFactUnknown>),
    OrFact(Box<OrFactUnknown>),
    AndFact(Box<AndFactUnknown>),
    ChainFact(Box<ChainFactUnknown>),
    ForallFact(Box<ForallFactUnknown>),
    ForallFactWithIff(Box<ForallFactWithIffUnknown>),
    NotForall(Box<NotForallUnknown>),
}

impl fmt::Display for FactUnknown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

impl FactUnknownParam {
    pub fn new(name: String, type_text: String) -> Self {
        Self { name, type_text }
    }
}

impl FactUnknownPart {
    pub fn new(index: usize, count: usize, stmt: Fact, unknown: Option<FactUnknown>) -> Self {
        FactUnknownPart {
            index,
            count,
            stmt,
            unknown: unknown.map(Box::new),
        }
    }
}

impl FactUnknown {
    pub fn new(goal: Fact) -> Self {
        Self::new_with_detail_lines(goal, vec![])
    }

    pub fn from_stmt_unknown(goal: Fact, unknown: StmtUnknown) -> Self {
        Self::new_with_detail_lines(goal, unknown.detail.unwrap_or_default())
    }

    pub fn new_with_detail_lines(goal: Fact, detail_lines: Vec<String>) -> Self {
        let detail = normalize_detail_lines(detail_lines);
        match goal.clone() {
            Fact::AtomicFact(_) => {
                FactUnknown::AtomicFact(Box::new(AtomicFactUnknown { goal, detail }))
            }
            Fact::ExistFact(exist_fact) => FactUnknown::ExistFact(Box::new(ExistFactUnknown {
                goal,
                witness_params: params_for_output(exist_fact.params_def_with_type()),
                body: exist_fact
                    .facts()
                    .iter()
                    .map(ExistBodyFact::from_ref_to_cloned_fact)
                    .collect(),
                detail,
            })),
            Fact::OrFact(or_fact) => FactUnknown::OrFact(Box::new(OrFactUnknown {
                goal,
                branches: or_fact
                    .facts
                    .iter()
                    .map(|fact| fact.clone().into())
                    .collect(),
                detail,
            })),
            Fact::AndFact(_) => FactUnknown::AndFact(Box::new(AndFactUnknown {
                goal,
                failed_part: None,
                detail,
            })),
            Fact::ChainFact(_) => FactUnknown::ChainFact(Box::new(ChainFactUnknown {
                goal,
                failed_part: None,
                detail,
            })),
            Fact::ForallFact(forall_fact) => FactUnknown::ForallFact(Box::new(ForallFactUnknown {
                goal,
                params: params_for_output(&forall_fact.params_def_with_type),
                requirements: forall_fact.dom_facts.clone(),
                failed_prove: None,
                detail,
            })),
            Fact::ForallFactWithIff(forall_iff) => {
                FactUnknown::ForallFactWithIff(Box::new(ForallFactWithIffUnknown {
                    goal,
                    params: params_for_output(&forall_iff.forall_fact.params_def_with_type),
                    requirements: forall_iff.forall_fact.dom_facts.clone(),
                    failed_direction: None,
                    child_unknown: None,
                    detail,
                }))
            }
            Fact::NotForall(_) => {
                FactUnknown::NotForall(Box::new(NotForallUnknown { goal, detail }))
            }
        }
    }

    pub fn and_with_failed_part(
        and_fact: AndFact,
        index: usize,
        count: usize,
        stmt: Fact,
        child_unknown: Option<FactUnknown>,
    ) -> Self {
        FactUnknown::AndFact(Box::new(AndFactUnknown {
            goal: and_fact.into(),
            failed_part: Some(FactUnknownPart::new(index, count, stmt, child_unknown)),
            detail: None,
        }))
    }

    pub fn chain_with_failed_part(
        chain_fact: ChainFact,
        index: usize,
        count: usize,
        stmt: Fact,
        child_unknown: Option<FactUnknown>,
        detail_lines: Vec<String>,
    ) -> Self {
        FactUnknown::ChainFact(Box::new(ChainFactUnknown {
            goal: chain_fact.into(),
            failed_part: Some(FactUnknownPart::new(index, count, stmt, child_unknown)),
            detail: normalize_detail_lines(detail_lines),
        }))
    }

    pub fn forall_with_failed_prove(
        forall_fact: ForallFact,
        index: usize,
        count: usize,
        stmt: Fact,
        child_unknown: Option<FactUnknown>,
        detail_lines: Vec<String>,
    ) -> Self {
        FactUnknown::ForallFact(Box::new(ForallFactUnknown {
            goal: forall_fact.clone().into(),
            params: params_for_output(&forall_fact.params_def_with_type),
            requirements: forall_fact.dom_facts.clone(),
            failed_prove: Some(FactUnknownPart::new(index, count, stmt, child_unknown)),
            detail: normalize_detail_lines(detail_lines),
        }))
    }

    pub fn forall_iff_with_failed_direction(
        forall_iff: ForallFactWithIff,
        failed_direction: String,
        child_unknown: Option<FactUnknown>,
    ) -> Self {
        FactUnknown::ForallFactWithIff(Box::new(ForallFactWithIffUnknown {
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
            FactUnknown::AtomicFact(x) => &x.goal,
            FactUnknown::ExistFact(x) => &x.goal,
            FactUnknown::OrFact(x) => &x.goal,
            FactUnknown::AndFact(x) => &x.goal,
            FactUnknown::ChainFact(x) => &x.goal,
            FactUnknown::ForallFact(x) => &x.goal,
            FactUnknown::ForallFactWithIff(x) => &x.goal,
            FactUnknown::NotForall(x) => &x.goal,
        }
    }

    pub fn detail(&self) -> Option<&Vec<String>> {
        match self {
            FactUnknown::AtomicFact(x) => x.detail.as_ref(),
            FactUnknown::ExistFact(x) => x.detail.as_ref(),
            FactUnknown::OrFact(x) => x.detail.as_ref(),
            FactUnknown::AndFact(x) => x.detail.as_ref(),
            FactUnknown::ChainFact(x) => x.detail.as_ref(),
            FactUnknown::ForallFact(x) => x.detail.as_ref(),
            FactUnknown::ForallFactWithIff(x) => x.detail.as_ref(),
            FactUnknown::NotForall(x) => x.detail.as_ref(),
        }
    }
}

fn params_for_output(param_defs: &ParamDefWithType) -> Vec<FactUnknownParam> {
    let mut params = Vec::new();
    for (name, param_type) in param_defs.collect_param_names_with_types() {
        params.push(FactUnknownParam::new(name, param_type.to_string()));
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
