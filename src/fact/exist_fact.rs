// `exist` / `exist!` / `not exist`: same [`ExistentialSpec`]; the outer variant selects the keyword.
// For `exist!`, verification may also discharge a companion uniqueness `forall`.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ExistFactEnum {
    ExistFact(ExistentialSpec),
    ExistUniqueFact(ExistentialSpec),
    NotExistFact(ExistentialSpec),
}

#[derive(Clone)]
pub struct ExistentialSpec {
    pub params_def_with_type: ParamDefWithType,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: LineFile,
}

impl ExistentialSpec {
    pub fn new(
        params_def_with_type: ParamDefWithType,
        facts: Vec<QuantifierFreeFact>,
        line_file: LineFile,
    ) -> Result<Self, RuntimeError> {
        let spec = ExistentialSpec {
            params_def_with_type,
            facts,
            line_file,
        };
        check_exist_fact_has_no_duplicate_exist_free_parameter(&ExistFactEnum::ExistFact(
            spec.clone(),
        ))?;
        Ok(spec)
    }

    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        let mut args: Vec<Obj> = Vec::new();
        for param_def_with_type in self.params_def_with_type.groups.iter() {
            if let ParamType::Obj(obj) = &param_def_with_type.param_type {
                args.push(obj.clone());
            }
        }

        for fact in self.facts.iter() {
            for arg in fact.get_args_from_fact() {
                args.push(arg);
            }
        }

        args
    }

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        let mut args: Vec<&Obj> = Vec::new();
        for param_def_with_type in self.params_def_with_type.groups.iter() {
            if let ParamType::Obj(obj) = &param_def_with_type.param_type {
                args.push(obj);
            }
        }

        for fact in self.facts.iter() {
            args.extend(fact.get_args_from_fact_ref());
        }

        args
    }
}

impl ExistFactEnum {
    pub fn spec(&self) -> &ExistentialSpec {
        match self {
            ExistFactEnum::ExistFact(b)
            | ExistFactEnum::ExistUniqueFact(b)
            | ExistFactEnum::NotExistFact(b) => b,
        }
    }

    pub fn is_exist_unique(&self) -> bool {
        matches!(self, ExistFactEnum::ExistUniqueFact(_))
    }

    pub fn is_not_exist(&self) -> bool {
        matches!(self, ExistFactEnum::NotExistFact(_))
    }

    pub fn is_plain_exist(&self) -> bool {
        matches!(self, ExistFactEnum::ExistFact(_))
    }

    pub fn keyword_prefix(&self) -> String {
        if self.is_not_exist() {
            format!("{} {}", NOT, EXIST)
        } else if self.is_exist_unique() {
            EXIST_BANG.to_string()
        } else {
            EXIST.to_string()
        }
    }

    /// Whether a stored exist fact can directly verify the `goal`.
    /// `exist!` can verify `exist`, but other cross-variant matches are rejected.
    pub fn can_be_used_to_verify_goal(&self, goal: &ExistFactEnum) -> bool {
        match self {
            ExistFactEnum::ExistFact(_) => goal.is_plain_exist(),
            ExistFactEnum::ExistUniqueFact(_) => goal.is_plain_exist() || goal.is_exist_unique(),
            ExistFactEnum::NotExistFact(_) => goal.is_not_exist(),
        }
    }

    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        self.spec().exist_fact_string_without_exist_as_prefix()
    }

    pub fn key(&self) -> String {
        let head = self.keyword_prefix();
        let b = self.spec();
        format!(
            "{} {}{}{}",
            head,
            LEFT_CURLY_BRACE,
            vec_to_string_join_by_comma(
                &b.facts
                    .iter()
                    .map(|fact| fact.key())
                    .collect::<Vec<String>>()
            ),
            RIGHT_CURLY_BRACE
        )
    }

    /// Conservative alpha-invariant bucket for existential facts stored under a forall.
    /// Exact typed matching is still required after lookup; this key intentionally contains no
    /// object names, so captured identifiers can never be rewritten as witness binders here.
    pub fn alpha_normalized_key(&self) -> String {
        let b = self.spec();
        let fact_shape = b
            .facts
            .iter()
            .map(|fact| match fact {
                QuantifierFreeFact::AtomicFact(_) => "atomic",
                QuantifierFreeFact::AndFact(_) => "and",
                QuantifierFreeFact::ChainFact(_) => "chain",
                QuantifierFreeFact::OrFact(_) => "or",
            })
            .collect::<Vec<&str>>()
            .join(",");
        format!(
            "#exist-alpha-bucket:{}:{}:{}",
            self.keyword_prefix(),
            b.params_def_with_type.number_of_params(),
            fact_shape
        )
    }

    pub fn line_file(&self) -> LineFile {
        self.spec().line_file.clone()
    }

    pub fn params_def_with_type(&self) -> &ParamDefWithType {
        &self.spec().params_def_with_type
    }

    pub fn facts(&self) -> &Vec<QuantifierFreeFact> {
        &self.spec().facts
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        self.spec().get_args_from_fact()
    }

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        self.spec().get_args_from_fact_ref()
    }
}

fn exist_fact_string_without_exist_as_prefix(
    param_defs: &ParamDefWithType,
    facts: &Vec<QuantifierFreeFact>,
) -> String {
    format!(
        "{} {} {}",
        param_defs.to_string(),
        ST,
        curly_braced_vec_to_string_with_sep(
            &facts
                .iter()
                .map(|fact| fact.to_string())
                .collect::<Vec<String>>(),
            format!("{} ", COMMA)
        )
    )
}

impl fmt::Display for ExistFactEnum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let head = self.keyword_prefix();
        write!(
            f,
            "{} {}",
            head,
            self.exist_fact_string_without_exist_as_prefix()
        )
    }
}
