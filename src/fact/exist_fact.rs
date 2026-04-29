// `exist` / `exist!` / `not exist`: same [`ExistFactBody`]; the outer variant selects the keyword.
// For `exist!`, verification may also discharge a companion uniqueness `forall`.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ExistFactEnum {
    ExistFact(ExistFactBody),
    ExistUniqueFact(ExistFactBody),
    NotExistFact(ExistFactBody),
}

#[derive(Clone)]
pub struct ExistFactBody {
    pub params_def_with_type: ParamDefWithType,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file: LineFile,
}

impl ExistFactBody {
    pub fn new(
        params_def_with_type: ParamDefWithType,
        facts: Vec<OrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Self {
        ExistFactBody {
            params_def_with_type,
            facts,
            line_file,
        }
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
}

impl ExistFactEnum {
    pub fn body(&self) -> &ExistFactBody {
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
        self.body().exist_fact_string_without_exist_as_prefix()
    }

    pub fn key(&self) -> String {
        let head = self.keyword_prefix();
        let b = self.body();
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

    /// Key for indexing `known_exist_facts_in_forall_facts`: exist witnesses renamed to `#0`, `#1`, …
    /// so different witness names match the same stored shape.
    pub fn alpha_normalized_key(&self) -> String {
        let b = self.body();
        let names = b.params_def_with_type.collect_param_names();
        let mut normalized_facts: Vec<OrAndChainAtomicFact> = b.facts.clone();
        for (i, name) in names.iter().enumerate() {
            let ph = format!("#{}", i);
            normalized_facts = normalized_facts
                .into_iter()
                .map(|f| f.replace_bound_identifier(name, &ph))
                .collect();
        }
        let head = self.keyword_prefix();
        format!(
            "{} {}{}{}",
            head,
            LEFT_CURLY_BRACE,
            vec_to_string_join_by_comma(
                &normalized_facts
                    .iter()
                    .map(|fact| fact.key())
                    .collect::<Vec<String>>()
            ),
            RIGHT_CURLY_BRACE
        )
    }

    pub fn line_file(&self) -> LineFile {
        self.body().line_file.clone()
    }

    pub fn params_def_with_type(&self) -> &ParamDefWithType {
        &self.body().params_def_with_type
    }

    pub fn facts(&self) -> &Vec<OrAndChainAtomicFact> {
        &self.body().facts
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        self.body().get_args_from_fact()
    }
}

fn exist_fact_string_without_exist_as_prefix(
    param_defs: &ParamDefWithType,
    facts: &Vec<OrAndChainAtomicFact>,
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = self.keyword_prefix();
        write!(
            f,
            "{} {}",
            head,
            self.exist_fact_string_without_exist_as_prefix()
        )
    }
}
