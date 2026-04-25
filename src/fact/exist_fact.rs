// `exist` vs `exist_unique`: same [`ExistFactBody`]; the outer [`ExistFactEnum`] variant selects the keyword.
// For `exist_unique`, verification may also discharge a companion uniqueness `forall`.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ExistFactEnum {
    ExistFact(ExistFactBody),
    ExistUniqueFact(ExistFactBody),
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

    pub fn with_new_line_file(self, line_file: LineFile) -> Self {
        ExistFactBody {
            params_def_with_type: self.params_def_with_type,
            facts: self
                .facts
                .into_iter()
                .map(|x| x.with_new_line_file(line_file.clone()))
                .collect(),
            line_file,
        }
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
            ExistFactEnum::ExistFact(b) | ExistFactEnum::ExistUniqueFact(b) => b,
        }
    }

    pub fn is_exist_unique(&self) -> bool {
        matches!(self, ExistFactEnum::ExistUniqueFact(_))
    }

    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        self.body().exist_fact_string_without_exist_as_prefix()
    }

    pub fn key(&self) -> String {
        let head = if self.is_exist_unique() {
            EXIST_UNIQUE
        } else {
            EXIST
        };
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
        let head = if self.is_exist_unique() {
            EXIST_UNIQUE
        } else {
            EXIST
        };
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

    pub fn with_new_line_file(self, line_file: LineFile) -> Self {
        match self {
            ExistFactEnum::ExistFact(b) => ExistFactEnum::ExistFact(b.with_new_line_file(line_file)),
            ExistFactEnum::ExistUniqueFact(b) => {
                ExistFactEnum::ExistUniqueFact(b.with_new_line_file(line_file))
            }
        }
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
        let head = if self.is_exist_unique() {
            EXIST_UNIQUE
        } else {
            EXIST
        };
        write!(
            f,
            "{} {}",
            head,
            self.exist_fact_string_without_exist_as_prefix()
        )
    }
}
