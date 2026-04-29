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
    pub facts: Vec<ExistBodyFact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub enum ExistBodyFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    InlineForall(ForallFact),
}

impl ExistFactBody {
    pub fn new(
        params_def_with_type: ParamDefWithType,
        facts: Vec<ExistBodyFact>,
        line_file: LineFile,
    ) -> Result<Self, RuntimeError> {
        let body = ExistFactBody {
            params_def_with_type,
            facts,
            line_file,
        };
        check_exist_fact_has_no_duplicate_exist_free_parameter(&ExistFactEnum::ExistFact(
            body.clone(),
        ))?;
        Ok(body)
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

impl ExistBodyFact {
    pub fn key(&self) -> String {
        match self {
            ExistBodyFact::AtomicFact(a) => a.key(),
            ExistBodyFact::AndFact(a) => a.key(),
            ExistBodyFact::ChainFact(c) => c.key(),
            ExistBodyFact::OrFact(o) => o.key(),
            ExistBodyFact::InlineForall(f) => inline_forall_fact_string(f),
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            ExistBodyFact::AtomicFact(a) => a.line_file(),
            ExistBodyFact::AndFact(a) => a.line_file(),
            ExistBodyFact::ChainFact(c) => c.line_file(),
            ExistBodyFact::OrFact(o) => o.line_file.clone(),
            ExistBodyFact::InlineForall(f) => f.line_file.clone(),
        }
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        match self {
            ExistBodyFact::AtomicFact(a) => a.get_args_from_fact(),
            ExistBodyFact::AndFact(a) => a.get_args_from_fact(),
            ExistBodyFact::ChainFact(c) => c.get_args_from_fact(),
            ExistBodyFact::OrFact(o) => o.get_args_from_fact(),
            ExistBodyFact::InlineForall(f) => forall_fact_args(f),
        }
    }

    pub fn to_fact(self) -> Fact {
        match self {
            ExistBodyFact::AtomicFact(a) => a.into(),
            ExistBodyFact::AndFact(a) => a.into(),
            ExistBodyFact::ChainFact(c) => c.into(),
            ExistBodyFact::OrFact(o) => o.into(),
            ExistBodyFact::InlineForall(f) => f.into(),
        }
    }

    pub fn from_ref_to_cloned_fact(&self) -> Fact {
        self.clone().to_fact()
    }

    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        match self {
            ExistBodyFact::AtomicFact(a) => {
                ExistBodyFact::AtomicFact(a.replace_bound_identifier(from, to))
            }
            ExistBodyFact::AndFact(a) => ExistBodyFact::AndFact(AndFact::new(
                a.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                a.line_file,
            )),
            ExistBodyFact::ChainFact(c) => ExistBodyFact::ChainFact(ChainFact::new(
                c.objs
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
                c.prop_names,
                c.line_file,
            )),
            ExistBodyFact::OrFact(o) => ExistBodyFact::OrFact(OrFact::new(
                o.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                o.line_file,
            )),
            ExistBodyFact::InlineForall(f) => {
                ExistBodyFact::InlineForall(replace_in_inline_forall_for_exist_alpha(f, from, to))
            }
        }
    }
}

impl fmt::Display for ExistBodyFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistBodyFact::AtomicFact(a) => write!(f, "{}", a),
            ExistBodyFact::AndFact(a) => write!(f, "{}", a),
            ExistBodyFact::ChainFact(c) => write!(f, "{}", c),
            ExistBodyFact::OrFact(o) => write!(f, "{}", o),
            ExistBodyFact::InlineForall(forall_fact) => {
                write!(f, "{}", inline_forall_fact_string(forall_fact))
            }
        }
    }
}

impl From<OrAndChainAtomicFact> for ExistBodyFact {
    fn from(fact: OrAndChainAtomicFact) -> Self {
        match fact {
            OrAndChainAtomicFact::AtomicFact(a) => ExistBodyFact::AtomicFact(a),
            OrAndChainAtomicFact::AndFact(a) => ExistBodyFact::AndFact(a),
            OrAndChainAtomicFact::ChainFact(c) => ExistBodyFact::ChainFact(c),
            OrAndChainAtomicFact::OrFact(o) => ExistBodyFact::OrFact(o),
        }
    }
}

impl From<AtomicFact> for ExistBodyFact {
    fn from(atomic_fact: AtomicFact) -> Self {
        ExistBodyFact::AtomicFact(atomic_fact)
    }
}

impl From<EqualFact> for ExistBodyFact {
    fn from(equal_fact: EqualFact) -> Self {
        ExistBodyFact::AtomicFact(equal_fact.into())
    }
}

fn forall_fact_args(forall_fact: &ForallFact) -> Vec<Obj> {
    let mut args: Vec<Obj> = Vec::new();
    for param_def_with_type in forall_fact.params_def_with_type.groups.iter() {
        if let ParamType::Obj(obj) = &param_def_with_type.param_type {
            args.push(obj.clone());
        }
    }
    for fact in forall_fact.dom_facts.iter() {
        match fact {
            Fact::AtomicFact(a) => args.extend(a.get_args_from_fact()),
            Fact::ExistFact(e) => args.extend(e.get_args_from_fact()),
            Fact::OrFact(o) => args.extend(o.get_args_from_fact()),
            Fact::AndFact(a) => args.extend(a.get_args_from_fact()),
            Fact::ChainFact(c) => args.extend(c.get_args_from_fact()),
            Fact::ForallFact(f) => args.extend(forall_fact_args(f)),
            Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {}
        }
    }
    for fact in forall_fact.then_facts.iter() {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => args.extend(a.get_args_from_fact()),
            ExistOrAndChainAtomicFact::AndFact(a) => args.extend(a.get_args_from_fact()),
            ExistOrAndChainAtomicFact::ChainFact(c) => args.extend(c.get_args_from_fact()),
            ExistOrAndChainAtomicFact::OrFact(o) => args.extend(o.get_args_from_fact()),
            ExistOrAndChainAtomicFact::ExistFact(e) => args.extend(e.get_args_from_fact()),
        }
    }
    args
}

fn inline_forall_fact_string(forall_fact: &ForallFact) -> String {
    let then_facts = curly_braced_vec_to_string_with_sep(
        &forall_fact
            .then_facts
            .iter()
            .map(|fact| fact.to_string())
            .collect::<Vec<String>>(),
        format!("{} ", COMMA),
    );
    if forall_fact.dom_facts.is_empty() {
        return format!(
            "{} {}{} {}",
            FORALL_BANG, forall_fact.params_def_with_type, COLON, then_facts
        );
    }
    format!(
        "{} {}{} {} {} {}",
        FORALL_BANG,
        forall_fact.params_def_with_type,
        COLON,
        vec_to_string_join_by_comma(
            &forall_fact
                .dom_facts
                .iter()
                .map(inline_fact_string)
                .collect::<Vec<String>>()
        ),
        RIGHT_ARROW,
        then_facts
    )
}

fn inline_fact_string(fact: &Fact) -> String {
    match fact {
        Fact::ForallFact(forall_fact) => inline_forall_fact_string(forall_fact),
        Fact::NotForall(not_forall) => {
            format!("{} {}", NOT, inline_forall_fact_string(&not_forall.forall_fact))
        }
        _ => fact.to_string(),
    }
}

fn replace_in_inline_forall_for_exist_alpha(
    forall_fact: ForallFact,
    from: &str,
    to: &str,
) -> ForallFact {
    let binds_same_name = forall_fact
        .params_def_with_type
        .collect_param_names()
        .iter()
        .any(|name| name == from);
    if binds_same_name {
        return forall_fact;
    }

    let dom_facts = forall_fact
        .dom_facts
        .into_iter()
        .map(|fact| replace_in_fact_for_exist_alpha(fact, from, to))
        .collect();
    let then_facts = forall_fact
        .then_facts
        .into_iter()
        .map(|fact| replace_in_exist_or_and_chain_for_exist_alpha(fact, from, to))
        .collect();

    ForallFact::new(
        forall_fact.params_def_with_type,
        dom_facts,
        then_facts,
        forall_fact.line_file,
    )
    .expect("alpha replacement preserves inline forall validity")
}

fn replace_in_fact_for_exist_alpha(fact: Fact, from: &str, to: &str) -> Fact {
    match fact {
        Fact::AtomicFact(a) => a.replace_bound_identifier(from, to).into(),
        Fact::ExistFact(e) => e.into(),
        Fact::OrFact(o) => OrFact::new(
            o.facts
                .into_iter()
                .map(|x| x.replace_bound_identifier(from, to))
                .collect(),
            o.line_file,
        )
        .into(),
        Fact::AndFact(a) => AndFact::new(
            a.facts
                .into_iter()
                .map(|x| x.replace_bound_identifier(from, to))
                .collect(),
            a.line_file,
        )
        .into(),
        Fact::ChainFact(c) => ChainFact::new(
            c.objs
                .into_iter()
                .map(|o| Obj::replace_bound_identifier(o, from, to))
                .collect(),
            c.prop_names,
            c.line_file,
        )
        .into(),
        Fact::ForallFact(f) => replace_in_inline_forall_for_exist_alpha(f, from, to).into(),
        Fact::ForallFactWithIff(f) => f.into(),
        Fact::NotForall(f) => f.into(),
    }
}

fn replace_in_exist_or_and_chain_for_exist_alpha(
    fact: ExistOrAndChainAtomicFact,
    from: &str,
    to: &str,
) -> ExistOrAndChainAtomicFact {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(a) => a.replace_bound_identifier(from, to).into(),
        ExistOrAndChainAtomicFact::AndFact(a) => AndFact::new(
            a.facts
                .into_iter()
                .map(|x| x.replace_bound_identifier(from, to))
                .collect(),
            a.line_file,
        )
        .into(),
        ExistOrAndChainAtomicFact::ChainFact(c) => ChainFact::new(
            c.objs
                .into_iter()
                .map(|o| Obj::replace_bound_identifier(o, from, to))
                .collect(),
            c.prop_names,
            c.line_file,
        )
        .into(),
        ExistOrAndChainAtomicFact::OrFact(o) => OrFact::new(
            o.facts
                .into_iter()
                .map(|x| x.replace_bound_identifier(from, to))
                .collect(),
            o.line_file,
        )
        .into(),
        ExistOrAndChainAtomicFact::ExistFact(e) => e.into(),
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
        let mut normalized_facts: Vec<ExistBodyFact> = b.facts.clone();
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

    pub fn facts(&self) -> &Vec<ExistBodyFact> {
        &self.body().facts
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        self.body().get_args_from_fact()
    }
}

fn exist_fact_string_without_exist_as_prefix(
    param_defs: &ParamDefWithType,
    facts: &Vec<ExistBodyFact>,
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
