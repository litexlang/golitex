use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum OrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}

impl From<OrAndChainAtomicFact> for ExistOrAndChainAtomicFact {
    fn from(f: OrAndChainAtomicFact) -> Self {
        match f {
            OrAndChainAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            OrAndChainAtomicFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            OrAndChainAtomicFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            OrAndChainAtomicFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => {
                OrAndChainAtomicFact::AtomicFact(a.replace_bound_identifier(from, to))
            }
            OrAndChainAtomicFact::AndFact(af) => OrAndChainAtomicFact::AndFact(AndFact::new(
                af.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                af.line_file,
            )),
            OrAndChainAtomicFact::ChainFact(cf) => OrAndChainAtomicFact::ChainFact(ChainFact::new(
                cf.objs
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
                cf.prop_names,
                cf.line_file,
            )),
            OrAndChainAtomicFact::OrFact(of) => OrAndChainAtomicFact::OrFact(OrFact::new(
                of.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                of.line_file,
            )),
        }
    }
}

impl From<AtomicFact> for OrAndChainAtomicFact {
    fn from(atomic_fact: AtomicFact) -> Self {
        OrAndChainAtomicFact::AtomicFact(atomic_fact)
    }
}

impl From<GreaterEqualFact> for OrAndChainAtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<LessFact> for OrAndChainAtomicFact {
    fn from(f: LessFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<EqualFact> for OrAndChainAtomicFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

// `exist` and `exist_unique` share this AST: same parameters and braced facts; `is_exist_unique` selects the keyword.
// For `exist_unique`, verification must also discharge the companion uniqueness `forall`; storing the existential
// also stores that generated `forall` (see environment / verify paths).
#[derive(Clone)]
pub struct ExistFact {
    pub params_def_with_type: ParamDefWithType,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub is_exist_unique: bool,
    pub line_file: LineFile,
}

impl ExistFact {
    pub fn new(
        params_def_with_type: ParamDefWithType,
        facts: Vec<OrAndChainAtomicFact>,
        is_exist_unique: bool,
        line_file: LineFile,
    ) -> Self {
        ExistFact {
            params_def_with_type,
            facts,
            is_exist_unique,
            line_file,
        }
    }

    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
    }

    pub fn key(&self) -> String {
        let head = if self.is_exist_unique {
            EXIST_UNIQUE
        } else {
            EXIST
        };
        format!(
            "{} {}{}{}",
            head,
            LEFT_CURLY_BRACE,
            vec_to_string_join_by_comma(
                &self
                    .facts
                    .iter()
                    .map(|fact| fact.key())
                    .collect::<Vec<String>>()
            ),
            RIGHT_CURLY_BRACE
        )
    }

    pub fn line_file(&self) -> LineFile {
        self.line_file.clone()
    }

    pub fn params_def_with_type(&self) -> &ParamDefWithType {
        &self.params_def_with_type
    }

    pub fn facts(&self) -> &Vec<OrAndChainAtomicFact> {
        &self.facts
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

impl fmt::Display for ExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = if self.is_exist_unique {
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

// ---------- Display & key for FactInsideExistFact ----------
impl fmt::Display for OrAndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            OrAndChainAtomicFact::AndFact(a) => write!(f, "{}", a),
            OrAndChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
            OrAndChainAtomicFact::OrFact(o) => write!(f, "{}", o),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn key(&self) -> String {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.key(),
            OrAndChainAtomicFact::AndFact(a) => a.key(),
            OrAndChainAtomicFact::ChainFact(c) => c.key(),
            OrAndChainAtomicFact::OrFact(o) => o.key(),
        }
    }
    pub fn line_file(&self) -> LineFile {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.line_file(),
            OrAndChainAtomicFact::AndFact(a) => a.line_file(),
            OrAndChainAtomicFact::ChainFact(c) => c.line_file(),
            OrAndChainAtomicFact::OrFact(o) => o.line_file.clone(),
        }
    }

    pub fn with_new_line_file(self, line_file: LineFile) -> Self {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => {
                OrAndChainAtomicFact::AtomicFact(a.with_new_line_file(line_file))
            }
            OrAndChainAtomicFact::AndFact(af) => OrAndChainAtomicFact::AndFact(AndFact::new(
                af.facts
                    .into_iter()
                    .map(|x| x.with_new_line_file(line_file.clone()))
                    .collect(),
                line_file,
            )),
            OrAndChainAtomicFact::ChainFact(cf) => {
                OrAndChainAtomicFact::ChainFact(ChainFact::new(cf.objs, cf.prop_names, line_file))
            }
            OrAndChainAtomicFact::OrFact(of) => OrAndChainAtomicFact::OrFact(OrFact::new(
                of.facts
                    .into_iter()
                    .map(|x| x.with_new_line_file(line_file.clone()))
                    .collect(),
                line_file,
            )),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn from_ref_to_cloned_fact(&self) -> Fact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.clone().into(),
            OrAndChainAtomicFact::AndFact(a) => a.clone().into(),
            OrAndChainAtomicFact::ChainFact(c) => c.clone().into(),
            OrAndChainAtomicFact::OrFact(o) => o.clone().into(),
        }
    }

    pub fn to_fact(self) -> Fact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => Fact::AtomicFact(a),
            OrAndChainAtomicFact::AndFact(a) => Fact::AndFact(a),
            OrAndChainAtomicFact::ChainFact(c) => Fact::ChainFact(c),
            OrAndChainAtomicFact::OrFact(o) => Fact::OrFact(o),
        }
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.get_args_from_fact(),
            OrAndChainAtomicFact::AndFact(a) => a.get_args_from_fact(),
            OrAndChainAtomicFact::ChainFact(c) => c.get_args_from_fact(),
            OrAndChainAtomicFact::OrFact(o) => o.get_args_from_fact(),
        }
    }
}

impl ExistFact {
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
