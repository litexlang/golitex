use super::QuantifierFreeFact;
use super::super::line_file::LineFile;
use super::super::param::TypedParameterList;
use crate::new_pipeline::runtime::FactId;

// Shared payload for `exist` / `exist!` / `not exist`.
//
// Body is only QuantifierFreeFact: atomic / and / chain / or.
//
// No nested exist: `exist x st { exist y st {P} }` flattens to `exist x, y st {P}`.
// No forall in the body either (same rule as and / or): keeping the body
// quantifier-free makes ExistFactIndexKey a fixed shape bucket, so known-exist
// and forall→exist search stay cheap. To state a nested universal, name it as a
// prop (or abstract_prop) and put that atomic in the body instead.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlainExistFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: Option<LineFile>,
}

// Exist-family tag for Env indexing and helpers that need all three kinds.
// Fact itself uses ExistFact / ExistUniqueFact / NotExistFact at the top level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistFactFamily {
    Exist(PlainExistFact),
    ExistUnique(PlainExistFact),
    NotExist(PlainExistFact),
}

impl ExistFactFamily {
    pub fn plain(&self) -> &PlainExistFact {
        match self {
            ExistFactFamily::Exist(p)
            | ExistFactFamily::ExistUnique(p)
            | ExistFactFamily::NotExist(p) => p,
        }
    }

    pub fn into_plain(self) -> PlainExistFact {
        match self {
            ExistFactFamily::Exist(p)
            | ExistFactFamily::ExistUnique(p)
            | ExistFactFamily::NotExist(p) => p,
        }
    }
}
