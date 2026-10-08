use super::super::line_file::SourceLine;
use super::super::param::TypedParameterList;
use super::QuantifierFreeFact;
use crate::runtime::FactId;

// Shared payload for `exist` / `exist!` / `not exist`.
//
// Body is only QuantifierFreeFact: atomic / and / chain / or.
//
// No nested exist: `exist x st { exist y st {P} }` flattens to `exist x, y st {P}`.
// No forall in the body either (same rule as and / or): keeping the body
// quantifier-free makes ExistShapedFactIndexKey a fixed shape bucket, so known-exist
// and forall→exist search stay cheap. To state a nested universal, name it as a
// prop (or abstract_prop) and put that atomic in the body instead.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlainExistFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: Option<SourceLine>,
}

// Three-way exist shape tag for Env indexing and helpers that need exist / exist! / not exist.
// Fact itself uses ExistFact / ExistUniqueFact / NotExistFact at the top level;
// only `Exist` (and Fact::ExistFact) is a true exist fact. PlainExistFact is the shared payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistShapedFact {
    Exist(PlainExistFact),
    ExistUnique(PlainExistFact),
    NotExist(PlainExistFact),
}

impl ExistShapedFact {
    pub fn plain(&self) -> &PlainExistFact {
        match self {
            ExistShapedFact::Exist(p)
            | ExistShapedFact::ExistUnique(p)
            | ExistShapedFact::NotExist(p) => p,
        }
    }

    pub fn into_plain(self) -> PlainExistFact {
        match self {
            ExistShapedFact::Exist(p)
            | ExistShapedFact::ExistUnique(p)
            | ExistShapedFact::NotExist(p) => p,
        }
    }
}
