use super::*;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferAtomicFactResult {
    HasSequenceLimitFact(Vec<InferHasSequenceLimitFactResult>),
    NotHasSequenceLimitFact(Vec<InferNotHasSequenceLimitFactResult>),
    NormalAtomicFact(Vec<InferNormalAtomicFactResult>),
    EqualFact(Vec<InferEqualFactResult>),
    LessFact(Vec<InferLessFactResult>),
    GreaterFact(Vec<InferGreaterFactResult>),
    LessEqualFact(Vec<InferLessEqualFactResult>),
    GreaterEqualFact(Vec<InferGreaterEqualFactResult>),
    IsSetFact(Vec<InferIsSetFactResult>),
    IsNonemptySetFact(Vec<InferIsNonemptySetFactResult>),
    IsFiniteSetFact(Vec<InferIsFiniteSetFactResult>),
    InFact(Vec<InferInFactResult>),
    SubsetFact(Vec<InferSubsetFactResult>),
    SupersetFact(Vec<InferSupersetFactResult>),
    ProperSubsetFact(Vec<InferProperSubsetFactResult>),
    ProperSupersetFact(Vec<InferProperSupersetFactResult>),
    PrimeFact(Vec<InferPrimeFactResult>),
    CoprimeFact(Vec<InferCoprimeFactResult>),
    DvdFact(Vec<InferDvdFactResult>),
    InjectiveFact(Vec<InferInjectiveFactResult>),
    SurjectiveFact(Vec<InferSurjectiveFactResult>),
    BijectiveFact(Vec<InferBijectiveFactResult>),
    IsChoiceFunctionForFact(Vec<InferIsChoiceFunctionForFactResult>),
    NotNormalAtomicFact(Vec<InferNotNormalAtomicFactResult>),
    NotEqualFact(Vec<InferNotEqualFactResult>),
    NotLessFact(Vec<InferNotLessFactResult>),
    NotGreaterFact(Vec<InferNotGreaterFactResult>),
    NotLessEqualFact(Vec<InferNotLessEqualFactResult>),
    NotGreaterEqualFact(Vec<InferNotGreaterEqualFactResult>),
    NotIsSetFact(Vec<InferNotIsSetFactResult>),
    NotIsNonemptySetFact(Vec<InferNotIsNonemptySetFactResult>),
    NotIsFiniteSetFact(Vec<InferNotIsFiniteSetFactResult>),
    NotInFact(Vec<InferNotInFactResult>),
    NotSubsetFact(Vec<InferNotSubsetFactResult>),
    NotSupersetFact(Vec<InferNotSupersetFactResult>),
    NotProperSubsetFact(Vec<InferNotProperSubsetFactResult>),
    NotProperSupersetFact(Vec<InferNotProperSupersetFactResult>),
    NotPrimeFact(Vec<InferNotPrimeFactResult>),
    NotCoprimeFact(Vec<InferNotCoprimeFactResult>),
    NotDvdFact(Vec<InferNotDvdFactResult>),
    NotInjectiveFact(Vec<InferNotInjectiveFactResult>),
    NotSurjectiveFact(Vec<InferNotSurjectiveFactResult>),
    NotBijectiveFact(Vec<InferNotBijectiveFactResult>),
    NotIsChoiceFunctionForFact(Vec<InferNotIsChoiceFunctionForFactResult>),
}

impl InferAtomicFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::NormalAtomicFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::EqualFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::LessFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::GreaterFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::LessEqualFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::GreaterEqualFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::IsSetFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::IsNonemptySetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::IsFiniteSetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::InFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::SubsetFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::SupersetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::ProperSubsetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::ProperSupersetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::PrimeFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::CoprimeFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::HasSequenceLimitFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotHasSequenceLimitFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::DvdFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::InjectiveFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::SurjectiveFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::BijectiveFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::IsChoiceFunctionForFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotNormalAtomicFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotEqualFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotLessFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::NotGreaterFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotLessEqualFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotGreaterEqualFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotIsSetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotIsNonemptySetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotIsFiniteSetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotInFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::NotSubsetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotSupersetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotProperSubsetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotProperSupersetFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotPrimeFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotCoprimeFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotDvdFact(rules) => rules.iter().flat_map(|r| r.stored_conclusions()).collect(),
            Self::NotInjectiveFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotSurjectiveFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotBijectiveFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
            Self::NotIsChoiceFunctionForFact(rules) => {
                rules.iter().flat_map(|r| r.stored_conclusions()).collect()
            }
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}

pub enum InferHasSequenceLimitFactResult {}
impl InferHasSequenceLimitFactResult {
    pub fn stored_conclusions(&self) -> Vec<&crate::store_fact_and_infer::StoreInferredFactResult> {
        match *self {}
    }
}
pub enum InferNotHasSequenceLimitFactResult {}
impl InferNotHasSequenceLimitFactResult {
    pub fn stored_conclusions(&self) -> Vec<&crate::store_fact_and_infer::StoreInferredFactResult> {
        match *self {}
    }
}
