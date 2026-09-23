//! Cross-form Fact queries and support routines.

use crate::prelude::*;

impl Fact {
    /// Identity allocated when this concrete fact node was created.
    pub fn fact_id(&self) -> FactId {
        match self {
            Fact::AtomicFact(fact) => fact.fact_id(),
            Fact::ExistFact(fact) => fact.fact_id(),
            Fact::OrFact(fact) => fact.fact_id,
            Fact::AndFact(fact) => fact.fact_id,
            Fact::ChainFact(fact) => fact.fact_id,
            Fact::ForallFact(fact) => fact.fact_id,
            Fact::ForallFactWithIff(fact) => fact.fact_id,
            Fact::NotForall(fact) => fact.fact_id,
        }
    }
}

impl AtomicFact {
    pub fn fact_id(&self) -> FactId {
        match self {
            AtomicFact::NormalAtomicFact(fact) => fact.fact_id,
            AtomicFact::EqualFact(fact) => fact.fact_id,
            AtomicFact::LessFact(fact) => fact.fact_id,
            AtomicFact::GreaterFact(fact) => fact.fact_id,
            AtomicFact::LessEqualFact(fact) => fact.fact_id,
            AtomicFact::GreaterEqualFact(fact) => fact.fact_id,
            AtomicFact::IsSetFact(fact) => fact.fact_id,
            AtomicFact::IsNonemptySetFact(fact) => fact.fact_id,
            AtomicFact::IsFiniteSetFact(fact) => fact.fact_id,
            AtomicFact::InFact(fact) => fact.fact_id,
            AtomicFact::IsCartFact(fact) => fact.fact_id,
            AtomicFact::IsTupleFact(fact) => fact.fact_id,
            AtomicFact::SubsetFact(fact) => fact.fact_id,
            AtomicFact::SupersetFact(fact) => fact.fact_id,
            AtomicFact::NotNormalAtomicFact(fact) => fact.fact_id,
            AtomicFact::NotEqualFact(fact) => fact.fact_id,
            AtomicFact::NotLessFact(fact) => fact.fact_id,
            AtomicFact::NotGreaterFact(fact) => fact.fact_id,
            AtomicFact::NotLessEqualFact(fact) => fact.fact_id,
            AtomicFact::NotGreaterEqualFact(fact) => fact.fact_id,
            AtomicFact::NotIsSetFact(fact) => fact.fact_id,
            AtomicFact::NotIsNonemptySetFact(fact) => fact.fact_id,
            AtomicFact::NotIsFiniteSetFact(fact) => fact.fact_id,
            AtomicFact::NotInFact(fact) => fact.fact_id,
            AtomicFact::NotIsCartFact(fact) => fact.fact_id,
            AtomicFact::NotIsTupleFact(fact) => fact.fact_id,
            AtomicFact::NotSubsetFact(fact) => fact.fact_id,
            AtomicFact::NotSupersetFact(fact) => fact.fact_id,
            AtomicFact::FnEqualFact(fact) => fact.fact_id,
        }
    }
}

impl ExistFact {
    pub fn fact_id(&self) -> FactId {
        self.spec().fact_id
    }
}

impl Fact {
    pub fn contains_native_complex_syntax(&self) -> bool {
        match self {
            Fact::AtomicFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            Fact::ExistFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            Fact::OrFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            Fact::AndFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            Fact::ChainFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            Fact::ForallFact(fact) => fact.contains_native_complex_syntax(),
            Fact::ForallFactWithIff(fact) => {
                fact.forall_fact.contains_native_complex_syntax()
                    || fact
                        .iff_facts
                        .iter()
                        .any(ExistOrAndChainAtomicFact::contains_native_complex_syntax)
            }
            Fact::NotForall(fact) => fact.forall_fact.contains_native_complex_syntax(),
        }
    }
}

impl ForallFact {
    fn contains_native_complex_syntax(&self) -> bool {
        self.typed_parameters.groups.iter().any(|group| {
            matches!(
                &group.param_type,
                ParamType::Obj(obj) if obj.contains_native_complex_syntax()
            )
        }) || self
            .dom_facts
            .iter()
            .any(Fact::contains_native_complex_syntax)
            || self
                .then_facts
                .iter()
                .any(ExistOrAndChainAtomicFact::contains_native_complex_syntax)
    }
}

impl ExistOrAndChainAtomicFact {
    fn contains_native_complex_syntax(&self) -> bool {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            ExistOrAndChainAtomicFact::AndFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            ExistOrAndChainAtomicFact::ChainFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            ExistOrAndChainAtomicFact::OrFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
            ExistOrAndChainAtomicFact::ExistFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_syntax),
        }
    }
}
