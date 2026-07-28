use crate::prelude::*;

impl Fact {
    pub(crate) fn contains_native_complex_syntax(&self) -> bool {
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
        self.params_def_with_type.groups.iter().any(|group| {
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
