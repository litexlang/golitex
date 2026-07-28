use crate::prelude::*;

impl Fact {
    pub(crate) fn contains_native_complex_builtin(&self) -> bool {
        match self {
            Fact::AtomicFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            Fact::ExistFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            Fact::OrFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            Fact::AndFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            Fact::ChainFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            Fact::ForallFact(fact) => fact.contains_native_complex_builtin(),
            Fact::ForallFactWithIff(fact) => {
                fact.forall_fact.contains_native_complex_builtin()
                    || fact
                        .iff_facts
                        .iter()
                        .any(ExistOrAndChainAtomicFact::contains_native_complex_builtin)
            }
            Fact::NotForall(fact) => fact.forall_fact.contains_native_complex_builtin(),
        }
    }
}

impl ForallFact {
    fn contains_native_complex_builtin(&self) -> bool {
        self.params_def_with_type.groups.iter().any(|group| {
            matches!(
                &group.param_type,
                ParamType::Obj(obj) if obj.contains_native_complex_builtin()
            )
        }) || self
            .dom_facts
            .iter()
            .any(Fact::contains_native_complex_builtin)
            || self
                .then_facts
                .iter()
                .any(ExistOrAndChainAtomicFact::contains_native_complex_builtin)
    }
}

impl ExistOrAndChainAtomicFact {
    fn contains_native_complex_builtin(&self) -> bool {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            ExistOrAndChainAtomicFact::AndFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            ExistOrAndChainAtomicFact::ChainFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            ExistOrAndChainAtomicFact::OrFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
            ExistOrAndChainAtomicFact::ExistFact(fact) => fact
                .get_args_from_fact_ref()
                .into_iter()
                .any(Obj::contains_native_complex_builtin),
        }
    }
}
