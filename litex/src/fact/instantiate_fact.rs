use crate::prelude::*;
use std::collections::HashMap;

impl Fact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Fact {
        match self {
            Fact::AtomicFact(atomic_fact) => {
                Fact::AtomicFact(atomic_fact.instantiate(param_to_arg_map))
            }
            Fact::ExistFact(exist_fact) => {
                Fact::ExistFact(exist_fact.instantiate(param_to_arg_map))
            }
            Fact::OrFact(or_fact) => Fact::OrFact(or_fact.instantiate(param_to_arg_map)),
            Fact::AndFact(and_fact) => Fact::AndFact(and_fact.instantiate(param_to_arg_map)),
            Fact::ChainFact(chain_fact) => {
                Fact::ChainFact(chain_fact.instantiate(param_to_arg_map))
            }
            Fact::ForallFact(forall_fact) => {
                Fact::ForallFact(forall_fact.instantiate(param_to_arg_map))
            }
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                Fact::ForallFactWithIff(forall_fact_with_iff.instantiate(param_to_arg_map))
            }
        }
    }
}

impl ExistOrAndChainAtomicFact {
    pub fn instantiate(
        &self,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> ExistOrAndChainAtomicFact {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.instantiate(param_to_arg_map))
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                ExistOrAndChainAtomicFact::AndFact(and_fact.instantiate(param_to_arg_map))
            }
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                ExistOrAndChainAtomicFact::ChainFact(chain_fact.instantiate(param_to_arg_map))
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                ExistOrAndChainAtomicFact::OrFact(or_fact.instantiate(param_to_arg_map))
            }
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                ExistOrAndChainAtomicFact::ExistFact(exist_fact.instantiate(param_to_arg_map))
            }
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> OrAndChainAtomicFact {
        match self {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                OrAndChainAtomicFact::AtomicFact(atomic_fact.instantiate(param_to_arg_map))
            }
            OrAndChainAtomicFact::AndFact(and_fact) => {
                OrAndChainAtomicFact::AndFact(and_fact.instantiate(param_to_arg_map))
            }
            OrAndChainAtomicFact::ChainFact(chain_fact) => {
                OrAndChainAtomicFact::ChainFact(chain_fact.instantiate(param_to_arg_map))
            }
            OrAndChainAtomicFact::OrFact(or_fact) => {
                OrAndChainAtomicFact::OrFact(or_fact.instantiate(param_to_arg_map))
            }
        }
    }
}

impl AndChainAtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> AndChainAtomicFact {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                AndChainAtomicFact::AtomicFact(atomic_fact.instantiate(param_to_arg_map))
            }
            AndChainAtomicFact::AndFact(and_fact) => {
                AndChainAtomicFact::AndFact(and_fact.instantiate(param_to_arg_map))
            }
            AndChainAtomicFact::ChainFact(chain_fact) => {
                AndChainAtomicFact::ChainFact(chain_fact.instantiate(param_to_arg_map))
            }
        }
    }
}

impl AtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> AtomicFact {
        match self {
            AtomicFact::NormalAtomicFact(fact) => {
                AtomicFact::NormalAtomicFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::EqualFact(fact) => {
                AtomicFact::EqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::LessFact(fact) => AtomicFact::LessFact(fact.instantiate(param_to_arg_map)),
            AtomicFact::GreaterFact(fact) => {
                AtomicFact::GreaterFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::LessEqualFact(fact) => {
                AtomicFact::LessEqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::GreaterEqualFact(fact) => {
                AtomicFact::GreaterEqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::IsSetFact(fact) => {
                AtomicFact::IsSetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::IsNonemptySetFact(fact) => {
                AtomicFact::IsNonemptySetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::IsFiniteSetFact(fact) => {
                AtomicFact::IsFiniteSetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::InFact(fact) => AtomicFact::InFact(fact.instantiate(param_to_arg_map)),
            AtomicFact::IsCartFact(fact) => {
                AtomicFact::IsCartFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::IsTupleFact(fact) => {
                AtomicFact::IsTupleFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::SubsetFact(fact) => {
                AtomicFact::SubsetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::SupersetFact(fact) => {
                AtomicFact::SupersetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotNormalAtomicFact(fact) => {
                AtomicFact::NotNormalAtomicFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotEqualFact(fact) => {
                AtomicFact::NotEqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotLessFact(fact) => {
                AtomicFact::NotLessFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotGreaterFact(fact) => {
                AtomicFact::NotGreaterFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotLessEqualFact(fact) => {
                AtomicFact::NotLessEqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotGreaterEqualFact(fact) => {
                AtomicFact::NotGreaterEqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotIsSetFact(fact) => {
                AtomicFact::NotIsSetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotIsNonemptySetFact(fact) => {
                AtomicFact::NotIsNonemptySetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotIsFiniteSetFact(fact) => {
                AtomicFact::NotIsFiniteSetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotInFact(fact) => {
                AtomicFact::NotInFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotIsCartFact(fact) => {
                AtomicFact::NotIsCartFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotIsTupleFact(fact) => {
                AtomicFact::NotIsTupleFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotSubsetFact(fact) => {
                AtomicFact::NotSubsetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotSupersetFact(fact) => {
                AtomicFact::NotSupersetFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::RestrictFact(fact) => {
                AtomicFact::RestrictFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::NotRestrictFact(fact) => {
                AtomicFact::NotRestrictFact(fact.instantiate(param_to_arg_map))
            }
        }
    }
}

impl NormalAtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NormalAtomicFact {
        let mut body = Vec::with_capacity(self.body.len());
        for obj in self.body.iter() {
            body.push(obj.instantiate(param_to_arg_map));
        }
        NormalAtomicFact {
            predicate: self.predicate.clone(),
            body,
            line_file: self.line_file,
        }
    }
}

impl EqualFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> EqualFact {
        EqualFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl LessFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> LessFact {
        LessFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl GreaterFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> GreaterFact {
        GreaterFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl LessEqualFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> LessEqualFact {
        LessEqualFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl GreaterEqualFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> GreaterEqualFact {
        GreaterEqualFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl IsSetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> IsSetFact {
        IsSetFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl IsNonemptySetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> IsNonemptySetFact {
        IsNonemptySetFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl IsFiniteSetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> IsFiniteSetFact {
        IsFiniteSetFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl InFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> InFact {
        InFact {
            element: self.element.instantiate(param_to_arg_map),
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl IsCartFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> IsCartFact {
        IsCartFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl IsTupleFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> IsTupleFact {
        IsTupleFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl SubsetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> SubsetFact {
        SubsetFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl SupersetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> SupersetFact {
        SupersetFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotNormalAtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotNormalAtomicFact {
        let mut body = Vec::with_capacity(self.body.len());
        for obj in self.body.iter() {
            body.push(obj.instantiate(param_to_arg_map));
        }
        NotNormalAtomicFact {
            predicate: self.predicate.clone(),
            body,
            line_file: self.line_file,
        }
    }
}

impl NotEqualFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotEqualFact {
        NotEqualFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotLessFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotLessFact {
        NotLessFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotGreaterFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotGreaterFact {
        NotGreaterFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotLessEqualFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotLessEqualFact {
        NotLessEqualFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotGreaterEqualFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotGreaterEqualFact {
        NotGreaterEqualFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotIsSetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotIsSetFact {
        NotIsSetFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotIsNonemptySetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotIsNonemptySetFact {
        NotIsNonemptySetFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotIsFiniteSetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotIsFiniteSetFact {
        NotIsFiniteSetFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotInFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotInFact {
        NotInFact {
            element: self.element.instantiate(param_to_arg_map),
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotIsCartFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotIsCartFact {
        NotIsCartFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotIsTupleFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotIsTupleFact {
        NotIsTupleFact {
            set: self.set.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotSubsetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotSubsetFact {
        NotSubsetFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotSupersetFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotSupersetFact {
        NotSupersetFact {
            left: self.left.instantiate(param_to_arg_map),
            right: self.right.instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl ExistFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ExistFact {
        let mut params_def_with_type = Vec::with_capacity(self.params_def_with_type.len());
        for param_def_with_type in self.params_def_with_type.iter() {
            params_def_with_type.push(ParamDefWithParamType(
                param_def_with_type.0.clone(),
                param_def_with_type.1.instantiate(param_to_arg_map),
            ));
        }
        let mut facts = Vec::with_capacity(self.facts.len());
        for fact in self.facts.iter() {
            facts.push(fact.instantiate(param_to_arg_map));
        }
        ExistFact {
            params_def_with_type,
            facts,
            line_file: self.line_file,
        }
    }
}

impl OrFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> OrFact {
        let mut facts = Vec::with_capacity(self.facts.len());
        for fact in self.facts.iter() {
            facts.push(fact.instantiate(param_to_arg_map));
        }
        OrFact {
            facts,
            line_file: self.line_file,
        }
    }
}

impl AndFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> AndFact {
        let mut facts = Vec::with_capacity(self.facts.len());
        for fact in self.facts.iter() {
            facts.push(fact.instantiate(param_to_arg_map));
        }
        AndFact {
            facts,
            line_file: self.line_file,
        }
    }
}

impl ChainFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ChainFact {
        let mut objs = Vec::with_capacity(self.objs.len());
        for obj in self.objs.iter() {
            objs.push(obj.instantiate(param_to_arg_map));
        }
        ChainFact {
            objs,
            prop_names: self.prop_names.clone(),
            line_file: self.line_file,
        }
    }
}

impl ForallFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ForallFact {
        let mut params_def_with_type = Vec::with_capacity(self.params_def_with_type.len());
        for param_def_with_type in self.params_def_with_type.iter() {
            params_def_with_type.push(ParamDefWithParamType(
                param_def_with_type.0.clone(),
                param_def_with_type.1.instantiate(param_to_arg_map),
            ));
        }
        let mut dom_facts = Vec::with_capacity(self.dom_facts.len());
        for dom_fact in self.dom_facts.iter() {
            dom_facts.push(dom_fact.instantiate(param_to_arg_map));
        }
        let mut then_facts = Vec::with_capacity(self.then_facts.len());
        for then_fact in self.then_facts.iter() {
            then_facts.push(then_fact.instantiate(param_to_arg_map));
        }
        ForallFact {
            params_def_with_type,
            dom_facts,
            then_facts,
            line_file: self.line_file,
        }
    }
}

impl ForallFactWithIff {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ForallFactWithIff {
        let forall_fact = self.forall_fact.instantiate(param_to_arg_map);
        let mut iff_facts = Vec::with_capacity(self.iff_facts.len());
        for iff_fact in self.iff_facts.iter() {
            iff_facts.push(iff_fact.instantiate(param_to_arg_map));
        }
        ForallFactWithIff {
            forall_fact,
            iff_facts,
            line_file: self.line_file,
        }
    }
}

impl RestrictFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> RestrictFact {
        RestrictFact {
            obj: self.obj.instantiate(param_to_arg_map),
            obj_can_restrict_to_fn_set: self
                .obj_can_restrict_to_fn_set
                .instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}

impl NotRestrictFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> NotRestrictFact {
        NotRestrictFact {
            obj: self.obj.instantiate(param_to_arg_map),
            obj_cannot_restrict_to_fn_set: self
                .obj_cannot_restrict_to_fn_set
                .instantiate(param_to_arg_map),
            line_file: self.line_file,
        }
    }
}
