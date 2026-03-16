use std::collections::HashMap;
use crate::obj::Obj;
use crate::fact::Fact;
use crate::fact::ExistOrAndChainAtomicFact;
use crate::fact::AtomicFact;
use crate::fact::ExistFact;
use crate::fact::OrFact;
use crate::fact::matchable_fact_with_atomic_fact_inside::AndFact;
use crate::fact::matchable_fact_with_atomic_fact_inside::ChainFact;
use crate::fact::ForallFact;
use crate::fact::ForallFactWithIff;
use crate::fact::{
    NormalAtomicFact,
    EqualFact,
    LessFact,
    GreaterFact,
    LessEqualFact,
    GreaterEqualFact,
    IsSetFact,
    IsNonemptySetFact,
    IsFiniteSetFact,
    InFact,
    IsCartFact,
    IsTupleFact,
    SubsetFact,
    SupersetFact,
    NotNormalAtomicFact,
    NotEqualFact,
    NotLessFact,
    NotGreaterFact,
    NotLessEqualFact,
    NotGreaterEqualFact,
    NotIsSetFact,
    NotIsNonemptySetFact,
    NotIsFiniteSetFact,
    NotInFact,
    NotIsCartFact,
    NotIsTupleFact,
    NotSubsetFact,
    NotSupersetFact,
};

impl ExistOrAndChainAtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ExistOrAndChainAtomicFact {
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

impl AtomicFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> AtomicFact {
        match self {
            AtomicFact::NormalAtomicFact(fact) => {
                AtomicFact::NormalAtomicFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::EqualFact(fact) => {
                AtomicFact::EqualFact(fact.instantiate(param_to_arg_map))
            }
            AtomicFact::LessFact(fact) => {
                AtomicFact::LessFact(fact.instantiate(param_to_arg_map))
            }
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
            AtomicFact::InFact(fact) => {
                AtomicFact::InFact(fact.instantiate(param_to_arg_map))
            }
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
        }
    }
}

impl NormalAtomicFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NormalAtomicFact {
        unreachable!("NormalAtomicFact::instantiate not implemented yet")
    }
}

impl EqualFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> EqualFact {
        unreachable!("EqualFact::instantiate not implemented yet")
    }
}

impl LessFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> LessFact {
        unreachable!("LessFact::instantiate not implemented yet")
    }
}

impl GreaterFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> GreaterFact {
        unreachable!("GreaterFact::instantiate not implemented yet")
    }
}

impl LessEqualFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> LessEqualFact {
        unreachable!("LessEqualFact::instantiate not implemented yet")
    }
}

impl GreaterEqualFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> GreaterEqualFact {
        unreachable!("GreaterEqualFact::instantiate not implemented yet")
    }
}

impl IsSetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> IsSetFact {
        unreachable!("IsSetFact::instantiate not implemented yet")
    }
}

impl IsNonemptySetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> IsNonemptySetFact {
        unreachable!("IsNonemptySetFact::instantiate not implemented yet")
    }
}

impl IsFiniteSetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> IsFiniteSetFact {
        unreachable!("IsFiniteSetFact::instantiate not implemented yet")
    }
}

impl InFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> InFact {
        unreachable!("InFact::instantiate not implemented yet")
    }
}

impl IsCartFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> IsCartFact {
        unreachable!("IsCartFact::instantiate not implemented yet")
    }
}

impl IsTupleFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> IsTupleFact {
        unreachable!("IsTupleFact::instantiate not implemented yet")
    }
}

impl SubsetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> SubsetFact {
        unreachable!("SubsetFact::instantiate not implemented yet")
    }
}

impl SupersetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> SupersetFact {
        unreachable!("SupersetFact::instantiate not implemented yet")
    }
}

impl NotNormalAtomicFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotNormalAtomicFact {
        unreachable!("NotNormalAtomicFact::instantiate not implemented yet")
    }
}

impl NotEqualFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotEqualFact {
        unreachable!("NotEqualFact::instantiate not implemented yet")
    }
}

impl NotLessFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotLessFact {
        unreachable!("NotLessFact::instantiate not implemented yet")
    }
}

impl NotGreaterFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotGreaterFact {
        unreachable!("NotGreaterFact::instantiate not implemented yet")
    }
}

impl NotLessEqualFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotLessEqualFact {
        unreachable!("NotLessEqualFact::instantiate not implemented yet")
    }
}

impl NotGreaterEqualFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotGreaterEqualFact {
        unreachable!("NotGreaterEqualFact::instantiate not implemented yet")
    }
}

impl NotIsSetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotIsSetFact {
        unreachable!("NotIsSetFact::instantiate not implemented yet")
    }
}

impl NotIsNonemptySetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotIsNonemptySetFact {
        unreachable!("NotIsNonemptySetFact::instantiate not implemented yet")
    }
}

impl NotIsFiniteSetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotIsFiniteSetFact {
        unreachable!("NotIsFiniteSetFact::instantiate not implemented yet")
    }
}

impl NotInFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotInFact {
        unreachable!("NotInFact::instantiate not implemented yet")
    }
}

impl NotIsCartFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotIsCartFact {
        unreachable!("NotIsCartFact::instantiate not implemented yet")
    }
}

impl NotIsTupleFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotIsTupleFact {
        unreachable!("NotIsTupleFact::instantiate not implemented yet")
    }
}

impl NotSubsetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotSubsetFact {
        unreachable!("NotSubsetFact::instantiate not implemented yet")
    }
}

impl NotSupersetFact {
    pub fn instantiate(&self, _param_to_arg_map: &HashMap<String, Obj>) -> NotSupersetFact {
        unreachable!("NotSupersetFact::instantiate not implemented yet")
    }
}

impl ExistFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ExistFact {
        unreachable!("ExistFact::instantiate not implemented yet")
    }
}

impl OrFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> OrFact {
        unreachable!("OrFact::instantiate not implemented yet")
    }
}

impl AndFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> AndFact {
        unreachable!("AndFact::instantiate not implemented yet")
    }
}

impl ChainFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ChainFact {
        unreachable!("ChainFact::instantiate not implemented yet")
    }
}

impl ForallFact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ForallFact {
        unreachable!("ForallFact::instantiate not implemented yet")
    }
}

impl ForallFactWithIff {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> ForallFactWithIff {
        unreachable!("ForallFactWithIff::instantiate not implemented yet")
    }
}

impl Fact {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Fact {
        match self {
            Fact::AtomicFact(atomic_fact) => {
                Fact::AtomicFact(atomic_fact.instantiate(param_to_arg_map))
            }
            Fact::ExistFact(exist_fact) => {
                Fact::ExistFact(exist_fact.instantiate(param_to_arg_map))
            }
            Fact::OrFact(or_fact) => {
                Fact::OrFact(or_fact.instantiate(param_to_arg_map))
            }
            Fact::AndFact(and_fact) => {
                Fact::AndFact(and_fact.instantiate(param_to_arg_map))
            }
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
