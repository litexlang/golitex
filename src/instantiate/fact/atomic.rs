use std::collections::HashMap;

use crate::runtime::runtime_ids::IdentifierId;

use crate::ast::fact::{
    AtomicFact, BijectiveFact, CoprimeFact, DvdFact, EqualFact, GreaterEqualFact, GreaterFact,
    InFact, InjectiveFact, IsCartFact, IsChoiceFunctionForFact, IsFiniteSetFact, IsNonemptySetFact,
    IsSetFact, IsTupleFact, LessEqualFact, LessFact, NormalAtomicFact, NotBijectiveFact,
    NotCoprimeFact, NotDvdFact, NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact,
    NotInjectiveFact, NotIsCartFact, NotIsChoiceFunctionForFact, NotIsFiniteSetFact,
    NotIsNonemptySetFact, NotIsSetFact, NotIsTupleFact, NotLessEqualFact, NotLessFact,
    NotNormalAtomicFact, NotPrimeFact, NotProperSubsetFact, NotProperSupersetFact, NotSubsetFact,
    NotSupersetFact, NotSurjectiveFact, PrimeFact, ProperSubsetFact, ProperSupersetFact,
    SubsetFact, SupersetFact, SurjectiveFact,
};
use crate::ast::obj::Obj;
use crate::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_atomic_fact_rec(
        &mut self,
        atomic: &AtomicFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<AtomicFact, InstError> {
    let fact_id = self.global_ids.allocate_fact_id();
    match atomic {
        AtomicFact::NormalAtomicFact(f) => {
            let mut body = Vec::with_capacity(f.body.len());
            for o in &f.body {
                body.push(self.inst_obj_rec(o, param_to_arg_map)?);
            }
            Ok(AtomicFact::NormalAtomicFact(NormalAtomicFact {
                fact_id,
                predicate: f.predicate.clone(),
                body,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NotNormalAtomicFact(f) => {
            let mut body = Vec::with_capacity(f.body.len());
            for o in &f.body {
                body.push(self.inst_obj_rec(o, param_to_arg_map)?);
            }
            Ok(AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact {
                fact_id,
                predicate: f.predicate.clone(),
                body,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::EqualFact(f) => Ok(AtomicFact::EqualFact(EqualFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotEqualFact(f) => Ok(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessFact(f) => Ok(AtomicFact::LessFact(LessFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessFact(f) => Ok(AtomicFact::NotLessFact(NotLessFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterFact(f) => Ok(AtomicFact::GreaterFact(GreaterFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterFact(f) => Ok(AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessEqualFact(f) => Ok(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessEqualFact(f) => Ok(AtomicFact::NotLessEqualFact(NotLessEqualFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterEqualFact(f) => Ok(AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterEqualFact(f) => Ok(AtomicFact::NotGreaterEqualFact(
            NotGreaterEqualFact {
                fact_id,
                left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
                right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::IsSetFact(f) => Ok(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsSetFact(f) => Ok(AtomicFact::NotIsSetFact(NotIsSetFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsNonemptySetFact(f) => Ok(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsNonemptySetFact(f) => Ok(AtomicFact::NotIsNonemptySetFact(
            NotIsNonemptySetFact {
                fact_id,
                set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::IsFiniteSetFact(f) => Ok(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsFiniteSetFact(f) => Ok(AtomicFact::NotIsFiniteSetFact(
            NotIsFiniteSetFact {
                fact_id,
                set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::InFact(f) => Ok(AtomicFact::InFact(InFact {
            fact_id,
            element: self.inst_obj_rec(&f.element, param_to_arg_map)?,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotInFact(f) => Ok(AtomicFact::NotInFact(NotInFact {
            fact_id,
            element: self.inst_obj_rec(&f.element, param_to_arg_map)?,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsCartFact(f) => Ok(AtomicFact::IsCartFact(IsCartFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsCartFact(f) => Ok(AtomicFact::NotIsCartFact(NotIsCartFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsTupleFact(f) => Ok(AtomicFact::IsTupleFact(IsTupleFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsTupleFact(f) => Ok(AtomicFact::NotIsTupleFact(NotIsTupleFact {
            fact_id,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SubsetFact(f) => Ok(AtomicFact::SubsetFact(SubsetFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSubsetFact(f) => Ok(AtomicFact::NotSubsetFact(NotSubsetFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SupersetFact(f) => Ok(AtomicFact::SupersetFact(SupersetFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSupersetFact(f) => Ok(AtomicFact::NotSupersetFact(NotSupersetFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::ProperSubsetFact(f) => Ok(AtomicFact::ProperSubsetFact(ProperSubsetFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotProperSubsetFact(f) => Ok(AtomicFact::NotProperSubsetFact(
            NotProperSubsetFact {
                fact_id,
                left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
                right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::ProperSupersetFact(f) => Ok(AtomicFact::ProperSupersetFact(
            ProperSupersetFact {
                fact_id,
                left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
                right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::NotProperSupersetFact(f) => Ok(AtomicFact::NotProperSupersetFact(
            NotProperSupersetFact {
                fact_id,
                left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
                right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::PrimeFact(f) => Ok(AtomicFact::PrimeFact(PrimeFact {
            fact_id,
            value: self.inst_obj_rec(&f.value, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotPrimeFact(f) => Ok(AtomicFact::NotPrimeFact(NotPrimeFact {
            fact_id,
            value: self.inst_obj_rec(&f.value, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::CoprimeFact(f) => Ok(AtomicFact::CoprimeFact(CoprimeFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotCoprimeFact(f) => Ok(AtomicFact::NotCoprimeFact(NotCoprimeFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::DvdFact(f) => Ok(AtomicFact::DvdFact(DvdFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotDvdFact(f) => Ok(AtomicFact::NotDvdFact(NotDvdFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::InjectiveFact(f) => Ok(AtomicFact::InjectiveFact(InjectiveFact {
            fact_id,
            domain: self.inst_obj_rec(&f.domain, param_to_arg_map)?,
            codomain: self.inst_obj_rec(&f.codomain, param_to_arg_map)?,
            function: self.inst_obj_rec(&f.function, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotInjectiveFact(f) => Ok(AtomicFact::NotInjectiveFact(NotInjectiveFact {
            fact_id,
            domain: self.inst_obj_rec(&f.domain, param_to_arg_map)?,
            codomain: self.inst_obj_rec(&f.codomain, param_to_arg_map)?,
            function: self.inst_obj_rec(&f.function, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SurjectiveFact(f) => Ok(AtomicFact::SurjectiveFact(SurjectiveFact {
            fact_id,
            domain: self.inst_obj_rec(&f.domain, param_to_arg_map)?,
            codomain: self.inst_obj_rec(&f.codomain, param_to_arg_map)?,
            function: self.inst_obj_rec(&f.function, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSurjectiveFact(f) => Ok(AtomicFact::NotSurjectiveFact(NotSurjectiveFact {
            fact_id,
            domain: self.inst_obj_rec(&f.domain, param_to_arg_map)?,
            codomain: self.inst_obj_rec(&f.codomain, param_to_arg_map)?,
            function: self.inst_obj_rec(&f.function, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::BijectiveFact(f) => Ok(AtomicFact::BijectiveFact(BijectiveFact {
            fact_id,
            domain: self.inst_obj_rec(&f.domain, param_to_arg_map)?,
            codomain: self.inst_obj_rec(&f.codomain, param_to_arg_map)?,
            function: self.inst_obj_rec(&f.function, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotBijectiveFact(f) => Ok(AtomicFact::NotBijectiveFact(NotBijectiveFact {
            fact_id,
            domain: self.inst_obj_rec(&f.domain, param_to_arg_map)?,
            codomain: self.inst_obj_rec(&f.codomain, param_to_arg_map)?,
            function: self.inst_obj_rec(&f.function, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsChoiceFunctionForFact(f) => Ok(AtomicFact::IsChoiceFunctionForFact(
            IsChoiceFunctionForFact {
                fact_id,
                index: self.inst_obj_rec(&f.index, param_to_arg_map)?,
                set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
                family: self.inst_obj_rec(&f.family, param_to_arg_map)?,
                choice: self.inst_obj_rec(&f.choice, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::NotIsChoiceFunctionForFact(f) => Ok(AtomicFact::NotIsChoiceFunctionForFact(
            NotIsChoiceFunctionForFact {
                fact_id,
                index: self.inst_obj_rec(&f.index, param_to_arg_map)?,
                set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
                family: self.inst_obj_rec(&f.family, param_to_arg_map)?,
                choice: self.inst_obj_rec(&f.choice, param_to_arg_map)?,
                line_file: f.line_file.clone(),
            },
        )),
    }
}
}
