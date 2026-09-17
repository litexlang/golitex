use std::collections::HashMap;

use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, FnEqualInFact, GreaterEqualFact, GreaterFact, InFact, IsCartFact,
    IsFiniteSetFact, IsNonemptySetFact, IsSetFact, IsTupleFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotEqualFact, NotFnEqualInFact, NotGreaterEqualFact, NotGreaterFact,
    NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact,
    NotIsTupleFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotSubsetFact,
    NotSupersetFact, SubsetFact, SupersetFact,
};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_atomic_fact_rec(
        &mut self,
        atomic: &AtomicFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<AtomicFact, InstError> {
    let fact_id = self.ids.allocate_fact_id();
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
        AtomicFact::FnEqualInFact(f) => Ok(AtomicFact::FnEqualInFact(FnEqualInFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotFnEqualInFact(f) => Ok(AtomicFact::NotFnEqualInFact(NotFnEqualInFact {
            fact_id,
            left: self.inst_obj_rec(&f.left, param_to_arg_map)?,
            right: self.inst_obj_rec(&f.right, param_to_arg_map)?,
            set: self.inst_obj_rec(&f.set, param_to_arg_map)?,
            line_file: f.line_file.clone(),
        })),
    }
}
}
