use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, FnEqualFact, FnEqualInFact, GreaterEqualFact, GreaterFact, InFact,
    IsCartFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact, IsTupleFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact, NotIsCartFact,
    NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact, NotIsTupleFact, NotLessEqualFact,
    NotLessFact, NotNormalAtomicFact, NotSubsetFact, NotSupersetFact, SubsetFact, SupersetFact,
};

use super::super::InstCtx;
use super::super::error::InstError;

pub fn inst_atomic_fact(ctx: &mut InstCtx<'_>, atomic: &AtomicFact) -> Result<AtomicFact, InstError> {
    let fact_id = ctx.rt.ids.allocate_fact_id();
    match atomic {
        AtomicFact::NormalAtomicFact(f) => {
            let mut body = Vec::with_capacity(f.body.len());
            for o in &f.body {
                body.push(ctx.inst_obj(o)?);
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
                body.push(ctx.inst_obj(o)?);
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
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotEqualFact(f) => Ok(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessFact(f) => Ok(AtomicFact::LessFact(LessFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessFact(f) => Ok(AtomicFact::NotLessFact(NotLessFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterFact(f) => Ok(AtomicFact::GreaterFact(GreaterFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterFact(f) => Ok(AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessEqualFact(f) => Ok(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessEqualFact(f) => Ok(AtomicFact::NotLessEqualFact(NotLessEqualFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterEqualFact(f) => Ok(AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterEqualFact(f) => Ok(AtomicFact::NotGreaterEqualFact(
            NotGreaterEqualFact {
                fact_id,
                left: ctx.inst_obj(&f.left)?,
                right: ctx.inst_obj(&f.right)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::IsSetFact(f) => Ok(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsSetFact(f) => Ok(AtomicFact::NotIsSetFact(NotIsSetFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsNonemptySetFact(f) => Ok(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsNonemptySetFact(f) => Ok(AtomicFact::NotIsNonemptySetFact(
            NotIsNonemptySetFact {
                fact_id,
                set: ctx.inst_obj(&f.set)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::IsFiniteSetFact(f) => Ok(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsFiniteSetFact(f) => Ok(AtomicFact::NotIsFiniteSetFact(
            NotIsFiniteSetFact {
                fact_id,
                set: ctx.inst_obj(&f.set)?,
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::InFact(f) => Ok(AtomicFact::InFact(InFact {
            fact_id,
            element: ctx.inst_obj(&f.element)?,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotInFact(f) => Ok(AtomicFact::NotInFact(NotInFact {
            fact_id,
            element: ctx.inst_obj(&f.element)?,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsCartFact(f) => Ok(AtomicFact::IsCartFact(IsCartFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsCartFact(f) => Ok(AtomicFact::NotIsCartFact(NotIsCartFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsTupleFact(f) => Ok(AtomicFact::IsTupleFact(IsTupleFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsTupleFact(f) => Ok(AtomicFact::NotIsTupleFact(NotIsTupleFact {
            fact_id,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SubsetFact(f) => Ok(AtomicFact::SubsetFact(SubsetFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSubsetFact(f) => Ok(AtomicFact::NotSubsetFact(NotSubsetFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SupersetFact(f) => Ok(AtomicFact::SupersetFact(SupersetFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSupersetFact(f) => Ok(AtomicFact::NotSupersetFact(NotSupersetFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::FnEqualInFact(f) => Ok(AtomicFact::FnEqualInFact(FnEqualInFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            set: ctx.inst_obj(&f.set)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::FnEqualFact(f) => Ok(AtomicFact::FnEqualFact(FnEqualFact {
            fact_id,
            left: ctx.inst_obj(&f.left)?,
            right: ctx.inst_obj(&f.right)?,
            line_file: f.line_file.clone(),
        })),
    }
}
