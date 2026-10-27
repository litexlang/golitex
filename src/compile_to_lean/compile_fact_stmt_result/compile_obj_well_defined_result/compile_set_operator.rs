use crate::compile_to_lean::helper::{ensure_object, source_subject};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_operator_wd(
        &self,
        object: &SetOperator,
        proof: &SetOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (constructor, children, requirements, subjects): (_, _, _, Vec<&Obj>) =
            match (object, proof) {
                (
                    SetOperator::IndexUnion(value),
                    SetOperatorObjWellDefinedProofByDef::IndexUnion(wd),
                ) => (
                    "indexUnion",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![
                        value.index_set.as_ref(),
                        value.ambient_set.as_ref(),
                        value.family_fn.as_ref(),
                    ],
                ),
                (
                    SetOperator::IndexIntersect(value),
                    SetOperatorObjWellDefinedProofByDef::IndexIntersect(wd),
                ) => (
                    "indexIntersect",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![
                        value.index_set.as_ref(),
                        value.ambient_set.as_ref(),
                        value.family_fn.as_ref(),
                    ],
                ),
                (
                    SetOperator::IndexCart(value),
                    SetOperatorObjWellDefinedProofByDef::IndexCart(wd),
                ) => (
                    "indexCart",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![
                        value.index_set.as_ref(),
                        value.family_set.as_ref(),
                        value.family_fn.as_ref(),
                    ],
                ),
                (
                    SetOperator::SymmetricDifference(value),
                    SetOperatorObjWellDefinedProofByDef::SymmetricDifference(wd),
                ) => (
                    "symmetricDifference",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref(), value.right.as_ref()],
                ),
                (
                    SetOperator::FamilyIntersect(value),
                    SetOperatorObjWellDefinedProofByDef::FamilyIntersect(wd),
                ) => (
                    "familyIntersect",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref()],
                ),
                (
                    SetOperator::FamilyUnion(value),
                    SetOperatorObjWellDefinedProofByDef::FamilyUnion(wd),
                ) => (
                    "familyUnion",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref()],
                ),
                (SetOperator::Union(value), SetOperatorObjWellDefinedProofByDef::Union(wd)) => (
                    "union",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref(), value.right.as_ref()],
                ),
                (
                    SetOperator::PowerSet(value),
                    SetOperatorObjWellDefinedProofByDef::PowerSet(wd),
                ) => (
                    "powerSet",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.set.as_ref()],
                ),
                (
                    SetOperator::Intersect(value),
                    SetOperatorObjWellDefinedProofByDef::Intersect(wd),
                ) => (
                    "intersect",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref(), value.right.as_ref()],
                ),
                (
                    SetOperator::SetMinus(value),
                    SetOperatorObjWellDefinedProofByDef::SetMinus(wd),
                ) => (
                    "setMinus",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref(), value.right.as_ref()],
                ),
                (
                    SetOperator::FamilyUnion(_)
                    | SetOperator::Union(_)
                    | SetOperator::Intersect(_)
                    | SetOperator::SetMinus(_)
                    | SetOperator::PowerSet(_),
                    _,
                ) => {
                    return Err(LeanCompileError::new(
                        "SetOperator/Constructor",
                        "Set operator evidence belongs to another source constructor.",
                    ))
                }
                _ => return Err(LeanCompileError::unsupported("WD/SetOperator")),
            };
        let indexed = matches!(
            object,
            SetOperator::IndexUnion(_) | SetOperator::IndexIntersect(_) | SetOperator::IndexCart(_)
        );
        let family_intersect = matches!(object, SetOperator::FamilyIntersect(_));
        let requirement_count = if indexed {
            4
        } else if family_intersect {
            1
        } else {
            0
        };
        if children.len() != subjects.len() || requirements.len() != requirement_count {
            return Err(LeanCompileError::new(
                "SetOperator/Stages",
                "This set operator requires its ordered child and domain WD stages.",
            ));
        }
        let mut terms = Vec::with_capacity(subjects.len());
        for (index, (subject, child)) in subjects.iter().zip(children).enumerate() {
            ensure_object(subject, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        if family_intersect {
            if !matches!(source_subject(&requirements[0])?, Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==subjects[0].ir())
            {
                return Err(LeanCompileError::unsupported("FamilyIntersect/NonemptyWD"));
            }
            terms.push(
                self.compile_verify(
                    &requirements[0],
                    &SourcePosition {
                        before: children.len(),
                        ..*position
                    },
                )?
                .1,
            );
        }
        if indexed {
            let cart = matches!(object, SetOperator::IndexCart(_));
            for (i, proof) in requirements.iter().enumerate() {
                let fact = source_subject(proof)?;
                let valid = match (i, &fact) {
                    (0, Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f))) => {
                        f.set.ir() == subjects[0].ir()
                    }
                    (1, Fact::AtomicFact(AtomicFact::IsSetFact(f))) => {
                        f.set.ir() == subjects[0].ir()
                    }
                    (2, Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f))) if cart => {
                        f.set.ir() == subjects[1].ir()
                    }
                    (2, Fact::AtomicFact(AtomicFact::IsSetFact(f))) if !cart => {
                        f.set.ir() == subjects[1].ir()
                    }
                    (3, Fact::AtomicFact(AtomicFact::InFact(f)))
                        if f.element.ir() == subjects[2].ir() =>
                    {
                        if let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &f.set {
                            s.dom_facts.is_empty()
                                && s.set_bound_parameters.groups.len() == 1
                                && s.set_bound_parameters.groups[0].params.len() == 1
                                && s.set_bound_parameters.groups[0].param_type.ir()
                                    == subjects[0].ir()
                                && if cart {
                                    s.ret_set.ir() == subjects[1].ir()
                                } else {
                                    matches!(&*s.ret_set, Obj::SetOperator(SetOperator::PowerSet(p)) if p.set.ir()==subjects[1].ir())
                                }
                        } else {
                            false
                        }
                    }
                    _ => false,
                };
                if !valid {
                    return Err(LeanCompileError::unsupported("IndexedSet/WDRequirement"));
                }
                terms.push(
                    self.compile_verify(
                        proof,
                        &SourcePosition {
                            before: children.len() + i,
                            ..*position
                        },
                    )?
                    .1,
                );
            }
        }
        Ok(format!("(Litex.{constructor} {})", terms.join(" ")))
    }
}
