use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_wd(
        &self,
        proof: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::WD(proof),
            before: 0,
        };
        let position = &source_position;
        match proof {
            ObjWellDefinedProof::ByKnown { obj, wd_id } => {
                let recorded = self.resolve_wd(*wd_id, position)?;
                if recorded.ir() != obj.ir() {
                    return Err(LeanCompileError::new(
                        "WD/ByKnown",
                        "WD id resolves to another object.",
                    ));
                }
                // A cache record is not a proof. Only an earlier replayed constructor
                // or an explicitly introduced certified parameter supplies this term.
                let term = self.compile_object_reference(obj, position)?;
                Ok(term)
            }
            ObjWellDefinedProof::ByDef { obj, proof } => {
                let term = match (obj, proof) {
                    (
                        Obj::Identifier(IdentifierObj::Plain { .. }),
                        ObjWellDefinedProofByDef::Identifier(_),
                    ) => self.compile_object_reference(obj, position)?,
                    (
                        Obj::Literal(Literal::Number(number)),
                        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(
                            _,
                        )),
                    ) => {
                        let value = number_literal(number, "ℂ")?;
                        format!("(Litex.number (M := M) {value})")
                    }
                    (Obj::StandardSet(set), ObjWellDefinedProofByDef::StandardSet(_)) => {
                        standard_term(set)?
                    }
                    (Obj::FunctionSpace(space), ObjWellDefinedProofByDef::FunctionSpace(proof)) => {
                        self.compile_function_space_wd(space, proof, position)?
                    }
                    (Obj::FnObj(application), ObjWellDefinedProofByDef::FnObj(proof)) => {
                        self.compile_fn_obj_wd(application, proof, position)?
                    }
                    (
                        Obj::ArithmeticOperator(operator),
                        ObjWellDefinedProofByDef::ArithmeticOperator(wd),
                    ) => {
                        let term = match (operator, wd) {
                            (
                                ArithmeticOperator::Add(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Add(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Add,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Sub(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Sub(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Sub,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Mul(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Mul(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Mul,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Div(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Div,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Neg(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Neg(p),
                            ) => self.compile_neg_wd(
                                &x.arg,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Pow(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                            ) => self.compile_pow_wd(
                                &x.base,
                                &x.exponent,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                position,
                            )?,
                            _ => {
                                return Err(LeanCompileError::unsupported("WD/ArithmeticOperator"))
                            }
                        };
                        term
                    }
                    (_, unsupported) => return Err(unsupported_wd_definition(unsupported)),
                };
                Ok(term)
            }
        }
    }

    pub(in crate::compile_to_lean) fn compile_atomic_wd(
        &self,
        wd: &AtomicFactWellDefinedProof,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::AtomicWD(wd),
            before: 0,
        };
        let position = &source_position;
        let args = atomic_fact_args_ref(fact);
        if wd.well_defined_of_each_parameter.len() != args.len() {
            return Err(LeanCompileError::new(
                "WD/Atomic",
                "Object WD evidence has the wrong argument arity.",
            ));
        }
        for (index, (arg, proof)) in args
            .iter()
            .zip(&wd.well_defined_of_each_parameter)
            .enumerate()
        {
            ensure_object(arg, proof)?;
            self.compile_wd(
                proof,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
        }
        match &wd.predicate_signature {
            PredicateSignatureWellDefinedProof::Builtin => {
                if matches!(fact, AtomicFact::NormalAtomicFact(_)) {
                    return Err(LeanCompileError::new(
                        "Prop/SignatureFamily",
                        "A concrete source predicate cannot use a builtin predicate signature.",
                    ));
                }
            }
            signature @ PredicateSignatureWellDefinedProof::Prop { .. } => {
                self.validate_prop_predicate_signature(signature, fact, position)?;
            }
            PredicateSignatureWellDefinedProof::AbstractProp { .. } => {
                return Err(LeanCompileError::unsupported("WD/UserPredicate"))
            }
        }
        match &wd.predicate_domain {
            PredicateDomainProof::ByRequirements(requirements) => {
                if matches!(fact, AtomicFact::NormalAtomicFact(_)) && !requirements.is_empty() {
                    return Err(LeanCompileError::new(
                        "WD/PropDomain",
                        "Concrete predicate formation has no extra domain stages; its typed memberships belong to definition proof or assumption meaning.",
                    ));
                }
                if matches!(
                    fact,
                    AtomicFact::LessFact(_)
                        | AtomicFact::GreaterFact(_)
                        | AtomicFact::LessEqualFact(_)
                        | AtomicFact::GreaterEqualFact(_)
                        | AtomicFact::NotLessFact(_)
                        | AtomicFact::NotGreaterFact(_)
                        | AtomicFact::NotLessEqualFact(_)
                        | AtomicFact::NotGreaterEqualFact(_)
                ) {
                    if requirements.len() != 2 || requirements.iter().zip(&args).any(|(requirement, argument)| !matches!(&requirement.requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == argument.ir() && f.set == Obj::StandardSet(StandardSet::R))) {
                        return Err(LeanCompileError::new("WD/OrderRealDomain", "The order predicate needs its two exact ordered real-membership stages."));
                    }
                }
                for (index, requirement) in requirements.iter().enumerate() {
                    let _compiled = self.compile_verify(
                        &requirement.result,
                        &SourcePosition {
                            before: args.len() + index,
                            ..*position
                        },
                    )?;
                    if source_subject(&requirement.result)? != requirement.requirement {
                        return Err(LeanCompileError::new(
                            "WD/PredicateDomain",
                            "Verified domain requirement has another subject.",
                        ));
                    }
                }
            }
            PredicateDomainProof::ByKnownFact(proof) => {
                let formed = SourcePosition {
                    before: args.len(),
                    ..*position
                };
                let known = self.compile_known_atomic(proof, fact, &formed)?;
                let _ = known;
            }
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_fact_wd(
        &self,
        wd: &FactWellDefinedProof,
        fact: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::FactWD(wd),
            before: 0,
        };
        let position = &source_position;
        match (wd, fact) {
            (FactWellDefinedProof::AtomicExceptEquality(wd), Fact::AtomicFact(atomic)) => {
                self.compile_atomic_wd(wd, atomic, position)
            }
            (
                FactWellDefinedProof::Equality(wd),
                Fact::AtomicFact(AtomicFact::EqualFact(equal)),
            ) => {
                ensure_object(&equal.left, &wd.left)?;
                ensure_object(&equal.right, &wd.right)?;
                self.compile_wd(&wd.left, position)?;
                self.compile_wd(
                    &wd.right,
                    &SourcePosition {
                        before: 1,
                        ..*position
                    },
                )?;
                Ok(())
            }
            (FactWellDefinedProof::Equality(_), _) => Err(LeanCompileError::new(
                "WD/Fact",
                "Equality WD has another subject.",
            )),
            (FactWellDefinedProof::AtomicExceptEquality(_), _) => Err(LeanCompileError::new(
                "WD/Fact",
                "Atomic WD has another subject.",
            )),
            (FactWellDefinedProof::ForallFact(proof), Fact::ForallFact(fact)) => {
                self.compile_forall_wd(fact, proof, position)
            }
            (FactWellDefinedProof::ForallFact(_), _) => Err(LeanCompileError::new(
                "WD/ForallSubject",
                "Quantified WD evidence has another source fact family.",
            )),
            (
                FactWellDefinedProof::AndFact { .. }
                | FactWellDefinedProof::ChainFact { .. }
                | FactWellDefinedProof::OrFact(_)
                | FactWellDefinedProof::ExistFact(_)
                | FactWellDefinedProof::ForallFactWithIff(_)
                | FactWellDefinedProof::NotForall(_),
                _,
            ) => Err(LeanCompileError::unsupported("WD/CompoundFact")),
        }
    }

    // The goal's WD scope predates the named theorem's separate truth scope.
    // Its actual parameter/domain producers cannot be replaced by body IDs.
}
