use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_membership_certificate(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
            if let Ok((_, set, _, hypothesis)) = position.visible_parameter(*id, &self.runtime) {
                if set == &Obj::StandardSet(StandardSet::R) {
                    return Ok(hypothesis);
                }
            }
        }
        if let Some(proof) = position.with_visible_membership(
            object,
            &Obj::StandardSet(StandardSet::R),
            &mut |result, producer| {
                self.compile_verify(result, producer)
                    .map(|compiled| compiled.1)
            },
        )? {
            return Ok(proof);
        }
        if let Some(proof) = position
            .with_visible_alias(object, &mut |_, value, wd, producer| {
                let wd = success_object_wd(wd, value)?;
                self.numeric_function_real_wd(wd, producer)
            })?
            .flatten()
        {
            return Ok(proof);
        }
        if matches!(object, Obj::FnObj(_)) {
            if let Some(proof) = position
                .with_visible_wd(object, &mut |wd, producer| {
                    self.numeric_function_real_wd(wd, producer)
                })?
                .flatten()
            {
                return Ok(proof);
            }
        }
        let mut current = Some(position);
        while let Some(cursor) = current {
            if let SourceOwner::Verify(VerifyFactResult::AtomicExceptEquality(result)) =
                cursor.owner
            {
                if let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() {
                    if cursor.before
                        >= proof
                            .well_defined_proof
                            .well_defined_of_each_parameter
                            .len()
                        && source_order_parts(&proof.fact).is_ok()
                    {
                        if let PredicateDomainProof::ByKnownFact(known) =
                            &proof.well_defined_proof.predicate_domain
                        {
                            let args = atomic_fact_args_ref(&proof.fact);
                            if args.len() == 2
                                && (object.ir() == args[0].ir() || object.ir() == args[1].ir())
                            {
                                let certificate =
                                    self.compile_known_atomic(known, &proof.fact, cursor)?;
                                let members = self.order_real_members_from_known(
                                    &proof.fact,
                                    &certificate,
                                    cursor,
                                )?;
                                return Ok(if object.ir() == args[0].ir() {
                                    members.0
                                } else {
                                    members.1
                                });
                            }
                        }
                    }
                }
            }
            current = cursor.parent;
        }
        Err(LeanCompileError::new(
            "Real/Producer",
            "No earlier original result supplies this exact real-membership certificate.",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_numeric_observation(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        if let Some(observation) =
            position.with_visible_alias(object, &mut |_, value, wd, producer| {
                let wd = success_object_wd(wd, value)?;
                self.numeric_wd(wd, producer)
            })?
        {
            return Ok(observation);
        }
        if !matches!(object, Obj::Identifier(_)) {
            if let Some(observation) = position
                .with_visible_wd(object, &mut |wd, producer| self.numeric_wd(wd, producer))?
            {
                return Ok(observation);
            }
        }
        if is_exact_zero(object) && position.has_visible_inferred_natural_zero() {
            return Ok((
                "(0 : ℂ)".into(),
                "(Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))".into(),
                "(Litex.numberInC (M := M) (0 : ℂ))".into(),
                EvalRational::new(0, 1),
            ));
        }
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
            if let Ok((_, set, _, hypothesis)) = position.visible_parameter(*id, &self.runtime) {
                if set == &Obj::StandardSet(StandardSet::C) {
                    return self.numeric_member(object, &hypothesis, position);
                }
                if set == &Obj::StandardSet(StandardSet::R) {
                    let term = self.compile_object_reference(object, position)?;
                    return self.numeric_member(
                        object,
                        &format!("(Litex.realToComplex {term} {hypothesis})"),
                        position,
                    );
                }
            }
        }
        if let Some(observation) = position.with_visible_membership(
            object,
            &Obj::StandardSet(StandardSet::C),
            &mut |result, producer| {
                let (_, member) = self.compile_verify(result, producer)?;
                self.numeric_member(object, &member, producer)
            },
        )? {
            return Ok(observation);
        }
        if let Some(observation) = position.with_visible_membership(
            object,
            &Obj::StandardSet(StandardSet::R),
            &mut |result, producer| {
                let (_, real) = self.compile_verify(result, producer)?;
                let term = self.compile_object_reference(object, producer)?;
                self.numeric_member(
                    object,
                    &format!("(Litex.realToComplex {term} {real})"),
                    producer,
                )
            },
        )? {
            return Ok(observation);
        }
        Err(LeanCompileError::new("Arithmetic/NumericEvidence", "No preceding original constructor or checked C-membership certificate supplies this observation."))
    }

    pub(in crate::compile_to_lean) fn numeric_member(
        &self,
        object: &Obj,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let term = self.compile_object_reference(object, position)?;
        Ok((
            format!("(Litex.NativeBridge.asComplex {term} {member})"),
            format!("(Litex.NativeBridge.asComplex_spec {term} {member})"),
            member.to_string(),
            None,
        ))
    }

    pub(in crate::compile_to_lean) fn numeric_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        match wd {
            ObjWellDefinedProof::ByKnown { obj, .. } => {
                self.compile_numeric_observation(obj, position)
            }
            ObjWellDefinedProof::ByDef {
                obj: Obj::Literal(Literal::Number(number)),
                proof: ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(_)),
            } => {
                let value = number_literal(number, "ℂ")?;
                Ok((
                    value.clone(),
                    format!("(Litex.NativeBridge.denoteNumber (M := M) {value})"),
                    format!("(Litex.numberInC (M := M) {value})"),
                    EvalRational::from_obj(match wd {
                        ObjWellDefinedProof::ByDef { obj, .. } => obj,
                        _ => unreachable!(),
                    }),
                ))
            }
            ObjWellDefinedProof::ByDef {
                obj: Obj::ArithmeticOperator(operation),
                proof: ObjWellDefinedProofByDef::ArithmeticOperator(proof),
            } => {
                let position = SourcePosition {
                    parent: Some(position),
                    owner: SourceOwner::WD(wd),
                    before: usize::MAX,
                };
                let pair = match (operation, proof) {
                    (
                        ArithmeticOperator::Add(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Add(p),
                    ) => self.numeric_binary_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        BinaryArithmetic::Add,
                        &position,
                    ),
                    (
                        ArithmeticOperator::Sub(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Sub(p),
                    ) => self.numeric_binary_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        BinaryArithmetic::Sub,
                        &position,
                    ),
                    (
                        ArithmeticOperator::Mul(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Mul(p),
                    ) => self.numeric_binary_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        BinaryArithmetic::Mul,
                        &position,
                    ),
                    (
                        ArithmeticOperator::Div(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                    ) => self.numeric_binary_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        BinaryArithmetic::Div,
                        &position,
                    ),
                    (
                        ArithmeticOperator::Neg(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Neg(p),
                    ) => self.numeric_neg_wd(
                        &x.arg,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        &position,
                    ),
                    (
                        ArithmeticOperator::Pow(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                    ) => self.numeric_pow_wd(
                        &x.base,
                        &x.exponent,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        &position,
                    ),
                    _ => return Err(LeanCompileError::unsupported("WD/ArithmeticOperator")),
                }?;
                Ok(pair)
            }
            ObjWellDefinedProof::ByDef {
                obj: Obj::FnObj(_),
                proof: ObjWellDefinedProofByDef::FnObj(_),
            } => {
                let (call, output, member) = self.numeric_function_output_wd(wd, position)?;
                let complex = match output {
                    StandardSet::N => format!("(Litex.naturalToComplex {call} {member})"),
                    StandardSet::Z => format!("(Litex.integerToComplex {call} {member})"),
                    StandardSet::Q => format!("(Litex.rationalToComplex {call} {member})"),
                    StandardSet::R => format!("(Litex.realToComplex {call} {member})"),
                    StandardSet::C => member,
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "Arithmetic/FunctionOutputCarrier",
                        ))
                    }
                };
                // The term is this actual constructor, so observing its return
                // law never asks the current WD cursor to rediscover itself.
                Ok((
                    format!("(Litex.NativeBridge.asComplex {call} {complex})"),
                    format!("(Litex.NativeBridge.asComplex_spec {call} {complex})"),
                    complex,
                    None,
                ))
            }
            ObjWellDefinedProof::ByDef {
                obj,
                proof: ObjWellDefinedProofByDef::Identifier(_),
            } => {
                // An identifier WD carries no numeric assertion. Its actual
                // preceding membership proof supplies the observation separately.
                if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = obj {
                    if let Ok((_, set, _, member)) = position.visible_parameter(*id, &self.runtime)
                    {
                        if set == &Obj::StandardSet(StandardSet::C) {
                            return self.numeric_member(obj, &member, position);
                        }
                    }
                }
                if let Some(observation) = position.with_visible_membership(
                    obj,
                    &Obj::StandardSet(StandardSet::C),
                    &mut |result, producer| {
                        let (_, member) = self.compile_verify(result, producer)?;
                        self.numeric_member(obj, &member, producer)
                    },
                )? {
                    return Ok(observation);
                }
                if let Some(observation) = position.with_visible_membership(
                    obj,
                    &Obj::StandardSet(StandardSet::R),
                    &mut |result, producer| {
                        let (_, real) = self.compile_verify(result, producer)?;
                        let term = self.compile_object_reference(obj, producer)?;
                        self.numeric_member(
                            obj,
                            &format!("(Litex.realToComplex {term} {real})"),
                            producer,
                        )
                    },
                )? {
                    return Ok(observation);
                }
                Err(LeanCompileError::new(
                    "Arithmetic/NumericEvidence",
                    "Identifier WD alone does not certify numeric membership.",
                ))
            }
            ObjWellDefinedProof::ByDef { proof, .. } => Err(unsupported_wd_definition(proof)),
        }
    }

    fn numeric_function_output_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, StandardSet, String), LeanCompileError> {
        let ObjWellDefinedProof::ByDef {
            obj: Obj::FnObj(application),
            proof: ObjWellDefinedProofByDef::FnObj(proof),
        } = wd
        else {
            return Err(LeanCompileError::new(
                "Arithmetic/FunctionOutputWD",
                "Function output observation needs its original application constructor.",
            ));
        };
        let constructor = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::WD(wd),
            before: 0,
        };
        let (call, output) = self.compile_fn_call_with_return(application, proof, &constructor)?;
        let law = if application.body[0].len() == 1 {
            "callInOutput"
        } else {
            "call2InOutput"
        };
        let member = format!("(Litex.{law} {call})");
        Ok((call, output, member))
    }

    fn numeric_function_real_wd(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        match wd {
            ObjWellDefinedProof::ByKnown {
                obj: object @ Obj::FnObj(_),
                wd_id,
            } => {
                if self.resolve_wd(*wd_id, position)?.ir() != object.ir() {
                    return Err(LeanCompileError::new(
                        "WD/ByKnown",
                        "Cached function WD resolves to another source object.",
                    ));
                }
                // Only a preceding original ByDef constructor can supply the
                // cached call's output tag and its checked domain certificates.
                Ok(position
                    .with_visible_wd(object, &mut |wd, producer| {
                        self.numeric_function_real_wd(wd, producer)
                    })?
                    .flatten())
            }
            ObjWellDefinedProof::ByDef {
                obj: Obj::FnObj(_),
                proof: ObjWellDefinedProofByDef::FnObj(_),
            } => {
                let (call, output, member) = self.numeric_function_output_wd(wd, position)?;
                Ok(match output {
                    StandardSet::N => Some(format!("(Litex.naturalToReal {call} {member})")),
                    StandardSet::Z => Some(format!("(Litex.integerToReal {call} {member})")),
                    StandardSet::Q => Some(format!("(Litex.rationalToReal {call} {member})")),
                    StandardSet::R => Some(member),
                    // A checked C return certifies a complex value only. Any
                    // later R assertion still needs its own source certificate.
                    _ => None,
                })
            }
            _ => Ok(None),
        }
    }
}
