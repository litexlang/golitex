use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_membership_certificate(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
            if let Ok((_, Some(set), _, hypothesis)) =
                position.visible_parameter(*id, &self.runtime)
            {
                if let Obj::StandardSet(set) = set {
                    if *set == StandardSet::NPos || numeric_refinement(set).is_some() {
                        if *set != StandardSet::CStar {
                            return standard_inclusion_term(
                                set,
                                &StandardSet::R,
                                &self.compile_object_reference(object, position)?,
                                &hypothesis,
                            );
                        }
                    }
                }
                if set == &Obj::StandardSet(StandardSet::R) {
                    return Ok(hypothesis);
                }
                if set == &Obj::StandardSet(StandardSet::RPos) {
                    return Ok(format!(
                        "(Litex.inRPos_real {} {hypothesis})",
                        self.compile_object_reference(object, position)?
                    ));
                }
                let bridge = match set {
                    Obj::StandardSet(StandardSet::N) => Some("naturalToReal"),
                    Obj::StandardSet(StandardSet::Z) => Some("integerToReal"),
                    Obj::StandardSet(StandardSet::Q) => Some("rationalToReal"),
                    _ => None,
                };
                if let Some(bridge) = bridge {
                    return Ok(format!(
                        "(Litex.{bridge} {} {hypothesis})",
                        self.compile_object_reference(object, position)?
                    ));
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
        if let Some(proof) = position.with_visible_membership(
            object,
            &Obj::StandardSet(StandardSet::RPos),
            &mut |result, producer| {
                let (_, positive) = self.compile_verify(result, producer)?;
                Ok(format!(
                    "(Litex.inRPos_real {} {positive})",
                    self.compile_object_reference(object, producer)?
                ))
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
                        if let PredicateDomainProof::ByCheckedArguments(requirements) =
                            &proof.well_defined_proof.predicate_domain
                        {
                            let args = atomic_fact_args_ref(&proof.fact);
                            for requirement in requirements {
                                if requirement.membership.element != *object {
                                    continue;
                                }
                                if requirement.membership.set != StandardSet::R
                                    || args
                                        .get(requirement.argument_index)
                                        .is_none_or(|arg| *arg != object)
                                    || !matches!(&requirement.requirement, Fact::AtomicFact(AtomicFact::InFact(member)) if member.element == *object && member.set == Obj::StandardSet(StandardSet::R))
                                {
                                    return Err(LeanCompileError::new("WD/OrderRealDomain", "Real-domain evidence is not attached to its checked argument."));
                                }
                                let producer = SourcePosition::new(
                                    Some(cursor),
                                    SourceOwner::AtomicWD(&proof.well_defined_proof),
                                    args.len() + requirement.argument_index,
                                );
                                return self.compile_structural(&requirement.membership, &producer);
                            }
                        }
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
        if let Some(number) = position.enumeration_literal(object) {
            let value = number_literal(number, "ℂ")?;
            return Ok((
                value.clone(),
                format!("(Litex.NativeBridge.denoteNumber (M := M) {value})"),
                format!("(Litex.numberInC (M := M) {value})"),
                EvalRational::from_obj(object),
            ));
        }
        if let Some(observation) =
            position.with_visible_alias(object, &mut |_, value, wd, producer| {
                let wd = success_object_wd(wd, value)?;
                self.numeric_wd(wd, producer)
            })?
        {
            return Ok(observation);
        }
        if let Some(observation) = self.numeric_preimage_call(object, position)? {
            return Ok(observation);
        }
        if let Some(observation) = self.numeric_inferred_coordinate(object, position)? {
            return Ok(observation);
        }
        if let Some(observation) = self.numeric_struct_field(object, position)? {
            return Ok(observation);
        }
        if !matches!(object, Obj::Identifier(_)) {
            if let Some(observation) = position
                .with_visible_wd(object, &mut |wd, producer| self.numeric_wd(wd, producer))?
            {
                return Ok(observation);
            }
        }
        if let Obj::Literal(Literal::Number(number)) = object {
            if let Some(observation) =
                position.with_visible_inferred_subject(object, &mut |_, _| {
                    let value = number_literal(number, "ℂ")?;
                    Ok((
                        value.clone(),
                        format!("(Litex.NativeBridge.denoteNumber (M := M) {value})"),
                        format!("(Litex.numberInC (M := M) {value})"),
                        EvalRational::from_obj(object),
                    ))
                })?
            {
                return Ok(observation);
            }
        }
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
            if let Ok((_, Some(set), _, hypothesis)) =
                position.visible_parameter(*id, &self.runtime)
            {
                if let Some(member) =
                    self.parameter_complex_membership(object, set, &hypothesis, position)?
                {
                    return self.numeric_member(object, &member, position);
                }
            }
        }
        // Replay formation owned by the exact named inference before consuming
        // a membership citation whose argument matching can observe this same
        // expression. This keeps the source dependency acyclic.
        if matches!(object, Obj::ArithmeticOperator(_)) {
            if let Some(observation) = position
                .with_visible_inferred_subject(object, &mut |_, producer| {
                    self.compile_inferred_numeric_observation(object, producer)
                })?
            {
                return Ok(observation);
            }
        }
        // An obtained compound term retains its original constructor WD.
        // Observe that operation before falling back to an opaque scalar from
        // membership, so the normalization certificate sees the same factors.
        if let Some(observation) =
            self.compile_callee_expression_reference(object, position, true)?
        {
            return Ok((
                format!("({observation}).val"),
                format!("({observation}).property.1"),
                format!("({observation}).property.2"),
                EvalRational::from_obj(object),
            ));
        }
        if let Some(observation) =
            self.compile_obtain_expression_reference(object, position, true)?
        {
            return Ok((
                format!("({observation}).val"),
                format!("({observation}).property.1"),
                format!("({observation}).property.2"),
                None,
            ));
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
            &Obj::StandardSet(StandardSet::RPos),
            &mut |result, producer| {
                let (_, positive) = self.compile_verify(result, producer)?;
                let term = self.compile_object_reference(object, producer)?;
                self.numeric_member(
                    object,
                    &format!("(Litex.positiveRealToComplex {term} {positive})"),
                    producer,
                )
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
        Err(LeanCompileError::new("Arithmetic/NumericEvidence", &format!("No preceding original constructor or checked C-membership certificate supplies the observation of {}.", object.ir())))
    }

    fn numeric_struct_field(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(String, String, String, Option<EvalRational>)>, LeanCompileError> {
        if !matches!(
            object,
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_))
        ) {
            return Ok(None);
        }
        position.with_visible_inferred_subject_filter(object, &mut |store, producer| {
            let StoreFactResult::AtomicFact(stored) = store else {
                return Ok(None);
            };
            let AtomicFact::InFact(member) = &stored.fact else {
                return Ok(None);
            };
            if member.element.ir() != object.ir() {
                return Ok(None);
            }
            let (actual, reference) = producer.visible_fact(stored.fact_id, &self.runtime)?;
            if actual != &Fact::AtomicFact(stored.fact.clone()) {
                return Err(LeanCompileError::unsupported(
                    "StructField/MembershipSubject",
                ));
            }
            let Some(complex) =
                self.parameter_complex_membership(object, &member.set, &reference, producer)?
            else {
                return Ok(None);
            };
            self.numeric_member(object, &complex, producer).map(Some)
        })
    }

    fn numeric_inferred_coordinate(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(String, String, String, Option<EvalRational>)>, LeanCompileError> {
        if !is_literal_coordinate_call(object) {
            return Ok(None);
        }
        let observation =
            position.with_visible_inferred_subject_filter(object, &mut |store, producer| {
                let Some(term) = self.compile_cart_inferred_subject(object, store, producer)?
                else {
                    return Ok(None);
                };
                let StoreFactResult::AtomicFact(stored) = store else {
                    return Ok(None);
                };
                let AtomicFact::InFact(member) = &stored.fact else {
                    return Ok(None);
                };
                let (actual, reference) = producer.visible_fact(stored.fact_id, &self.runtime)?;
                if actual != &Fact::AtomicFact(stored.fact.clone()) {
                    return Err(LeanCompileError::new(
                        "CartInference/ObservationSubject",
                        "The coordinate observation cites another stored membership.",
                    ));
                }
                let Some(complex) =
                    self.parameter_complex_membership(object, &member.set, &reference, producer)?
                else {
                    return Ok(None);
                };
                Ok(Some((
                    format!("(Litex.NativeBridge.asComplex {term} {complex})"),
                    format!("(Litex.NativeBridge.asComplex_spec {term} {complex})"),
                    complex,
                    None,
                )))
            })?;
        Ok(observation)
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
            ObjWellDefinedProof::ByDef {
                obj: Obj::ComplexOperator(_),
                proof: ObjWellDefinedProofByDef::ComplexOperator(_),
            } => self.numeric_complex_wd(wd, position),
            ObjWellDefinedProof::ByDef {
                obj: Obj::HyperbolicOperator(_),
                proof: ObjWellDefinedProofByDef::HyperbolicOperator(_),
            } => self.numeric_hyperbolic_wd(wd, position),
            ObjWellDefinedProof::ByDef {
                obj: Obj::TrigOperator(_),
                proof: ObjWellDefinedProofByDef::TrigOperator(_),
            } => self.numeric_trig_wd(wd, position),
            ObjWellDefinedProof::ByDef {
                obj:
                    Obj::ExpLogOperator(
                        ExpLogOperator::Exp(_) | ExpLogOperator::Ln(_) | ExpLogOperator::Log(_),
                    ),
                proof: ObjWellDefinedProofByDef::ExpLogOperator(_),
            } => self.numeric_exp_log_wd(wd, position),
            ObjWellDefinedProof::ByDef {
                obj,
                proof: ObjWellDefinedProofByDef::Literal(_),
            } if native_real_constant(obj).is_some() => {
                self.compile_wd(wd, position)?;
                let value = format!("({} : ℂ)", native_real_constant(obj).unwrap());
                Ok((
                    value.clone(),
                    format!("(Litex.NativeBridge.denoteNumber (M := M) {value})"),
                    format!("(Litex.numberInC (M := M) {value})"),
                    None,
                ))
            }
            ObjWellDefinedProof::ByDef {
                obj: Obj::FiniteSetStat(_),
                proof: ObjWellDefinedProofByDef::FiniteSetStat(_),
            } => self.numeric_finite_stat_wd(wd, position),
            ObjWellDefinedProof::ByDef {
                obj: object @ Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_)),
                ..
            } => {
                self.compile_wd(wd, position)?;
                self.numeric_struct_field(object, position)?
                    .ok_or_else(|| LeanCompileError::unsupported("StructField/NumericMembership"))
            }

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
                obj: Obj::Literal(Literal::ImaginaryUnit(_)),
                proof:
                    ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::ImaginaryUnit(_)),
            } => Ok((
                "Complex.I".into(),
                "(Litex.NativeBridge.denoteNumber (M := M) Complex.I)".into(),
                "(Litex.numberInC (M := M) Complex.I)".into(),
                None,
            )),
            ObjWellDefinedProof::ByDef {
                obj: Obj::IntegerOperator(operator),
                proof: ObjWellDefinedProofByDef::IntegerOperator(proof),
            } => {
                let position = SourcePosition {
                    parent: Some(position),
                    owner: SourceOwner::WD(wd),
                    before: usize::MAX,
                };
                match (operator, proof) {
                    (
                        IntegerOperator::Factorial(_),
                        IntegerOperatorObjWellDefinedProofByDef::Factorial(p),
                    ) => self.numeric_factorial_wd(wd, &p.child_obj_well_defined, &position),
                    (IntegerOperator::Gcd(_), IntegerOperatorObjWellDefinedProofByDef::Gcd(p)) => {
                        self.numeric_gcd_lcm_wd(wd, &p.child_obj_well_defined, false, &position)
                    }
                    (IntegerOperator::Lcm(_), IntegerOperatorObjWellDefinedProofByDef::Lcm(p)) => {
                        self.numeric_gcd_lcm_wd(wd, &p.child_obj_well_defined, true, &position)
                    }
                    (IntegerOperator::Mod(_), IntegerOperatorObjWellDefinedProofByDef::Mod(p)) => {
                        self.numeric_integer_division_wd(
                            wd,
                            &p.child_obj_well_defined,
                            false,
                            &position,
                        )
                    }
                    (
                        IntegerOperator::Quot(_),
                        IntegerOperatorObjWellDefinedProofByDef::Quot(p),
                    ) => self.numeric_integer_division_wd(
                        wd,
                        &p.child_obj_well_defined,
                        true,
                        &position,
                    ),
                    _ => Err(LeanCompileError::unsupported(
                        "NumericObservation/IntegerOperator",
                    )),
                }
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
                        ArithmeticOperator::Abs(x),
                        ArithmeticOperatorObjWellDefinedProofByDef::Abs(p),
                    ) => self.numeric_abs_wd(
                        &x.arg,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        &position,
                    ),
                    (
                        ArithmeticOperator::Min(_),
                        ArithmeticOperatorObjWellDefinedProofByDef::Min(p),
                    ) => self.numeric_min_max_wd(wd, &p.child_obj_well_defined, false, &position),
                    (
                        ArithmeticOperator::Sign(_),
                        ArithmeticOperatorObjWellDefinedProofByDef::Sign(p),
                    ) => self.numeric_sign_wd(wd, &p.child_obj_well_defined, &position),
                    (
                        ArithmeticOperator::Floor(_),
                        ArithmeticOperatorObjWellDefinedProofByDef::Floor(p),
                    ) => self.numeric_rounding_wd(wd, &p.child_obj_well_defined, false, &position),
                    (
                        ArithmeticOperator::Ceil(_),
                        ArithmeticOperatorObjWellDefinedProofByDef::Ceil(p),
                    ) => self.numeric_rounding_wd(wd, &p.child_obj_well_defined, true, &position),
                    (
                        ArithmeticOperator::Max(_),
                        ArithmeticOperatorObjWellDefinedProofByDef::Max(p),
                    ) => self.numeric_min_max_wd(wd, &p.child_obj_well_defined, true, &position),
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
                obj: Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)),
                proof:
                    ObjWellDefinedProofByDef::ExpLogOperator(
                        ExpLogOperatorObjWellDefinedProofByDef::Sqrt(_),
                    ),
            } => self.numeric_sqrt_wd(wd, position),
            ObjWellDefinedProof::ByDef {
                obj: object @ Obj::FnObj(_),
                proof: ObjWellDefinedProofByDef::FnObj(_),
            } => {
                // Cartesian parameter inference already publishes the coordinate
                // object and its membership. Numeric observation consumes that
                // exact completed producer; endpoint WD is checked separately.
                if let Some(observation) = self.numeric_inferred_coordinate(object, position)? {
                    return Ok(observation);
                }
                let (call, output, member) =
                    self.numeric_function_output_wd(wd, position, Some("_litex_numeric_call"))?;
                let complex =
                    if numeric_refinement(&output).is_some() || output == StandardSet::NPos {
                        let member = format!(
                            "(show Litex.In _litex_numeric_call {} from {member})",
                            standard_term(&output)?
                        );
                        standard_inclusion_term(
                            &output,
                            &StandardSet::C,
                            "_litex_numeric_call",
                            &member,
                        )?
                    } else {
                        let (carrier, bridge) = match output {
                            StandardSet::N => ("N", Some("naturalToComplex")),
                            StandardSet::Z => ("Z", Some("integerToComplex")),
                            StandardSet::Q => ("Q", Some("rationalToComplex")),
                            StandardSet::R => ("R", Some("realToComplex")),
                            StandardSet::RPos => ("RPos", Some("positiveRealToComplex")),
                            StandardSet::C => ("C", None),
                            _ => {
                                return Err(LeanCompileError::unsupported(
                                    "Arithmetic/FunctionOutputCarrier",
                                ))
                            }
                        };
                        let member = format!(
                            "(show Litex.In _litex_numeric_call Litex.{carrier} from {member})"
                        );
                        match bridge {
                            Some(bridge) => {
                                format!("(Litex.{bridge} _litex_numeric_call {member})")
                            }
                            None => member,
                        }
                    };
                // Keep the original constructor and return law, sharing the
                // constructor locally instead of repeating its full WD term.
                let setup = format!(
                    "let _litex_numeric_call := {call};\nlet _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := {complex};"
                );
                Ok((
                    format!("({setup}\nLitex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member)"),
                    format!("({setup}\nLitex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member)"),
                    format!("({setup}\n_litex_numeric_member)"),
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
                    if let Ok((_, Some(set), _, member)) =
                        position.visible_parameter(*id, &self.runtime)
                    {
                        if let Some(member) =
                            self.parameter_complex_membership(obj, set, &member, position)?
                        {
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
                    &Obj::StandardSet(StandardSet::RPos),
                    &mut |result, producer| {
                        let (_, positive) = self.compile_verify(result, producer)?;
                        let term = self.compile_object_reference(obj, producer)?;
                        self.numeric_member(
                            obj,
                            &format!("(Litex.positiveRealToComplex {term} {positive})"),
                            producer,
                        )
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
        output_reference: Option<&str>,
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
        use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
        if application.body.len() == 1 {
            if let Some(
                FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set },
            ) = &proof.domain_fn_set
            {
                let call = self.compile_fn_obj_wd(application, proof, &constructor)?;
                // The constructor above replayed all original WD stages.
                // Its output law can refer to the local constructor binding.
                let output = self.compile_numeric_carrier(&fn_set.ret_set, &constructor)?;
                let member = self.compile_call_output_proof(
                    application,
                    proof,
                    output_reference.unwrap_or(&call),
                )?;
                return Ok((call, output, member));
            }
        }
        self.compile_fn_call_with_output(application, proof, &constructor)
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
                let (call, output, member) = self.numeric_function_output_wd(wd, position, None)?;
                if (numeric_refinement(&output).is_some() && output != StandardSet::CStar)
                    || output == StandardSet::NPos
                {
                    return standard_inclusion_term(&output, &StandardSet::R, &call, &member)
                        .map(Some);
                }
                Ok(match output {
                    StandardSet::N => Some(format!("(Litex.naturalToReal {call} {member})")),
                    StandardSet::Z => Some(format!("(Litex.integerToReal {call} {member})")),
                    StandardSet::Q => Some(format!("(Litex.rationalToReal {call} {member})")),
                    StandardSet::R => Some(member),
                    StandardSet::RPos => Some(format!("(Litex.inRPos_real {call} {member})")),
                    // A checked C return certifies a complex value only. Any
                    // later R assertion still needs its own source certificate.
                    _ => None,
                })
            }
            _ => Ok(None),
        }
    }
    fn parameter_complex_membership(
        &self,
        object: &Obj,
        carrier: &Obj,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        if let Obj::StandardSet(set) = carrier {
            if *set == StandardSet::NPos || numeric_refinement(set).is_some() {
                return standard_inclusion_term(
                    set,
                    &StandardSet::C,
                    &self.compile_object_reference(object, position)?,
                    member,
                )
                .map(Some);
            }
        }
        let bridge = match carrier {
            Obj::StandardSet(StandardSet::C) => return Ok(Some(member.to_string())),
            Obj::StandardSet(StandardSet::N) => "naturalToComplex",
            Obj::StandardSet(StandardSet::Z) => "integerToComplex",
            Obj::StandardSet(StandardSet::Q) => "rationalToComplex",
            Obj::StandardSet(StandardSet::R) => "realToComplex",
            Obj::StandardSet(StandardSet::RPos) => "positiveRealToComplex",
            _ => return Ok(None),
        };
        Ok(Some(format!(
            "(Litex.{bridge} {} {member})",
            self.compile_object_reference(object, position)?
        )))
    }
}
