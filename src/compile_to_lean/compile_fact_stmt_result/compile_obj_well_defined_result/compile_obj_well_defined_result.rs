use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{arithmetic_stages, SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ComplexOperatorObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::HyperbolicOperatorObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::TrigOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_wd(
        &self,
        proof: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Some(term) = position.bound_wd_child(proof) {
            return Ok(term);
        }
        if let Some((children, _)) = arithmetic_stages(proof) {
            if children.iter().any(|child| {
                !matches!(
                    child.obj(),
                    Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
                )
            }) {
                let mut bindings = String::new();
                for (index, child) in children.iter().enumerate() {
                    let prior = SourcePosition::new(
                        Some(position),
                        SourceOwner::WDLocals(proof, index),
                        index,
                    );
                    let term = self.compile_wd(child, &prior)?;
                    bindings.push_str(&format!(
                        "let {} := {};\n",
                        prior.wd_child_name(index),
                        term
                    ));
                }
                let formed = SourcePosition::new(
                    Some(position),
                    SourceOwner::WDLocals(proof, children.len()),
                    0,
                );
                let term = self.compile_wd_body(proof, &formed)?;
                // Validate all stages above before reusing an earlier certified
                // host object. The alias belongs to the enclosing source prefix,
                // never to the temporary bindings being constructed here.
                return Ok(position
                    .compatible_wd_reference(proof)?
                    .unwrap_or_else(|| format!("({bindings}{term})")));
            }
        }
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::WD(proof),
            before: 0,
        };
        let term = self.compile_wd_body(proof, &source_position)?;
        if matches!(proof, ObjWellDefinedProof::ByDef { .. }) {
            if let Some(reference) = position.compatible_wd_reference(proof)? {
                return Ok(reference);
            }
        }
        Ok(term)
    }

    pub(in crate::compile_to_lean) fn compile_wd_requirement(
        &self,
        result: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Some(proof) = position.bound_wd_requirement(result) {
            return Ok(proof);
        }
        self.compile_verify(result, position)
            .map(|(_, proof)| proof)
    }

    fn compile_wd_body(
        &self,
        proof: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            ObjWellDefinedProof::ByKnown { obj, wd_id } => {
                let recorded = self.resolve_wd(*wd_id, position)?;
                if recorded.ir() != obj.ir() {
                    return Err(LeanCompileError::new(
                        "WD/ByKnown",
                        "WD id resolves to another object.",
                    ));
                }
                if let Some(number) = position.enumeration_literal(obj) {
                    return Ok(format!(
                        "(Litex.number (M := M) {})",
                        number_literal(number, "ℂ")?
                    ));
                }
                if let Some(term) = position.registered_wd_reference(obj, Some(*wd_id))? {
                    return Ok(term);
                }
                // A beta expansion can cite the cached anonymous body of its
                // original named declaration. That declaration already emitted
                // this certified object; share it without replacing the selected
                // call's argument, domain, or guard evidence.
                if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = obj {
                    let mut ancestor = Some(position);
                    while let Some(cursor) = ancestor {
                        if let SourceOwner::FunctionExpansion(expansion) = cursor.owner {
                            if let Obj::FnObj(application) = &expansion.application {
                                if let FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) =
                                    application.head.as_ref()
                                {
                                    if let Ok((declaration, producer, _)) =
                                        position.visible_function(id)
                                    {
                                        if &declaration.statement.equal_to_anonymous_fn == function
                                        {
                                            return Ok(self.context_application(
                                                &format!("_object_i{}", id.value()),
                                                &producer,
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                        ancestor = cursor.parent;
                    }
                }
                // A cache record is not a proof. Only an earlier replayed constructor
                // or an explicitly introduced certified parameter supplies this term.
                let term = self.compile_object_reference(obj, position)?;
                Ok(term)
            }
            ObjWellDefinedProof::ByDef { obj, proof } => {
                let term = match (obj, proof) {
                    (Obj::BoundOperator(object), ObjWellDefinedProofByDef::BoundOperator(evidence)) => self.compile_real_extremum_wd(object, evidence, position)?,
                    (Obj::IteratedOperator(object @ (IteratedOperator::SumOfFiniteSet(_) | IteratedOperator::ProductOfFiniteSet(_))), ObjWellDefinedProofByDef::IteratedOperator(evidence)) => self.compile_finite_aggregate_wd(object, evidence, position)?,
                    (Obj::IteratedOperator(IteratedOperator::Reduce(object)), ObjWellDefinedProofByDef::IteratedOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef::Reduce(evidence))) => self.compile_range_fold_wd(object, evidence, position)?,
                    (Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(object)), ObjWellDefinedProofByDef::IteratedOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef::FiniteSetReduce(evidence))) => self.compile_finite_fold_wd(object, evidence, position)?,
                    (Obj::IteratedOperator(object), ObjWellDefinedProofByDef::IteratedOperator(evidence)) => self.compile_range_aggregate_wd(object, evidence, position)?,
                    (Obj::FiniteSetStat(object), ObjWellDefinedProofByDef::FiniteSetStat(evidence)) => self.compile_finite_stat_wd(object, evidence, position)?,
                    (Obj::InstantiatedTemplateObj(instance), ObjWellDefinedProofByDef::InstantiatedTemplateObj(evidence)) => self.compile_template_wd(instance, evidence, position)?,
                    (Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(object)), ObjWellDefinedProofByDef::Structish(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef::FieldAccess(evidence))) => self.compile_struct_field_wd(object, evidence, position)?,
                    (Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(object)), ObjWellDefinedProofByDef::Structish(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef::StructObj(evidence))) => self.compile_struct_wd(object, evidence, position)?,
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
                    (
                        Obj::IntegerOperator(IntegerOperator::Factorial(x)),
                        ObjWellDefinedProofByDef::IntegerOperator(
                            IntegerOperatorObjWellDefinedProofByDef::Factorial(p),
                        ),
                    ) => self.compile_factorial_wd(
                        &x.arg,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        position,
                    )?,
                    (
                        Obj::Literal(Literal::ImaginaryUnit(_)),
                        ObjWellDefinedProofByDef::Literal(
                            LiteralObjWellDefinedProofByDef::ImaginaryUnit(_),
                        ),
                    ) => "(Litex.number (M := M) Complex.I)".into(),
                    (Obj::ComplexOperator(ComplexOperator::Conjugate(x)), ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::Conjugate(p))) => self.compile_complex_wd(&x.arg, "conj", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::ComplexOperator(ComplexOperator::RealPart(x)), ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::RealPart(p))) => self.compile_complex_wd(&x.arg, "re", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::ComplexOperator(ComplexOperator::ImaginaryPart(x)), ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::ImaginaryPart(p))) => self.compile_complex_wd(&x.arg, "img", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::ComplexOperator(ComplexOperator::ComplexAbs(x)), ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::ComplexAbs(p))) => self.compile_complex_wd(&x.arg, "complexAbs", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::MatrixOperator(operator), ObjWellDefinedProofByDef::MatrixOperator(proof)) => self.compile_matrix_operator_wd(operator, proof, position)?,
                    (Obj::HyperbolicOperator(HyperbolicOperator::Sinh(x)), ObjWellDefinedProofByDef::HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef::Sinh(p))) => self.compile_hyperbolic_wd(&x.arg, "Sinh", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::HyperbolicOperator(HyperbolicOperator::Cosh(x)), ObjWellDefinedProofByDef::HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef::Cosh(p))) => self.compile_hyperbolic_wd(&x.arg, "Cosh", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::HyperbolicOperator(HyperbolicOperator::Tanh(x)), ObjWellDefinedProofByDef::HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef::Tanh(p))) => self.compile_hyperbolic_wd(&x.arg, "Tanh", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::HyperbolicOperator(HyperbolicOperator::Coth(x)), ObjWellDefinedProofByDef::HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef::Coth(p))) => self.compile_hyperbolic_wd(&x.arg, "Coth", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::HyperbolicOperator(HyperbolicOperator::Sech(x)), ObjWellDefinedProofByDef::HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef::Sech(p))) => self.compile_hyperbolic_wd(&x.arg, "Sech", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::HyperbolicOperator(HyperbolicOperator::Csch(x)), ObjWellDefinedProofByDef::HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef::Csch(p))) => self.compile_hyperbolic_wd(&x.arg, "Csch", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Sin(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Sin(p))) => self.compile_trig_wd(&x.arg, "Sin", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Cos(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Cos(p))) => self.compile_trig_wd(&x.arg, "Cos", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Tan(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Tan(p))) => self.compile_trig_wd(&x.arg, "Tan", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Cot(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Cot(p))) => self.compile_trig_wd(&x.arg, "Cot", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Sec(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Sec(p))) => self.compile_trig_wd(&x.arg, "Sec", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Csc(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Csc(p))) => self.compile_trig_wd(&x.arg, "Csc", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Arcsin(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arcsin(p))) => self.compile_trig_wd(&x.arg, "Arcsin", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Arccos(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arccos(p))) => self.compile_trig_wd(&x.arg, "Arccos", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Arctan(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arctan(p))) => self.compile_trig_wd(&x.arg, "Arctan", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::TrigOperator(TrigOperator::Arccot(x)), ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arccot(p))) => self.compile_trig_wd(&x.arg, "Arccot", &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::Literal(Literal::EulerNumber(_)), ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::EulerNumber(_))) => "(Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ))".into(),
                    (Obj::Literal(Literal::Pi(_)), ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Pi(_))) => "(Litex.number (M := M) (Real.pi : ℂ))".into(),
                    (Obj::ExpLogOperator(ExpLogOperator::Exp(x)), ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Exp(p))) => self.compile_exp_ln_wd(&x.arg, false, &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::ExpLogOperator(ExpLogOperator::Ln(x)), ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Ln(p))) => self.compile_exp_ln_wd(&x.arg, true, &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::ExpLogOperator(ExpLogOperator::Log(x)), ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Log(p))) => self.compile_log_wd(x, &p.child_obj_well_defined, &p.requirement_fact_verified, position)?,
                    (Obj::StandardSet(set), ObjWellDefinedProofByDef::StandardSet(_)) => {
                        standard_term(set)?
                    }
                    (Obj::SetFormer(set), ObjWellDefinedProofByDef::SetFormer(proof)) => {
                        self.compile_set_former(set, proof, position)?
                    }
                    (Obj::ProductShape(shape), ObjWellDefinedProofByDef::ProductShape(proof)) => {
                        self.compile_product_shape_wd(shape, proof, position)?
                    }
                    (Obj::SetOperator(operator), ObjWellDefinedProofByDef::SetOperator(proof)) => {
                        self.compile_set_operator_wd(operator, proof, position)?
                    }
                    (Obj::FunctionSpace(space), ObjWellDefinedProofByDef::FunctionSpace(proof)) => {
                        self.compile_function_space_wd(space, proof, position)?
                    }
                    (Obj::FnObj(application), ObjWellDefinedProofByDef::FnObj(proof)) => {
                        self.compile_fn_obj_wd(application, proof, position)?
                    }
                    (
                        Obj::ExpLogOperator(ExpLogOperator::Sqrt(value)),
                        ObjWellDefinedProofByDef::ExpLogOperator(
                            ExpLogOperatorObjWellDefinedProofByDef::Sqrt(proof),
                        ),
                    ) => self.compile_sqrt_wd(
                        &value.arg,
                        &proof.child_obj_well_defined,
                        &proof.requirement_fact_verified,
                        position,
                    )?,
                    (
                        Obj::IntegerOperator(IntegerOperator::Gcd(x)),
                        ObjWellDefinedProofByDef::IntegerOperator(
                            IntegerOperatorObjWellDefinedProofByDef::Gcd(p),
                        ),
                    ) => self.compile_gcd_lcm_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        false,
                        position,
                    )?,
                    (
                        Obj::IntegerOperator(IntegerOperator::Lcm(x)),
                        ObjWellDefinedProofByDef::IntegerOperator(
                            IntegerOperatorObjWellDefinedProofByDef::Lcm(p),
                        ),
                    ) => self.compile_gcd_lcm_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        true,
                        position,
                    )?,
                    (
                        Obj::IntegerOperator(IntegerOperator::Mod(x)),
                        ObjWellDefinedProofByDef::IntegerOperator(
                            IntegerOperatorObjWellDefinedProofByDef::Mod(p),
                        ),
                    ) => self.compile_integer_division_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        false,
                        position,
                    )?,
                    (
                        Obj::IntegerOperator(IntegerOperator::Quot(x)),
                        ObjWellDefinedProofByDef::IntegerOperator(
                            IntegerOperatorObjWellDefinedProofByDef::Quot(p),
                        ),
                    ) => self.compile_integer_division_wd(
                        &x.left,
                        &x.right,
                        &p.child_obj_well_defined,
                        &p.requirement_fact_verified,
                        true,
                        position,
                    )?,
                    (
                        Obj::ArithmeticOperator(operator),
                        ObjWellDefinedProofByDef::ArithmeticOperator(wd),
                    ) => {
                        let term = match (operator, wd) {
                            (
                                ArithmeticOperator::Floor(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Floor(p),
                            ) => self.compile_rounding_wd(
                                &x.arg,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                false,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Ceil(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Ceil(p),
                            ) => self.compile_rounding_wd(
                                &x.arg,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                true,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Sign(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Sign(p),
                            ) => self.compile_sign_wd(
                                &x.arg,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Min(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Min(p),
                            ) => self.compile_min_max_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                false,
                                position,
                            )?,
                            (
                                ArithmeticOperator::Max(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Max(p),
                            ) => self.compile_min_max_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                true,
                                position,
                            )?,
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
                                ArithmeticOperator::Abs(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Abs(p),
                            ) => self.compile_abs_wd(
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
        self.compile_atomic_wd_locals(wd, fact, position)
            .map(|_| ())
    }

    /// Consume every original WD stage once, retaining its constructor term
    /// for the proposition and selected proof that follow this formation.
    pub(in crate::compile_to_lean) fn compile_atomic_wd_locals(
        &self,
        wd: &AtomicFactWellDefinedProof,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::AtomicWDLocals(wd, 0),
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
        let mut bindings = Vec::new();
        for (index, (arg, proof)) in args
            .iter()
            .zip(&wd.well_defined_of_each_parameter)
            .enumerate()
        {
            ensure_object(arg, proof)?;
            let prior = SourcePosition {
                owner: SourceOwner::AtomicWDLocals(wd, index),
                before: index,
                ..*position
            };
            let mut term = self.compile_wd(proof, &prior)?;
            // Keep a compatible earlier call's host representation after this
            // occurrence's complete signature/domain evidence was consumed.
            if let ObjWellDefinedProof::ByDef {
                obj: Obj::FnObj(application),
                proof: ObjWellDefinedProofByDef::FnObj(call),
            } = proof
            {
                if let Some(alias) = prior.bound_compatible_fn_call(application, call) {
                    term = alias;
                }
            }
            if !matches!(
                arg,
                Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
            ) {
                bindings.push(format!(
                    "let {} := {term}",
                    prior.atomic_wd_child_name(index)
                ));
            }
        }
        let formed = SourcePosition {
            owner: SourceOwner::AtomicWDLocals(wd, args.len()),
            before: args.len(),
            ..*position
        };
        let position = &formed;
        match &wd.predicate_signature {
            PredicateSignatureWellDefinedProof::Builtin => {
                let certificate = match fact {
                    AtomicFact::NormalAtomicFact(f) => Some(&f.predicate),
                    AtomicFact::NotNormalAtomicFact(f) => Some(&f.predicate),
                    _ => None,
                };
                let supported_certificate = certificate.is_some_and(|name| {
                    crate::compile_to_lean::compile_real_extrema::certificate_name(name).is_some()
                        && args.len() == 2
                });
                if !supported_certificate
                    && certificate.is_some_and(|name| {
                        crate::builtin_theorem::builtin_certificate_arity(name.local_name())
                            .is_some()
                    })
                {
                    return Err(LeanCompileError::unsupported("Prop/RealBoundCertificate"));
                }
                if !supported_certificate
                    && matches!(
                        fact,
                        AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_)
                    )
                {
                    return Err(LeanCompileError::new(
                        "Prop/SignatureFamily",
                        "A concrete source predicate cannot use a builtin predicate signature.",
                    ));
                }
            }
            signature @ PredicateSignatureWellDefinedProof::Prop { .. } => {
                self.validate_prop_predicate_signature(signature, fact, position)?;
            }
            signature @ PredicateSignatureWellDefinedProof::AbstractProp { .. } => {
                self.validate_abstract_predicate_signature(signature, fact, position)?;
            }
        }
        match &wd.predicate_domain {
            PredicateDomainProof::MultivariableAnalysis(_) => {
                return Err(LeanCompileError::unsupported(
                    "WD/MultivariableAnalysisPredicate",
                ))
            }
            PredicateDomainProof::SequenceAnalysis(p) => {
                bindings.push(self.compile_sequence_analysis_domain(
                    fact,
                    &p.sequence_source,
                    &SourcePosition {
                        before: args.len(),
                        ..*position
                    },
                )?);
            }
            PredicateDomainProof::FunctionAnalysis(_) => {
                return Err(LeanCompileError::unsupported("WD/RealAnalysisPredicate"))
            }
            PredicateDomainProof::FunctionLimit(_) => {
                return Err(LeanCompileError::unsupported("WD/FunctionLimitPredicate"))
            }
            PredicateDomainProof::SequenceLimit(p) => {
                let (_, value, _) =
                    crate::compile_to_lean::compile_sequence_epsilon::limit_parts(fact)
                        .ok_or_else(|| {
                            LeanCompileError::unsupported("SequenceLimit/DomainSubject")
                        })?;
                if p.value_real.element.ir() != value.ir() || p.value_real.set != StandardSet::R {
                    return Err(LeanCompileError::unsupported("SequenceLimit/RealValue"));
                }
                let formed = SourcePosition {
                    before: args.len(),
                    ..*position
                };
                bindings.push(self.compile_sequence_analysis_domain(
                    fact,
                    &p.sequence_source,
                    &formed,
                )?);
                let real = self.compile_structural(&p.value_real, &formed)?;
                bindings.push(format!(
                    "have _sequence_limit_real : Litex.In {} (Litex.R (M := M)) := {real}",
                    self.compile_object_reference(value, &formed)?
                ));
            }
            PredicateDomainProof::ByKnownZeroRemainder(p) => {
                self.compile_known_dvd_zero(fact, p, position)?;
            }
            PredicateDomainProof::ByCheckedArguments(requirements) => {
                let numeric_domains =
                    crate::compile_to_lean::compile_basic_predicates::numeric_predicate_domains(
                        fact,
                    );
                if numeric_domains.is_none()
                    && !matches!(
                        fact,
                        AtomicFact::LessFact(_)
                            | AtomicFact::GreaterFact(_)
                            | AtomicFact::LessEqualFact(_)
                            | AtomicFact::GreaterEqualFact(_)
                            | AtomicFact::NotLessFact(_)
                            | AtomicFact::NotGreaterFact(_)
                            | AtomicFact::NotLessEqualFact(_)
                            | AtomicFact::NotGreaterEqualFact(_)
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "WD/CheckedArgumentPredicateDomain",
                    ));
                }
                if requirements.len() != args.len() {
                    return Err(LeanCompileError::new(
                        "WD/OrderRealDomain",
                        "Checked argument domains have another arity.",
                    ));
                }
                let carriers = numeric_domains.unwrap_or_else(|| vec![StandardSet::R; args.len()]);
                for (index, requirement) in requirements.iter().enumerate() {
                    let carrier = &carriers[index];
                    if requirement.argument_index != index
                        || !matches!(&requirement.requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == *args[index] && f.set == Obj::StandardSet(carrier.clone()))
                        || requirement.membership.element != *args[index]
                        || &requirement.membership.set != carrier
                    {
                        return Err(LeanCompileError::new(
                            "WD/OrderRealDomain",
                            "Checked argument membership has another subject, carrier or position.",
                        ));
                    }
                    self.compile_structural(
                        &requirement.membership,
                        &SourcePosition {
                            before: args.len() + index,
                            ..*position
                        },
                    )?;
                }
            }
            PredicateDomainProof::ByRequirements(requirements) => {
                if let Some(carriers) =
                    crate::compile_to_lean::compile_basic_predicates::numeric_predicate_domains(
                        fact,
                    )
                {
                    if requirements.len() != carriers.len() || requirements.iter().zip(args.iter().zip(carriers)).any(|(r,(arg,carrier))| !matches!(&r.requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == arg.ir() && f.set == Obj::StandardSet(carrier))) {
                        return Err(LeanCompileError::unsupported("WD/NumberPredicateDomain"));
                    }
                }
                self.validate_real_bound_domain(
                    fact,
                    &requirements
                        .iter()
                        .map(|r| &r.requirement)
                        .collect::<Vec<_>>(),
                )?;
                self.validate_mapping_domain(
                    fact,
                    &requirements
                        .iter()
                        .map(|r| &r.requirement)
                        .collect::<Vec<_>>(),
                )?;
                if matches!(
                    fact,
                    AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_)
                ) && !requirements.is_empty()
                {
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
        Ok(bindings)
    }

    /// Render a goal from its original formation without discarding and then
    /// rebuilding the same endpoint constructors.
    pub(in crate::compile_to_lean) fn compile_formed_fact_proposition(
        &self,
        wd: &FactWellDefinedProof,
        fact: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (wd, fact) {
            (FactWellDefinedProof::ForallFact(proof), Fact::ForallFact(fact)) => {
                self.compile_forall_formation(fact, proof, position)
            }
            (FactWellDefinedProof::ForallFactWithIff(proof), Fact::ForallFactWithIff(fact)) => {
                self.compile_forall_iff_formation(fact, proof, position)
            }
            (FactWellDefinedProof::Equality(wd), Fact::AtomicFact(AtomicFact::EqualFact(fact))) => {
                let bindings = self.compile_equal_wd_locals(fact, wd, position)?;
                let formed =
                    SourcePosition::new(Some(position), SourceOwner::EqualWDLocals(wd, 2), 2);
                Ok(Self::scope_equal_wd(
                    format!(
                        "Litex.Same {} {}",
                        self.compile_object_reference(&fact.left, &formed)?,
                        self.compile_object_reference(&fact.right, &formed)?
                    ),
                    &bindings,
                ))
            }
            (FactWellDefinedProof::AtomicExceptEquality(wd), Fact::AtomicFact(atomic)) => {
                let bindings = self.compile_atomic_wd_locals(wd, atomic, position)?;
                let formed = SourcePosition::new(
                    Some(position),
                    SourceOwner::AtomicWDLocals(wd, wd.well_defined_of_each_parameter.len()),
                    usize::MAX,
                );
                Ok(Self::scope_equal_wd(
                    self.atomic_proposition(atomic, &formed)?,
                    &bindings,
                ))
            }
            _ => {
                self.compile_fact_wd(wd, fact, position)?;
                let formed =
                    SourcePosition::new(Some(position), SourceOwner::FactWD(wd), usize::MAX);
                self.fact_proposition(fact, &formed)
            }
        }
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
            (FactWellDefinedProof::NotForall(proof), Fact::NotForall(fact)) => {
                self.compile_not_forall_wd(fact, proof, position)
            }
            (FactWellDefinedProof::ForallFactWithIff(proof), Fact::ForallFactWithIff(fact)) => self
                .compile_forall_iff_formation(fact, proof, position)
                .map(|_| ()),
            (FactWellDefinedProof::ForallFact(_), _) => Err(LeanCompileError::new(
                "WD/ForallSubject",
                "Quantified WD evidence has another source fact family.",
            )),
            (FactWellDefinedProof::AndFact { components }, Fact::AndFact(fact)) => {
                if components.len() != fact.facts.len() || components.is_empty() {
                    return Err(LeanCompileError::unsupported("WD/AndArity"));
                }
                for (index, (wd, atomic)) in components.iter().zip(&fact.facts).enumerate() {
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    self.compile_atomic_wd(wd, atomic, &prior)?;
                }
                Ok(())
            }
            (FactWellDefinedProof::ChainFact { adjacent }, Fact::ChainFact(fact)) => {
                if adjacent.len() != fact.prop_names.len() || adjacent.is_empty() {
                    return Err(LeanCompileError::unsupported("WD/ChainArity"));
                }
                for (index, wd) in adjacent.iter().enumerate() {
                    let atomic = crate::compile_to_lean::compile_compound_fact::chain_edge(
                        fact,
                        index,
                        fact.fact_id,
                    )?;
                    let prior = SourcePosition {
                        before: index,
                        ..*position
                    };
                    self.compile_atomic_wd(wd, &atomic, &prior)?;
                }
                Ok(())
            }
            (
                FactWellDefinedProof::ExistFact(proof),
                Fact::ExistFact(fact) | Fact::NotExistFact(fact) | Fact::ExistUniqueFact(fact),
            ) => self
                .compile_exist_formation(fact, proof, position)
                .map(|_| ()),
            (
                FactWellDefinedProof::AndFact { .. }
                | FactWellDefinedProof::ChainFact { .. }
                | FactWellDefinedProof::ExistFact(_)
                | FactWellDefinedProof::ForallFactWithIff(_)
                | FactWellDefinedProof::NotForall(_),
                _,
            ) => Err(LeanCompileError::unsupported("WD/CompoundFact")),
            (FactWellDefinedProof::OrFact(proof), Fact::OrFact(fact)) => {
                self.compile_or_wd(fact, proof, position)
            }
            (FactWellDefinedProof::OrFact(_), _) => {
                Err(LeanCompileError::unsupported("WD/OrSubject"))
            }
        }
    }

    // The goal's WD scope predates the named theorem's separate truth scope.
    // Its actual parameter/domain producers cannot be replaced by body IDs.
}
