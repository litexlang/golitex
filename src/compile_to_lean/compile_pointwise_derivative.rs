//! Replay the selected finite derivative tree using semantic calculus laws.
use super::compile_function_derivative::derivative_parts;
use super::compile_function_derivative_definition::validate_derivative_interior;
use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::pointwise_derivative::{
    DerivativeConclusionProof, DerivativeConstructorProof as C, DerivativeExpressionProof,
    PointInteriorProof, PointwiseDerivativeProof,
};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("PointwiseDerivative/{stage}"))
}
fn number(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(value.into())))
}
pub(super) fn names(
    p: &DerivativeExpressionProof,
) -> Result<(String, String, String, String), LeanCompileError> {
    let id = source_subject(&p.value_real)?.fact_id().value();
    Ok((
        format!("_derivative_raw_{id}"),
        format!("_derivative_value_{id}"),
        format!("_derivative_slope_{id}"),
        format!("_derivative_node_{id}"),
    ))
}
impl LitexToLeanCompiler {
    fn compile_cited_derivative_function_domain(
        &self,
        known: &AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
        target: &HasDerivativeAtFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::store_fact_and_infer::{InferAtomicFactResult, InferHasDerivativeAtFactResult};
        let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(given)) =
            self.resolve_fact(known.cite_fact_id, position)?
        else {
            return Err(invalid("OuterCandidateSource"));
        };
        let original =
            self.compile_function_raw_expression_bound(&given.function, position, &HashMap::new())?;
        let real = position
            .with_visible_inferred_subject_filter(&given.function, &mut |_, producer| {
                let mut cursor = Some(producer);
                while let Some(site) = cursor {
                    let rules = match site.owner {
                        SourceOwner::AtomicInference(
                            seed,
                            InferAtomicFactResult::HasDerivativeAtFact(rules),
                        ) if seed.fact_id() == known.cite_fact_id => Some(rules),
                        SourceOwner::PropInference(store)
                            if store.primary_fact_id() == known.cite_fact_id =>
                        {
                            match &store.infer {
                                Some(crate::store_fact_and_infer::InferResult::AtomicFact(
                                    InferAtomicFactResult::HasDerivativeAtFact(rules),
                                )) => Some(rules),
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    if let Some(rules) = rules {
                        let [InferHasDerivativeAtFactResult::Definition(inferred)] =
                            rules.as_slice()
                        else {
                            return Err(invalid("OuterCandidateInference"));
                        };
                        if inferred.source_fact_id != known.cite_fact_id {
                            return Err(invalid("OuterCandidateIdentity"));
                        }
                        let domain = inferred
                            .function_domain
                            .as_ref()
                            .ok_or_else(|| invalid("OuterCandidateDomainCapture"))?;
                        return self
                            .compile_real_function_domain(&given.function, domain, site)
                            .map(Some);
                    }
                    cursor = site.parent;
                }
                Ok(None)
            })?
            .ok_or_else(|| invalid("OuterCandidateDomainProducer"))?;
        if known.why_parameters_of_known_fact_are_equal_to_givens.len() != 3 {
            return Err(invalid("OuterCandidateMatchingArity"));
        }
        let query = EqualFact {
            fact_id: known.cite_fact_id,
            left: given.function,
            right: target.function.clone(),
            line_file: None,
        };
        let equal = self.compile_equality_search(
            &query,
            &known.why_parameters_of_known_fact_are_equal_to_givens[0],
            position,
        )?;
        let real = real.replace('\n', "\n  ");
        Ok(format!("(by\n  have _outer_original : Litex.RealFunctionValue M {original} := {real}\n  exact (congrArg (Litex.RealFunctionValue M) {equal}).mp _outer_original\n)"))
    }
    pub(super) fn compile_derivative_tree_membership(
        &self,
        obj: &Obj,
        proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(source_subject(proof)?,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==obj.ir()&&p.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("MembershipSubject"));
        }
        let (ty, term) =
            self.compile_verify(proof, &position.atomic_search_verify_prior(proof)?)?;
        Ok(format!(
            "  have h_{} : {ty} := {term}",
            source_subject(proof)?.fact_id().value()
        ))
    }
    pub(super) fn compile_derivative_tree(
        &self,
        p: &DerivativeExpressionProof,
        parameter: IdentifierId,
        point: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if !instantiated_object_matches(
            &p.expression,
            &p.value,
            &HashMap::from([(parameter, point.clone())]),
        ) {
            return Err(invalid("PointSubstitution"));
        }
        let (raw, value, slope, node) = names(p)?;
        let mut lines =
            vec![self.compile_derivative_tree_membership(&p.value, &p.value_real, position)?];
        let value_raw =
            self.compile_function_raw_expression_bound(&p.value, position, &HashMap::new())?;
        lines.push(format!("  let {value} : M.Value := {value_raw}"));
        let mut expected = number("0");
        let (raw_body, coefficient, step) = match &p.constructor {
            C::Constant => {
                if contains_parameter(&p.expression, parameter) {
                    return Err(invalid("ConstantParameter"));
                }
                (
                    value.clone(),
                    "M.number 0".into(),
                    format!(
                        "Litex.semanticDerivativeConstant {value} _derivative_real_point h_{}",
                        source_subject(&p.value_real)?.fact_id().value()
                    ),
                )
            }
            C::Variable => {
                if !matches!(&p.expression,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter)
                {
                    return Err(invalid("VariableSubject"));
                }
                expected = number("1");
                (
                    "M.number (_derivative_input : ℂ)".into(),
                    "M.number 1".into(),
                    "Litex.semanticDerivativeVariable _derivative_real_point".into(),
                )
            }
            C::Neg { argument } => {
                if !matches!(&p.expression,Obj::ArithmeticOperator(ArithmeticOperator::Neg(e)) if e.arg.ir()==argument.expression.ir())
                {
                    return Err(invalid("NegSubject"));
                }
                lines.extend(self.compile_derivative_tree(argument, parameter, point, position)?);
                let (a, _, da, ha) = names(argument)?;
                expected = Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                    arg: Box::new(argument.derivative.clone()),
                }));
                (
                    format!("M.negValue ({a} _derivative_input)"),
                    format!("M.negValue {da}"),
                    format!("Litex.semanticDerivativeNeg {a} _derivative_real_point {da} {ha}"),
                )
            }
            C::Add { left, right }
            | C::Sub { left, right }
            | C::Mul { left, right }
            | C::Div { left, right, .. } => {
                let (operation, law, actual_left, actual_right) =
                    match (&p.constructor, &p.expression) {
                        (C::Add { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Add(e))) => {
                            ("addValue", "Add", e.left.as_ref(), e.right.as_ref())
                        }
                        (C::Sub { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Sub(e))) => {
                            ("subValue", "Sub", e.left.as_ref(), e.right.as_ref())
                        }
                        (C::Mul { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Mul(e))) => {
                            ("mulValue", "Mul", e.left.as_ref(), e.right.as_ref())
                        }
                        (C::Div { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Div(e))) => {
                            ("divValue", "Div", e.left.as_ref(), e.right.as_ref())
                        }
                        _ => return Err(invalid("BinarySubject")),
                    };
                if actual_left.ir() != left.expression.ir()
                    || actual_right.ir() != right.expression.ir()
                {
                    return Err(invalid("BinaryChildren"));
                }
                lines.extend(self.compile_derivative_tree(left, parameter, point, position)?);
                lines.extend(self.compile_derivative_tree(right, parameter, point, position)?);
                let (a, av, da, ha) = names(left)?;
                let (b, bv, db, hb) = names(right)?;
                let coefficient = match &p.constructor {
                    C::Add { .. } => {
                        expected = add_objs(left.derivative.clone(), right.derivative.clone());
                        format!("M.addValue {da} {db}")
                    }
                    C::Sub { .. } => {
                        expected = sub_objs(left.derivative.clone(), right.derivative.clone());
                        format!("M.subValue {da} {db}")
                    }
                    C::Mul { .. } => {
                        expected = add_objs(
                            mul_objs(left.derivative.clone(), right.value.clone()),
                            mul_objs(left.value.clone(), right.derivative.clone()),
                        );
                        format!("M.addValue (M.mulValue {da} {bv}) (M.mulValue {av} {db})")
                    }
                    C::Div {
                        denominator_nonzero,
                        ..
                    } => {
                        if !matches!(source_subject(denominator_nonzero)?,Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir()==right.value.ir()&&is_zero(&f.right))
                        {
                            return Err(invalid("DenominatorSubject"));
                        }
                        let (ty, term) = self.compile_verify(
                            denominator_nonzero,
                            &position.atomic_search_verify_prior(denominator_nonzero)?,
                        )?;
                        lines.push(format!(
                            "  have h_{} : {ty} := {term}",
                            source_subject(denominator_nonzero)?.fact_id().value()
                        ));
                        expected = div_objs(
                            div_objs(
                                sub_objs(
                                    mul_objs(left.derivative.clone(), right.value.clone()),
                                    mul_objs(left.value.clone(), right.derivative.clone()),
                                ),
                                right.value.clone(),
                            ),
                            right.value.clone(),
                        );
                        format!("M.divValue (M.divValue (M.subValue (M.mulValue {da} {bv}) (M.mulValue {av} {db})) {bv}) {bv}")
                    }
                    _ => unreachable!(),
                };
                let (nonzero, rewrites) = if let C::Div {
                    denominator_nonzero,
                    ..
                } = &p.constructor
                {
                    (
                        format!(
                            " (by rw [_derivative_at_{}]; exact h_{})",
                            source_subject(&right.value_real)?.fact_id().value(),
                            source_subject(denominator_nonzero)?.fact_id().value()
                        ),
                        true,
                    )
                } else {
                    (String::new(), matches!(p.constructor, C::Mul { .. }))
                };
                let term=format!("Litex.semanticDerivative{law} {a} {b} _derivative_real_point {da} {db} {ha} {hb}{nonzero}");
                let step = if rewrites {
                    format!("(by\n    have _derivative_step := {term}\n    rw [_derivative_at_{}, _derivative_at_{}] at _derivative_step\n    exact _derivative_step\n  )",source_subject(&left.value_real)?.fact_id().value(),source_subject(&right.value_real)?.fact_id().value())
                } else {
                    term
                };
                (
                    format!("M.{operation} ({a} _derivative_input) ({b} _derivative_input)"),
                    coefficient,
                    step,
                )
            }
            C::Elementary {
                kind,
                argument,
                domain,
            } => {
                use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
                if p.expression.ir() != kind.apply(argument.expression.clone()).ir() {
                    return Err(invalid("ElementarySubject"));
                }
                lines.extend(self.compile_derivative_tree(argument, parameter, point, position)?);
                let positive = matches!(kind, K::Ln | K::Sqrt);
                let carrier = Obj::StandardSet(if positive {
                    StandardSet::RPos
                } else {
                    StandardSet::R
                });
                if !matches!(source_subject(domain)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==argument.value.ir()&&f.set==carrier)
                {
                    return Err(invalid("ElementaryDomain"));
                }
                let (ty, term) =
                    self.compile_verify(domain, &position.atomic_search_verify_prior(domain)?)?;
                let did = source_subject(domain)?.fact_id().value();
                lines.push(format!("  have h_{did} : {ty} := {term}"));
                let (a, av, da, ha) = names(argument)?;
                let (operation, law, factor) = match kind {
                    K::Exp => (
                        "(Litex.realUnaryValue (M := M) Real.exp)",
                        "Exp",
                        format!("(Litex.realUnaryValue (M := M) Real.exp {av})"),
                    ),
                    K::Sin => (
                        "(Litex.realUnaryValue (M := M) Real.sin)",
                        "Sin",
                        format!("(Litex.realUnaryValue (M := M) Real.cos {av})"),
                    ),
                    K::Cos => (
                        "(Litex.realUnaryValue (M := M) Real.cos)",
                        "Cos",
                        format!("(M.negValue (Litex.realUnaryValue (M := M) Real.sin {av}))"),
                    ),
                    K::Ln => (
                        "(Litex.realUnaryValue (M := M) Real.log)",
                        "Ln",
                        String::new(),
                    ),
                    K::Sqrt => ("(Litex.sqrtValue (M := M))", "Sqrt", String::new()),
                };
                let unit = matches!(&argument.derivative,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
                    && !positive;
                expected = kind.derivative(argument.value.clone(), argument.derivative.clone());
                let coefficient = match kind {
                    K::Ln => format!("M.divValue {da} {av}"),
                    K::Sqrt => {
                        format!("M.divValue (M.divValue {da} (M.number 2)) (Litex.sqrtValue {av})")
                    }
                    _ if unit => factor,
                    _ => format!("M.mulValue {factor} {da}"),
                };
                let aid = source_subject(&argument.value_real)?.fact_id().value();
                let positive_proof = if positive {
                    format!(" (by rw [_derivative_at_{aid}]; exact h_{did})")
                } else {
                    String::new()
                };
                let term=format!("Litex.semanticDerivative{law} {a} _derivative_real_point {da}{positive_proof} {ha}");
                let finish = if unit {
                    format!("exact Litex.semanticDerivativeDropUnit {raw} _derivative_real_point {slope} h_{} _derivative_step",source_subject(&p.derivative_real)?.fact_id().value())
                } else {
                    "exact _derivative_step".into()
                };
                let step=format!("(by\n    have _derivative_step := {term}\n    rw [_derivative_at_{aid}] at _derivative_step\n    {finish}\n  )");
                (
                    format!("{operation} ({a} _derivative_input)"),
                    coefficient,
                    step,
                )
            }
            C::NaturalPower {
                base,
                exponent_natural,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &p.expression else {
                    return Err(invalid("PowerSubject"));
                };
                if power.base.ir() != base.expression.ir()
                    || contains_parameter(&power.exponent, parameter)
                {
                    return Err(invalid("PowerBase"));
                }
                lines.extend(self.compile_derivative_tree(base, parameter, point, position)?);
                if !matches!(source_subject(exponent_natural)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==power.exponent.ir()&&f.set==Obj::StandardSet(StandardSet::N))
                {
                    return Err(invalid("PowerExponent"));
                }
                let exponent_position = position.atomic_search_verify_prior(exponent_natural)?;
                let (ty, term) = self.compile_verify(exponent_natural, &exponent_position)?;
                let eid = source_subject(exponent_natural)?.fact_id().value();
                lines.push(format!("  have h_{eid} : {ty} := {term}"));
                let exponent = self.compile_object_reference(&power.exponent, position)?;
                let exponent_raw = self.compile_function_raw_expression_bound(
                    &power.exponent,
                    position,
                    &HashMap::new(),
                )?;
                let (a, av, da, ha) = names(base)?;
                let index = sub_objs(
                    Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                        left: power.exponent.clone(),
                        right: Box::new(number("1")),
                    })),
                    number("1"),
                );
                expected = mul_objs(
                    mul_objs(
                        *power.exponent.clone(),
                        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                            base: Box::new(base.value.clone()),
                            exponent: Box::new(index),
                        })),
                    ),
                    base.derivative.clone(),
                );
                let term=format!("Litex.semanticDerivativePower {a} _derivative_real_point {da} {exponent_raw} (Litex.NativeBridge.asNat {exponent} h_{eid}) (Litex.NativeBridge.asNat_spec {exponent} h_{eid}) {ha}");
                (format!("M.powValue ({a} _derivative_input) {exponent_raw}"),format!("M.mulValue (M.mulValue {exponent_raw} (M.powValue {av} (Litex.derivativePowerIndexValue {exponent_raw}))) {da}"),format!("(by\n    have _derivative_step := {term}\n    rw [_derivative_at_{}] at _derivative_step\n    exact _derivative_step\n  )",source_subject(&base.value_real)?.fact_id().value()))
            }
            C::Compose {
                function,
                argument,
                outer,
            } => {
                use crate::execute::execute_fact_stmt::pointwise_derivative::DerivativeLeafProof;
                if contains_parameter(function, parameter)
                    || !super::compile_sequence_analysis::call_matches(
                        &p.expression,
                        function,
                        &argument.expression,
                    )
                {
                    return Err(invalid("CompositionSubject"));
                }
                lines.extend(self.compile_derivative_tree(argument, parameter, point, position)?);
                let (a, av, da, ha) = names(argument)?;
                let id = source_subject(&p.value_real)?.fact_id().value();
                let (outer_slope, outer_slope_raw, real, candidate) = match outer {
                    DerivativeLeafProof::Candidate(proof) => {
                        let AtomicFact::HasDerivativeAtFact(fact) = &proof.fact else {
                            return Err(invalid("OuterCandidateKind"));
                        };
                        if fact.function.ir() != function.ir()
                            || fact.point.ir() != argument.value.ir()
                        {
                            return Err(invalid("OuterCandidateSubject"));
                        }
                        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                            proof.searched_proof.as_ref()
                        else {
                            return Err(invalid("OuterCandidateCitation"));
                        };
                        let candidate = self.compile_known_atomic(known, &proof.fact, position)?;
                        let real =
                            self.compile_cited_derivative_function_domain(known, fact, position)?;
                        let raw = self.compile_function_raw_expression_bound(
                            &fact.value,
                            position,
                            &HashMap::new(),
                        )?;
                        (fact.value.clone(), raw, real, candidate)
                    }
                    DerivativeLeafProof::Selected {
                        differentiability,
                        value_well_defined,
                    } => {
                        if !matches!(source_subject(differentiability)?,Fact::AtomicFact(AtomicFact::FunctionDifferentiableAtFact(f)) if f.function.ir()==function.ir()&&f.point.ir()==argument.value.ir())
                        {
                            return Err(invalid("OuterDifferentiabilitySubject"));
                        }
                        let (ty, term) = self.compile_verify(
                            differentiability,
                            &position.atomic_search_verify_prior(differentiability)?,
                        )?;
                        lines.push(format!(
                            "  have h_{} : {ty} := {term}",
                            source_subject(differentiability)?.fact_id().value()
                        ));
                        let value: Obj =
                            DerivativeAt::new(function.clone(), argument.value.clone()).into();
                        ensure_object(&value, value_well_defined)?;
                        let term = self.compile_wd(
                            value_well_defined,
                            &position.atomic_search_wd_prior(value_well_defined)?,
                        )?;
                        let name = format!("_derivative_outer_{id}");
                        lines.push(format!("  let {name} := {term}"));
                        (
                            value,
                            format!("(Litex.denote {name})"),
                            format!("{name}.wd.1"),
                            format!("(Litex.derivativeSelectedCandidate {name})"),
                        )
                    }
                };
                expected = crate::execute::execute_fact_stmt::multiply_derivative_terms(
                    outer_slope.clone(),
                    argument.derivative.clone(),
                );
                let f = self.compile_function_raw_expression_bound(
                    function,
                    position,
                    &HashMap::new(),
                )?;
                let aid = source_subject(&argument.value_real)?.fact_id().value();
                let outer_node = format!("_derivative_outer_node_{id}");
                let real = real.replace('\n', "\n    ");
                let candidate = candidate.replace('\n', "\n    ");
                lines.push(format!("  have {outer_node} : Litex.SemanticDerivativeAtValue M (fun x : ℝ => Litex.FunctionSemantics.callValue {f} (M.number (x : ℂ))) (Litex.observeRealValue ({a} _derivative_real_point)) {outer_slope_raw} := Litex.semanticDerivativeOfCandidate {f} {av} {outer_slope_raw} (Litex.observeRealValue ({a} _derivative_real_point)) (_derivative_at_{aid}.symm.trans (Litex.semanticDerivativeValuePoint {a} _derivative_real_point {da} {ha})) {real} {candidate}"));
                let left_unit = matches!(&outer_slope,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1");
                let right_unit = matches!(&argument.derivative,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1");
                let coefficient = if left_unit {
                    da.clone()
                } else if right_unit {
                    outer_slope_raw.clone()
                } else {
                    format!("M.mulValue {outer_slope_raw} {da}")
                };
                let term=format!("Litex.semanticDerivativeCompose {a} {f} _derivative_real_point {da} {outer_slope_raw} {ha} {outer_node}");
                let step = if left_unit || right_unit {
                    format!("(Litex.semanticDerivativeDrop{}Unit {raw} _derivative_real_point {slope} h_{} ({term}))",if left_unit{"Left"}else{""},source_subject(&p.derivative_real)?.fact_id().value())
                } else {
                    term
                };
                (
                    format!("Litex.FunctionSemantics.callValue {f} ({a} _derivative_input)"),
                    coefficient,
                    step,
                )
            }
        };
        if p.derivative.ir() != expected.ir() {
            return Err(invalid("DerivativeFormula"));
        }
        lines.push(format!(
            "  let {raw} : ℝ → M.Value := fun (_derivative_input : ℝ) => {raw_body}"
        ));
        lines.push(format!("  let {slope} : M.Value := {coefficient}"));
        let value_id = |q: &DerivativeExpressionProof| {
            source_subject(&q.value_real).map(|f| format!("_derivative_at_{}", f.fact_id().value()))
        };
        let at = match &p.constructor {
            C::Constant => "rfl".to_owned(),
            C::Variable => "exact _derivative_point_value.symm".to_owned(),
            C::Neg { argument } => format!("exact congrArg M.negValue {}", value_id(argument)?),
            C::Add { left, right } => format!(
                "exact congrArg₂ M.addValue {} {}",
                value_id(left)?,
                value_id(right)?
            ),
            C::Sub { left, right } => format!(
                "exact congrArg₂ M.subValue {} {}",
                value_id(left)?,
                value_id(right)?
            ),
            C::Mul { left, right } => format!(
                "exact congrArg₂ M.mulValue {} {}",
                value_id(left)?,
                value_id(right)?
            ),
            C::Div { left, right, .. } => format!(
                "exact congrArg₂ M.divValue {} {}",
                value_id(left)?,
                value_id(right)?
            ),
            C::Elementary { kind, argument, .. } => {
                use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
                let operation = match kind {
                    K::Exp => "(Litex.realUnaryValue (M := M) Real.exp)",
                    K::Sin => "(Litex.realUnaryValue (M := M) Real.sin)",
                    K::Cos => "(Litex.realUnaryValue (M := M) Real.cos)",
                    K::Ln => "(Litex.realUnaryValue (M := M) Real.log)",
                    K::Sqrt => "(Litex.sqrtValue (M := M))",
                };
                format!("exact congrArg {operation} {}", value_id(argument)?)
            }
            C::NaturalPower { base, .. } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &p.expression else {
                    return Err(invalid("PowerPointValue"));
                };
                let exponent = self.compile_function_raw_expression_bound(
                    &power.exponent,
                    position,
                    &HashMap::new(),
                )?;
                format!(
                    "exact congrArg (fun value => M.powValue value {exponent}) {}",
                    value_id(base)?
                )
            }
            C::Compose {
                function, argument, ..
            } => {
                let f = self.compile_function_raw_expression_bound(
                    function,
                    position,
                    &HashMap::new(),
                )?;
                format!(
                    "exact congrArg (Litex.FunctionSemantics.callValue {f}) {}",
                    value_id(argument)?
                )
            }
        };
        lines.push(format!(
            "  have _derivative_at_{} : {raw} _derivative_real_point = {value} := by\n    {at}",
            source_subject(&p.value_real)?.fact_id().value()
        ));
        lines.push(self.compile_derivative_tree_membership(
            &p.derivative,
            &p.derivative_real,
            position,
        )?);
        lines.push(format!("  have {node} : Litex.SemanticDerivativeAtValue M {raw} _derivative_real_point {slope} := {step}"));
        Ok(lines)
    }
    pub(super) fn compile_pointwise_derivative(
        &self,
        goal: &AtomicFact,
        p: &PointwiseDerivativeProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (function, point, value, negative) =
            derivative_parts(goal).ok_or_else(|| invalid("Goal"))?;
        if negative
            || function.ir() != p.function.ir()
            || point.ir() != p.point.ir()
            || p.expression.expression.ir() != p.body.equal_to.ir()
            || !crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(
                &p.domain.source.signature,
                &p.body.body,
            )
        {
            return Err(invalid("Subject"));
        }
        let [group] = p.body.body.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("Signature"));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(invalid("Arity"));
        };
        let body_obj = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.body.clone()));
        ensure_object(&body_obj, &p.body_well_defined)?;
        let mut lines = Vec::new();
        for checked in [&p.domain.input_real, &p.domain.output_real] {
            let (ty, term) =
                self.compile_verify(checked, &position.atomic_search_verify_prior(checked)?)?;
            lines.push(format!(
                "  have h_{} : {ty} := {term}",
                source_subject(checked)?.fact_id().value()
            ));
        }
        self.compile_real_function_domain(function, &p.domain, position)?;
        let body = self.compile_wd(
            &p.body_well_defined,
            &position.atomic_search_wd_prior(&p.body_well_defined)?,
        )?;
        lines.push(format!("  let _derivative_literal := {body}"));
        let path = self.compile_equality_path(function, &body_obj, &p.body_equal, position)?;
        let f = self.compile_object_reference(function, position)?;
        let pt = self.compile_object_reference(point, position)?;
        let real = self.compile_real_membership_certificate(point, position)?;
        let (view, equal) =
            self.compile_function_limit_domain_view(function, &p.domain, position)?;
        lines.push(view);
        lines.push(format!("  have _derivative_point_real : Litex.In {pt} Litex.R := {real}\n  let _derivative_real_point := Litex.NativeBridge.asReal {pt} _derivative_point_real\n  have _derivative_point_value : Litex.denote {pt}=M.number (_derivative_real_point : ℂ) := Litex.NativeBridge.asReal_spec {pt} _derivative_point_real"));
        let interior = match &p.interior {
            PointInteriorProof::Known { condition, proof } => {
                validate_derivative_interior(function, point, &p.domain.domain, condition)?;
                if source_subject(proof)? != *condition {
                    return Err(invalid("InteriorProofSubject"));
                }
                let (ty, term) =
                    self.compile_verify(proof, &position.atomic_search_verify_prior(proof)?)?;
                format!("(by\n    unfold Litex.DerivativeInteriorClauseValue\n    have _derivative_domain_eq := {equal}\n    rw [← _derivative_domain_eq]\n    exact (show {ty} from {term})\n  )")
            }
            PointInteriorProof::StandardOpen {
                set,
                domain_equal,
                point_member,
            } => {
                if !matches!(source_subject(point_member)?,Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==point.ir()&&m.set.ir()==p.domain.domain.ir())
                {
                    return Err(invalid("InteriorMember"));
                }
                let (ty, term) = self.compile_verify(
                    point_member,
                    &position.atomic_search_verify_prior(point_member)?,
                )?;
                let query = EqualFact {
                    fact_id: goal.fact_id(),
                    left: p.domain.domain.clone(),
                    right: Obj::StandardSet(set.clone()),
                    line_file: None,
                };
                let domain_equal = self.compile_equality_search(&query, domain_equal, position)?;
                let carrier = self.compile_object_reference(&query.right, position)?;
                let open = match set {
                    StandardSet::R => "realDomainOpen",
                    StandardSet::RPos => "positiveRealDomainOpen",
                    StandardSet::RNeg => "negativeRealDomainOpen",
                    StandardSet::RStar => "nonzeroRealDomainOpen",
                    _ => return Err(invalid("OpenCarrier")),
                };
                format!("(by\n    have _point_member : {ty} := {term}\n    have _carrier_eq : _source_domain=Litex.denote {carrier} := {domain_equal}\n    have _carrier_open : IsOpen {{x : ℝ | M.mem (M.number (x : ℂ)) _source_domain}} := by\n      rw [_carrier_eq]\n      exact Litex.{open}\n    exact Litex.derivativeInteriorOfOpenDomain (Litex.denote {f}) (Litex.denote {pt}) _source_domain _derivative_real_point _derivative_point_value {equal} _point_member _carrier_open\n  )")
            }
            PointInteriorProof::Guarded { .. } => {
                let neighbourhood = self.compile_derivative_neighbourhood(
                    function,
                    &p.domain.domain,
                    point,
                    &p.interior,
                    position,
                    &mut lines,
                )?;
                format!("(by\n    have _source_neighbourhood : ∀ᶠ (x : ℝ) in nhds _derivative_real_point, M.mem (M.number (x : ℂ)) _source_domain := {neighbourhood}\n    have _function_neighbourhood : ∀ᶠ (x : ℝ) in nhds _derivative_real_point, M.mem (M.number (x : ℂ)) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := by\n      rw [← {equal}]\n      exact _source_neighbourhood\n    exact Litex.derivativeInteriorOfNeighborhood (Litex.denote {f}) (Litex.denote {pt}) _derivative_real_point _derivative_point_value _function_neighbourhood\n  )")
            }
        };
        lines.push(format!("  have _derivative_interior : Litex.DerivativeInteriorClauseValue M (Litex.denote {f}) (Litex.denote {pt}) := {interior}"));
        lines.extend(self.compile_derivative_tree(&p.expression, parameter.id, point, position)?);
        let (raw, _, slope, node) = names(&p.expression)?;
        lines.push(format!("  have _derivative_body_eq : Litex.Same {f} _derivative_literal := {path}\n  have _derivative_graph_domain : Litex.FunctionSemantics.domainValue (Litex.denote {f}) = _derivative_literal.val.signature.domain := by\n    rw [_derivative_body_eq]\n    exact Litex.FunctionSemantics.domainValue_eq _derivative_literal.val.signature.domain_isSet (Litex.formulaFnInFnSet _derivative_literal)\n  have _derivative_body : ∀ x : ℝ, M.mem (M.number (x : ℂ)) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) → Litex.FunctionSemantics.callValue (Litex.denote {f}) (M.number (x : ℂ))={raw} x := by\n    intro x hx\n    have _input := _derivative_graph_domain ▸ hx\n    exact (congrArg (fun g => Litex.FunctionSemantics.callValue g (M.number (x : ℂ))) _derivative_body_eq).trans (Litex.FunctionSemantics.call_graphValue _ _ _ _derivative_literal.wd _ _input)\n  have _derivative_candidate : Litex.HasDerivativeAtValue M (Litex.denote {f}) (Litex.denote {pt}) {slope} := Litex.derivativeOfSemanticFormula (Litex.denote {f}) (Litex.denote {pt}) {slope} _derivative_real_point {raw} _derivative_point_value _derivative_interior _derivative_body {node}"));
        match (&p.conclusion,value){
            (DerivativeConclusionProof::Candidate(checked),Some(value))=>{
                if !matches!(source_subject(checked)?,Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==p.expression.derivative.ir()&&eq.right.ir()==value.ir()){return Err(invalid("ConclusionEquality"));}
                let (ty,term)=self.compile_verify(checked,&position.atomic_search_verify_prior(checked)?)?;
                let result=self.compile_function_raw_expression_bound(value,position,&HashMap::new())?;
                lines.push(format!("  have _derivative_conclusion : {slope}={result} := (show {ty} from {term})\n  exact (congrArg (fun value => Litex.HasDerivativeAtValue M (Litex.denote {f}) (Litex.denote {pt}) value) _derivative_conclusion).mp _derivative_candidate"));
            },
            (DerivativeConclusionProof::Differentiable,None)=>lines.push(format!("  exact Litex.derivativeExistsValueOfCandidate (Litex.denote {f}) (Litex.denote {pt}) {slope} _derivative_candidate")),
            _=>return Err(invalid("ConclusionKind")),
        }
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}
