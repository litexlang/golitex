//! Consume the original neighbourhood certificates for classical derivatives.
use super::compile_function_derivative_definition::validate_derivative_interior;
use super::compile_pointwise_derivative::names;
use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::pointwise_continuity::{
    PointwiseContinuityConstructorProof as C, PointwiseContinuityExpressionProof,
};
use crate::execute::execute_fact_stmt::pointwise_derivative::{
    InteriorOperandProof, PointInteriorProof,
};
use crate::prelude::*;
use std::collections::HashMap;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DerivativeInterior/{stage}"))
}
fn continuity_names(
    p: &PointwiseContinuityExpressionProof,
) -> Result<(String, String, String), LeanCompileError> {
    let id = source_subject(&p.value_real)?.fact_id().value();
    Ok((
        format!("_interior_raw_{id}"),
        format!("_interior_at_{id}"),
        format!("_interior_continuous_{id}"),
    ))
}
impl LitexToLeanCompiler {
    fn compile_interior_continuity(
        &self,
        p: &PointwiseContinuityExpressionProof,
        parameter: IdentifierId,
        point: &Obj,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
    ) -> Result<(String, String, String), LeanCompileError> {
        if !instantiated_object_matches(
            &p.expression,
            &p.value,
            &HashMap::from([(parameter, point.clone())]),
        ) {
            return Err(invalid("PointSubstitution"));
        }
        lines.push(self.compile_derivative_tree_membership(&p.value, &p.value_real, position)?);
        let (raw, at, node) = continuity_names(p)?;
        let val =
            self.compile_function_raw_expression_bound(&p.value, position, &HashMap::new())?;
        let (body, point_equal, step) = match &p.constructor {
            C::Constant => {
                if contains_parameter(&p.expression, parameter) {
                    return Err(invalid("ConstantParameter"));
                }
                (
                    val.clone(),
                    "rfl".into(),
                    format!(
                        "Litex.semanticContinuousConstant {val} _derivative_real_point h_{}",
                        source_subject(&p.value_real)?.fact_id().value()
                    ),
                )
            }
            C::Variable => {
                if !matches!(&p.expression,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter)
                {
                    return Err(invalid("VariableSubject"));
                }
                (
                    "(M.number (_interior_input : ℂ))".into(),
                    "exact _derivative_point_value.symm".into(),
                    "Litex.semanticContinuousVariable _derivative_real_point".into(),
                )
            }
            C::Neg { argument } | C::Abs { argument } => {
                let (operation, law) = match (&p.constructor, &p.expression) {
                    (C::Neg { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Neg(e)))
                        if e.arg.ir() == argument.expression.ir() =>
                    {
                        ("M.negValue", "Neg")
                    }
                    (C::Abs { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Abs(e)))
                        if e.arg.ir() == argument.expression.ir() =>
                    {
                        ("Litex.absValue", "Abs")
                    }
                    _ => return Err(invalid("UnarySubject")),
                };
                let (a, aa, ha) =
                    self.compile_interior_continuity(argument, parameter, point, position, lines)?;
                (
                    format!("{operation} ({a} _interior_input)"),
                    format!("exact congrArg {operation} {aa}"),
                    format!("Litex.semanticContinuous{law} {a} _derivative_real_point {ha}"),
                )
            }
            C::Add { left, right }
            | C::Sub { left, right }
            | C::Mul { left, right }
            | C::Div { left, right, .. } => {
                let (operation, law, a, b) = match (&p.constructor, &p.expression) {
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
                if a.ir() != left.expression.ir() || b.ir() != right.expression.ir() {
                    return Err(invalid("BinaryChildren"));
                }
                let (a, aa, ha) =
                    self.compile_interior_continuity(left, parameter, point, position, lines)?;
                let (b, ba, hb) =
                    self.compile_interior_continuity(right, parameter, point, position, lines)?;
                let nonzero = if let C::Div {
                    denominator_nonzero,
                    ..
                } = &p.constructor
                {
                    if !matches!(source_subject(denominator_nonzero)?,Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir()==right.value.ir()&&matches!(&f.right,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0"))
                    {
                        return Err(invalid("DenominatorSubject"));
                    }
                    let (ty, term) = self.compile_verify(
                        denominator_nonzero,
                        &position.atomic_search_verify_prior(denominator_nonzero)?,
                    )?;
                    format!(" (by rw [{ba}]; exact (show {ty} from {term}))")
                } else {
                    String::new()
                };
                (format!("M.{operation} ({a} _interior_input) ({b} _interior_input)"),format!("exact congrArg₂ M.{operation} {aa} {ba}"),format!("Litex.semanticContinuous{law} {a} {b} _derivative_real_point {ha} {hb}{nonzero}"))
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
                    return Err(invalid("PowerChildren"));
                }
                if !matches!(source_subject(exponent_natural)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==power.exponent.ir()&&f.set==Obj::StandardSet(StandardSet::N))
                {
                    return Err(invalid("PowerExponent"));
                }
                let (a, aa, ha) =
                    self.compile_interior_continuity(base, parameter, point, position, lines)?;
                let (ty, term) = self.compile_verify(
                    exponent_natural,
                    &position.atomic_search_verify_prior(exponent_natural)?,
                )?;
                let eid = source_subject(exponent_natural)?.fact_id().value();
                lines.push(format!("  have h_{eid} : {ty} := {term}"));
                let exponent = self.compile_object_reference(&power.exponent, position)?;
                let raw_exponent = self.compile_function_raw_expression_bound(
                    &power.exponent,
                    position,
                    &HashMap::new(),
                )?;
                (format!("M.powValue ({a} _interior_input) {raw_exponent}"),format!("exact congrArg (fun value => M.powValue value {raw_exponent}) {aa}"),format!("Litex.semanticContinuousPower {a} _derivative_real_point {raw_exponent} (Litex.NativeBridge.asNat {exponent} h_{eid}) (Litex.NativeBridge.asNat_spec {exponent} h_{eid}) {ha}"))
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
                let valid = match kind {
                    K::Sqrt => {
                        matches!(source_subject(domain)?,Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.right.ir()==argument.value.ir()&&matches!(&f.left,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0"))
                    }
                    _ => {
                        matches!(source_subject(domain)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==argument.value.ir()&&f.set==Obj::StandardSet(if *kind==K::Ln{StandardSet::RPos}else{StandardSet::R}))
                    }
                };
                if !valid {
                    return Err(invalid("ElementaryDomain"));
                }
                let (a, aa, ha) =
                    self.compile_interior_continuity(argument, parameter, point, position, lines)?;
                let (ty, term) =
                    self.compile_verify(domain, &position.atomic_search_verify_prior(domain)?)?;
                let did = source_subject(domain)?.fact_id().value();
                lines.push(format!("  have h_{did} : {ty} := {term}"));
                let (operation, law) = match kind {
                    K::Exp => ("(Litex.realUnaryValue (M := M) Real.exp)", "Exp"),
                    K::Ln => ("(Litex.realUnaryValue (M := M) Real.log)", "Ln"),
                    K::Sin => ("(Litex.realUnaryValue (M := M) Real.sin)", "Sin"),
                    K::Cos => ("(Litex.realUnaryValue (M := M) Real.cos)", "Cos"),
                    K::Sqrt => ("(Litex.sqrtValue (M := M))", "Sqrt"),
                };
                let positive = if *kind == K::Ln {
                    format!(" (by rw [{aa}]; exact h_{did})")
                } else {
                    String::new()
                };
                (
                    format!("{operation} ({a} _interior_input)"),
                    format!("exact congrArg {operation} {aa}"),
                    format!(
                        "Litex.semanticContinuous{law} {a} _derivative_real_point{positive} {ha}"
                    ),
                )
            }
            C::Leaf { .. } | C::Compose { .. } => {
                return Err(invalid("RelativeContinuityNeedsNeighbourhood"))
            }
        };
        lines.push(format!(
            "  let {raw} : ℝ → M.Value := fun (_interior_input : ℝ) => {body}"
        ));
        lines.push(format!(
            "  have {at} : {raw} _derivative_real_point={val} := by\n    {point_equal}"
        ));
        lines.push(format!("  have {node} : Litex.SemanticContinuousAtValue M {raw} _derivative_real_point := {step}"));
        Ok((raw, at, node))
    }
    pub(super) fn compile_derivative_neighbourhood(
        &self,
        function: &Obj,
        domain: &Obj,
        point: &Obj,
        proof: &PointInteriorProof,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
    ) -> Result<String, LeanCompileError> {
        let raw_domain =
            self.compile_function_raw_expression_bound(domain, position, &HashMap::new())?;
        let pt = self.compile_object_reference(point, position)?;
        match proof {
            PointInteriorProof::Known { condition, proof } => {
                validate_derivative_interior(function, point, domain, condition)?;
                if source_subject(proof)? != *condition {
                    return Err(invalid("KnownSubject"));
                }
                let (ty, term) =
                    self.compile_verify(proof, &position.atomic_search_verify_prior(proof)?)?;
                Ok(format!("Litex.realNeighborhoodOfInteriorClause {raw_domain} (Litex.denote {pt}) _derivative_real_point _derivative_point_value (show {ty} from {term})"))
            }
            PointInteriorProof::StandardOpen {
                set,
                domain_equal,
                point_member,
            } => {
                if !matches!(source_subject(point_member)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==point.ir()&&f.set.ir()==domain.ir())
                {
                    return Err(invalid("OpenPointMember"));
                }
                let (ty, term) = self.compile_verify(
                    point_member,
                    &position.atomic_search_verify_prior(point_member)?,
                )?;
                let query = EqualFact {
                    fact_id: source_subject(point_member)?.fact_id(),
                    left: domain.clone(),
                    right: Obj::StandardSet(set.clone()),
                    line_file: None,
                };
                let equal = self.compile_equality_search(&query, domain_equal, position)?;
                let carrier = self.compile_object_reference(&query.right, position)?;
                let law = match set {
                    StandardSet::R => "realDomainOpen",
                    StandardSet::RPos => "positiveRealDomainOpen",
                    StandardSet::RNeg => "negativeRealDomainOpen",
                    StandardSet::RStar => "nonzeroRealDomainOpen",
                    _ => return Err(invalid("OpenCarrier")),
                };
                Ok(format!("(by\n    have _member : {ty} := {term}\n    have _equal : {raw_domain}=Litex.denote {carrier} := {equal}\n    have _open : IsOpen {{x : ℝ | M.mem (M.number (x : ℂ)) {raw_domain}}} := by\n      rw [_equal]\n      exact Litex.{law}\n    have _point : M.mem (M.number (_derivative_real_point : ℂ)) {raw_domain} := by\n      rw [← _derivative_point_value]\n      exact _member\n    exact _open.mem_nhds _point\n  )"))
            }
            PointInteriorProof::Guarded {
                base,
                point_member,
                guards,
            } => {
                let Obj::SetFormer(SetFormer::SetBuilder(builder)) = domain else {
                    return Err(invalid("GuardedDomain"));
                };
                if guards.len() != builder.facts.len() {
                    return Err(invalid("GuardCount"));
                }
                let base_term = self.compile_derivative_neighbourhood(
                    function,
                    &builder.param_set,
                    point,
                    base,
                    position,
                    lines,
                )?;
                if !matches!(source_subject(point_member)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==point.ir()&&f.set.ir()==domain.ir())
                {
                    return Err(invalid("GuardedPointMember"));
                }
                let (ty, term) = self.compile_verify(
                    point_member,
                    &position.atomic_search_verify_prior(point_member)?,
                )?;
                let id = source_subject(point_member)?.fact_id().value();
                lines.push(format!("  have h_{id} : {ty} := {term}"));
                let base_name = format!("_interior_base_{id}");
                let base_raw = self.compile_function_raw_expression_bound(
                    &builder.param_set,
                    position,
                    &HashMap::new(),
                )?;
                lines.push(format!("  have {base_name} : ∀ᶠ (x : ℝ) in nhds _derivative_real_point, M.mem (M.number (x : ℂ)) {base_raw} := {base_term}"));
                let mut events = Vec::new();
                for (guard, expected) in guards.iter().zip(&builder.facts) {
                    if !matches!(expected,QuantifierFreeFact::AtomicFact(f) if *f==guard.guard) {
                        return Err(invalid("GuardSubject"));
                    }
                    let mut strict = guard.guard.clone();
                    strict = match strict {
                        AtomicFact::LessEqualFact(f) => LessFact {
                            fact_id: f.fact_id,
                            left: f.left,
                            right: f.right,
                            line_file: f.line_file,
                        }
                        .into(),
                        AtomicFact::GreaterEqualFact(f) => GreaterFact {
                            fact_id: f.fact_id,
                            left: f.left,
                            right: f.right,
                            line_file: f.line_file,
                        }
                        .into(),
                        f => f,
                    };
                    if !instantiated_fact_matches(
                        &strict.into(),
                        &guard.point_fact,
                        &HashMap::from([(builder.param_binding.id, point.clone())]),
                    ) || source_subject(&guard.point_proof)? != guard.point_fact
                    {
                        return Err(invalid("GuardPointSubject"));
                    }
                    let args = atomic_fact_args_ref(&guard.guard);
                    let operands = if matches!(&guard.guard, AtomicFact::InFact(_)) {
                        &args[..1]
                    } else {
                        args.as_slice()
                    };
                    if operands.len() != guard.operands.len() {
                        return Err(invalid("GuardOperandArity"));
                    }
                    let mut children = Vec::new();
                    for (operand, expected) in guard.operands.iter().zip(operands) {
                        let child = match operand {
                            InteriorOperandProof::Continuous(p) => {
                                if p.expression.ir() != expected.ir() {
                                    return Err(invalid("ContinuousSubject"));
                                }
                                self.compile_interior_continuity(
                                    p,
                                    builder.param_binding.id,
                                    point,
                                    position,
                                    lines,
                                )?
                            }
                            InteriorOperandProof::Differentiable(p) => {
                                if p.expression.ir() != expected.ir() {
                                    return Err(invalid("DerivativeSubject"));
                                }
                                lines.extend(self.compile_derivative_tree(
                                    p,
                                    builder.param_binding.id,
                                    point,
                                    position,
                                )?);
                                let (raw, _, slope, node) = names(p)?;
                                let cid = source_subject(&p.value_real)?.fact_id().value();
                                let continuous = format!("_interior_from_derivative_{cid}");
                                lines.push(format!("  have {continuous} : Litex.SemanticContinuousAtValue M {raw} _derivative_real_point := Litex.semanticContinuousOfDerivative {raw} _derivative_real_point {slope} {node}"));
                                (raw, format!("_derivative_at_{cid}"), continuous)
                            }
                        };
                        children.push(child);
                    }
                    let (ty, term) = self.compile_verify(
                        &guard.point_proof,
                        &position.atomic_search_verify_prior(&guard.point_proof)?,
                    )?;
                    let gid = guard.point_fact.fact_id().value();
                    lines.push(format!("  have h_{gid} : {ty} := {term}"));
                    let raw_args = args
                        .iter()
                        .map(|arg| {
                            self.compile_function_raw_expression_bound(
                                arg,
                                position,
                                &HashMap::from([(
                                    builder.param_binding.id,
                                    "(M.number (_interior_input : ℂ))".into(),
                                )]),
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let prop =
                        self.compile_atomic_raw_proposition(&guard.guard, &raw_args, position)?;
                    let event = format!("_interior_guard_{gid}");
                    let (a, aa, ha) = &children[0];
                    let step = match &guard.guard {
                        AtomicFact::LessFact(_)
                        | AtomicFact::GreaterFact(_)
                        | AtomicFact::LessEqualFact(_)
                        | AtomicFact::GreaterEqualFact(_) => {
                            let (b, ba, hb) = &children[1];
                            let reverse = matches!(
                                &guard.guard,
                                AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_)
                            );
                            let (a, aa, ha, b, ba, hb) = if reverse {
                                (b, ba, hb, a, aa, ha)
                            } else {
                                (a, aa, ha, b, ba, hb)
                            };
                            let source=format!("Litex.semanticContinuousLt {a} {b} _derivative_real_point {ha} {hb} (by rw [{aa},{ba}]; exact h_{gid})");
                            if matches!(
                                &guard.guard,
                                AtomicFact::LessEqualFact(_) | AtomicFact::GreaterEqualFact(_)
                            ) {
                                format!("exact ({source}).mono (fun _ h => by obtain ⟨r,s,hr,hs,hl⟩ := h; exact ⟨r,s,hr,hs,le_of_lt hl⟩)")
                            } else {
                                format!("exact {source}")
                            }
                        }
                        AtomicFact::NotEqualFact(_) => {
                            let (b, ba, hb) = &children[1];
                            format!("exact Litex.semanticContinuousNe {a} {b} _derivative_real_point {ha} {hb} (by rw [{aa},{ba}]; exact h_{gid})")
                        }
                        AtomicFact::InFact(f) => {
                            let law = match &f.set {
                                Obj::StandardSet(StandardSet::R) => "realDomainOpen",
                                Obj::StandardSet(StandardSet::RPos) => "positiveRealDomainOpen",
                                Obj::StandardSet(StandardSet::RNeg) => "negativeRealDomainOpen",
                                Obj::StandardSet(StandardSet::RStar) => "nonzeroRealDomainOpen",
                                _ => return Err(invalid("MembershipCarrier")),
                            };
                            format!("exact Litex.semanticContinuousMembership {a} _derivative_real_point {} {ha} (by rw [{aa}]; exact h_{gid}) Litex.{law}",raw_args[1])
                        }
                        _ => return Err(invalid("GuardKind")),
                    };
                    lines.push(format!("  have {event} : ∀ᶠ (_interior_input : ℝ) in nhds _derivative_real_point, {prop} := by\n    {step}"));
                    events.push(event);
                }
                let mut filters = vec![base_name];
                filters.extend(events.clone());
                let mut hypotheses = vec!["_base_member".to_owned()];
                hypotheses.extend((0..events.len()).map(|i| format!("_guard_{i}")));
                let mut pair = vec!["_base_member".to_owned(), "_base_member".to_owned()];
                pair.extend(hypotheses[1..].iter().cloned());
                if events.is_empty() {
                    pair.push("True.intro".into());
                }
                Ok(format!("(by\n    filter_upwards [{}] with _interior_input {}\n    apply (Litex.SetSemantics.sep_members _ _ _).mpr\n    exact ⟨{}⟩\n  )",filters.join(","),hypotheses.join(" "),pair.join(",")))
            }
        }
    }
}
