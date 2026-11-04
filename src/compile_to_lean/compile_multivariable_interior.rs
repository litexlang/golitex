//! Replay structural guard certificates along the requested coordinate path.
use super::compile_multivariable_scalar_limit::{distance, vector_set};
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_smooth_partial_derivative::{id, indices, minus, number, plus, times};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::expression::{
    call_head, depends_on, SmoothCoordinateConstructorProof as C,
    SmoothCoordinateExpressionProof as E,
};
use crate::execute::execute_fact_stmt::multivariable::strategy::MultivariableInteriorProof as P;
use crate::prelude::*;
use crate::rational_expression::helper::{div_objs, sub_objs};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MultivariableInterior/{stage}"))
}
fn names(p: &E) -> Result<(String, String, String), LeanCompileError> {
    let i = id(p)?;
    Ok((
        format!("_guard_raw_{i}"),
        format!("_guard_at_{i}"),
        format!("_guard_continuous_{i}"),
    ))
}

fn validate_known_interior(
    domain: &Obj,
    point: &Obj,
    dimension: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(exists) = fact else {
        return Err(invalid("KnownExistence"));
    };
    let radius = parameter(
        &exists.typed_parameters,
        &Obj::StandardSet(StandardSet::RPos),
    )?;
    let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion))] =
        exists.facts.as_slice()
    else {
        return Err(invalid("KnownInclusion"));
    };
    let Obj::SetFormer(SetFormer::SetBuilder(ball)) = &inclusion.left else {
        return Err(invalid("KnownBall"));
    };
    if inclusion.right.ir() != domain.ir() || ball.param_set.ir() != vector_set(dimension).ir() {
        return Err(invalid("KnownDomain"));
    }
    if radius.id == ball.param_binding.id
        || [domain, point, dimension].iter().any(|obj| {
            contains_parameter(obj, radius.id) || contains_parameter(obj, ball.param_binding.id)
        })
    {
        return Err(invalid("KnownCapture"));
    }
    let [QuantifierFreeFact::AtomicFact(bound)] = ball.facts.as_slice() else {
        return Err(invalid("KnownBound"));
    };
    let (d, r, strict) = source_order_oriented(bound)?;
    let radius_obj = Obj::Identifier(IdentifierObj::from_bound_name(radius));
    if !strict || r.ir() != radius_obj.ir() {
        return Err(invalid("KnownRadius"));
    }
    distance(
        d,
        &Obj::Identifier(IdentifierObj::from_bound_name(&ball.param_binding)),
        point,
        dimension,
    )
}

impl LitexToLeanCompiler {
    fn compile_guard_continuity(
        &self,
        p: &E,
        parameter: IdentifierId,
        point: &Obj,
        dimension: &Obj,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
    ) -> Result<(String, String, String), LeanCompileError> {
        let binding = HashMap::from([(parameter, point.clone())]);
        if !instantiated_object_matches(&p.expression, &p.value_reduction.source, &binding)
            || !instantiated_object_matches(
                &p.derivative_expression,
                &p.derivative_reduction.source,
                &binding,
            )
            || p.value != p.value_reduction.result
            || p.derivative_value != p.derivative_reduction.result
        {
            return Err(invalid("OperandSubstitution"));
        }
        for (obj, wd) in [
            (&p.value_reduction.source, &p.value_source_well_defined),
            (
                &p.derivative_reduction.source,
                &p.derivative_source_well_defined,
            ),
        ] {
            ensure_object(obj, wd)?;
        }
        for (obj, proof) in [
            (&p.value, &p.value_real),
            (&p.derivative_value, &p.derivative_real),
        ] {
            if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == *obj && f.set == Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("OperandRealSubject"));
            }
        }
        let i = id(p)?;
        lines.push(self.compile_smooth_value_checked(
            &p.value_real,
            &p.value_source_well_defined,
            position,
        )?);
        let (raw, at, continuous) = names(p)?;
        let body = self.compile_function_raw_expression_bound(
            &p.expression,
            position,
            &HashMap::from([(parameter, "(_smooth_path _guard_input)".into())]),
        )?;
        let value =
            self.compile_function_raw_expression_bound(&p.value, position, &HashMap::new())?;
        let reduction =
            self.compile_multivariable_reduction(&p.value_reduction, position, &HashMap::new())?;
        let (expected, step) = match &p.constructor {
            C::Constant => {
                if depends_on(&p.expression, parameter) {
                    return Err(invalid("ConstantCapture"));
                }
                let source = self.compile_function_raw_expression_bound(
                    &p.value_reduction.source,
                    position,
                    &HashMap::new(),
                )?;
                (number(0), format!("((congrArg (fun v => Litex.SemanticContinuousAtValue M (fun _ : ℝ => v) 0) (show {source}={value} from {reduction})).mpr (Litex.semanticContinuousConstant {value} 0 h_{i}))"))
            }
            C::Coordinate {
                index,
                index_member,
                axis_comparison,
            } => {
                let Obj::FnObj(call) = &p.expression else {
                    return Err(invalid("CoordinateSubject"));
                };
                if !matches!(call_head(&call.head), Obj::Identifier(IdentifierObj::Plain {id,..}) if id==parameter)
                    || call.body.len() != 1
                    || call.body[0].len() != 1
                    || *call.body[0][0] != *index
                    || depends_on(index, parameter)
                    || !matches!(source_subject(index_member)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == *index && f.set == indices(dimension))
                {
                    return Err(invalid("CoordinateIndex"));
                }
                // The producer records axis one for guard smoothness. Keep that
                // evidence, but prove continuity along the actual requested axis.
                let same = match source_subject(axis_comparison)? {
                    Fact::AtomicFact(AtomicFact::EqualFact(f))
                        if f.left == *index && f.right == number(1) =>
                    {
                        true
                    }
                    Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if f.left == *index && f.right == number(1) =>
                    {
                        false
                    }
                    _ => return Err(invalid("OriginalGuardAxis")),
                };
                lines.push(self.compile_smooth_checked(index_member, position)?);
                lines.push(self.compile_smooth_checked(axis_comparison, position)?);
                let ix =
                    self.compile_function_raw_expression_bound(index, position, &HashMap::new())?;
                let hid = source_subject(index_member)?.fact_id().value();
                (number(if same {1} else {0}), format!("Litex.semanticContinuousOfDerivative {raw} 0 (Litex.matrixIdentityEntry {ix} _smooth_axis) (Litex.semanticDerivativeCoordinatePath _smooth_point _smooth_dimension _smooth_axis {ix} _smooth_natural _smooth_point_vector _smooth_axis_member h_{hid})"))
            }
            C::Neg { argument } => {
                if !matches!(&p.expression, Obj::ArithmeticOperator(ArithmeticOperator::Neg(f)) if *f.arg == argument.expression)
                {
                    return Err(invalid("NegSubject"));
                }
                let (a, _, ha) = self.compile_guard_continuity(
                    argument, parameter, point, dimension, position, lines,
                )?;
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                        arg: Box::new(argument.derivative_expression.clone()),
                    })),
                    format!("Litex.semanticContinuousNeg {a} 0 {ha}"),
                )
            }
            C::Add { left, right }
            | C::Subtract { left, right }
            | C::Multiply { left, right }
            | C::Divide { left, right, .. } => {
                let (x, y, law) = match (&p.constructor, &p.expression) {
                    (C::Add { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Add(f))) => {
                        (&f.left, &f.right, "Add")
                    }
                    (C::Subtract { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Sub(f))) => {
                        (&f.left, &f.right, "Sub")
                    }
                    (C::Multiply { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Mul(f))) => {
                        (&f.left, &f.right, "Mul")
                    }
                    (C::Divide { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Div(f))) => {
                        (&f.left, &f.right, "Div")
                    }
                    _ => return Err(invalid("BinarySubject")),
                };
                if **x != left.expression || **y != right.expression {
                    return Err(invalid("BinaryChildren"));
                }
                let (a, _, ha) = self
                    .compile_guard_continuity(left, parameter, point, dimension, position, lines)?;
                let (b, ba, hb) = self.compile_guard_continuity(
                    right, parameter, point, dimension, position, lines,
                )?;
                let dl = left.derivative_expression.clone();
                let dr = right.derivative_expression.clone();
                let expected = match &p.constructor {
                    C::Add { .. } => plus(dl, dr),
                    C::Subtract { .. } => minus(dl, dr),
                    C::Multiply { .. } => plus(
                        times(dl, right.expression.clone()),
                        times(left.expression.clone(), dr),
                    ),
                    _ => div_objs(
                        div_objs(
                            minus(
                                times(dl, right.expression.clone()),
                                times(left.expression.clone(), dr),
                            ),
                            right.expression.clone(),
                        ),
                        right.expression.clone(),
                    ),
                };
                let mut step = format!("Litex.semanticContinuous{law} {a} {b} 0 {ha} {hb}");
                if let C::Divide { nonzero, .. } = &p.constructor {
                    ensure_nonzero_subject(&source_subject(nonzero)?, &right.value)?;
                    lines.push(self.compile_smooth_checked(nonzero, position)?);
                    let nid = source_subject(nonzero)?.fact_id().value();
                    step.push_str(&format!(" (by rw [{ba}]; exact h_{nid})"));
                }
                (expected, step)
            }
            C::NaturalPower {
                base,
                exponent_natural,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &p.expression else {
                    return Err(invalid("PowerSubject"));
                };
                if *power.base != base.expression
                    || depends_on(&power.exponent, parameter)
                    || !matches!(source_subject(exponent_natural)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == *power.exponent && f.set==Obj::StandardSet(StandardSet::N))
                {
                    return Err(invalid("PowerExponent"));
                }
                lines.push(self.compile_smooth_checked(exponent_natural, position)?);
                let (a, _, ha) = self
                    .compile_guard_continuity(base, parameter, point, dimension, position, lines)?;
                let eid = source_subject(exponent_natural)?.fact_id().value();
                let exponent = self.compile_object_reference(&power.exponent, position)?;
                let eraw = self.compile_function_raw_expression_bound(
                    &power.exponent,
                    position,
                    &HashMap::new(),
                )?;
                lines.push(format!("  let _guard_exponent_{i} := Litex.NativeBridge.asNat {exponent} h_{eid}\n  have _guard_exponent_value_{i} : {eraw}=M.number (_guard_exponent_{i} : ℂ) := Litex.NativeBridge.asNat_spec {exponent} h_{eid}"));
                let index = sub_objs(
                    Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                        left: power.exponent.clone(),
                        right: Box::new(number(1)),
                    })),
                    number(1),
                );
                let expected = times(
                    times(
                        *power.exponent.clone(),
                        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                            base: Box::new(base.expression.clone()),
                            exponent: Box::new(index),
                        })),
                    ),
                    base.derivative_expression.clone(),
                );
                (expected,format!("Litex.semanticContinuousPower {a} 0 {eraw} _guard_exponent_{i} _guard_exponent_value_{i} {ha}"))
            }
            C::Elementary {
                kind,
                argument,
                domain,
            } => {
                use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
                if p.expression != kind.apply(argument.expression.clone()) {
                    return Err(invalid("ElementarySubject"));
                }
                let (a, aa, ha) = self.compile_guard_continuity(
                    argument, parameter, point, dimension, position, lines,
                )?;
                let carrier = Obj::StandardSet(if matches!(kind, K::Ln | K::Sqrt) {
                    StandardSet::RPos
                } else {
                    StandardSet::R
                });
                if !matches!(source_subject(domain)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element==argument.value && f.set==carrier)
                {
                    return Err(invalid("ElementaryDomain"));
                }
                lines.push(self.compile_smooth_checked(domain, position)?);
                let did = source_subject(domain)?.fact_id().value();
                let law = match kind {
                    K::Exp => "Exp",
                    K::Ln => "Ln",
                    K::Sin => "Sin",
                    K::Cos => "Cos",
                    K::Sqrt => "Sqrt",
                };
                let positive = if matches!(kind, K::Ln) {
                    format!(" (by rw [{aa}]; exact h_{did})")
                } else {
                    String::new()
                };
                (
                    kind.derivative(
                        argument.expression.clone(),
                        argument.derivative_expression.clone(),
                    ),
                    format!("Litex.semanticContinuous{law} {a} 0{positive} {ha}"),
                )
            }
        };
        if expected.ir() != p.derivative_expression.ir() {
            return Err(invalid("OriginalDerivativeFormula"));
        }
        lines.push(self.compile_smooth_value_checked(
            &p.derivative_real,
            &p.derivative_source_well_defined,
            position,
        )?);
        let derivative_source = self.compile_function_raw_expression_bound(
            &p.derivative_reduction.source,
            position,
            &HashMap::new(),
        )?;
        let derivative_value = self.compile_function_raw_expression_bound(
            &p.derivative_value,
            position,
            &HashMap::new(),
        )?;
        let derivative_reduction = self.compile_multivariable_reduction(
            &p.derivative_reduction,
            position,
            &HashMap::new(),
        )?;
        lines.push(format!("  have _guard_derivative_eval_{i} : {derivative_source}={derivative_value} := {derivative_reduction}"));
        let at_point = if matches!(p.constructor, C::Constant) {
            format!("exact {reduction}")
        } else {
            format!("simp only [{raw},_smooth_path,Complex.ofReal_zero,Litex.coordinatePathValueZero _smooth_point _smooth_dimension _smooth_axis _smooth_natural _smooth_point_vector _smooth_axis_member]\n    exact {reduction}")
        };
        lines.push(format!("  let {raw} : ℝ → M.Value := fun _guard_input => {body}\n  have {at} : {raw} 0={value} := by\n    {at_point}\n  have {continuous} : Litex.SemanticContinuousAtValue M {raw} 0 := {step}"));
        Ok((raw, at, continuous))
    }

    pub(super) fn compile_multivariable_path_neighborhood(
        &self,
        domain: &Obj,
        point: &Obj,
        dimension: &Obj,
        proof: &P,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
    ) -> Result<String, LeanCompileError> {
        let domain_raw =
            self.compile_function_raw_expression_bound(domain, position, &HashMap::new())?;
        match proof {
            P::Known { condition, proof } => {
                validate_known_interior(domain, point, dimension, condition)?;
                if source_subject(proof)? != *condition {
                    return Err(invalid("KnownSubject"));
                }
                lines.push(self.compile_smooth_checked(proof, position)?);
                let i = condition.fact_id().value();
                lines.push(format!("  have _guard_interior_{i} : Litex.MultivariableInteriorValue {domain_raw} _smooth_point _smooth_dimension := by\n    obtain ⟨radius,hr,control⟩ := h_{i}\n    refine ⟨radius,hr,?_⟩\n    intro input hi hclose\n    exact control input ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨hi,hi,hclose⟩)"));
                Ok(format!("Litex.coordinatePathNeighborhoodOfInterior {domain_raw} _smooth_point _smooth_dimension _smooth_axis _smooth_natural _smooth_point_vector _smooth_axis_member _guard_interior_{i}"))
            }
            P::FullEuclideanSpace { point_member, .. }
            | P::ExactFiniteFunctionSpace { point_member, .. } => {
                let ambient = super::compile_multivariable_scalar_limit::vector_set(dimension);
                if !matches!(source_subject(point_member)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element==*point&&f.set==ambient)
                {
                    return Err(invalid("BaseMember"));
                }
                let (left, right, equality) = match proof {
                    P::FullEuclideanSpace { domain_equal, .. } => {
                        (domain.clone(), ambient, domain_equal)
                    }
                    P::ExactFiniteFunctionSpace {
                        source,
                        target,
                        signature_equal,
                        ..
                    } => {
                        self.validate_function_carrier_signature(domain, source)?;
                        Self::validate_finite_seq_signature(
                            &FiniteSeqSet {
                                set: Box::new(Obj::StandardSet(StandardSet::R)),
                                n: Box::new(dimension.clone()),
                            },
                            target,
                        )?;
                        (
                            Obj::FunctionSpace(FunctionSpace::FnSet(source.clone())),
                            Obj::FunctionSpace(FunctionSpace::FnSet(target.clone())),
                            signature_equal,
                        )
                    }
                    _ => unreachable!(),
                };
                let equal = self.compile_equality_search(
                    &EqualFact {
                        fact_id: source_subject(point_member)?.fact_id(),
                        left,
                        right,
                        line_file: None,
                    },
                    equality,
                    position,
                )?;
                lines.push(self.compile_smooth_checked(point_member, position)?);
                Ok(format!("(by\n    have he : {domain_raw}=Litex.realVectorSetValue _smooth_dimension := {equal}\n    rw [he]\n    exact Filter.Eventually.of_forall (fun h : ℝ => Litex.coordinatePathValueInVector _smooth_point _smooth_dimension _smooth_axis (M.number (h : ℂ)) _smooth_natural _smooth_point_vector _smooth_axis_member ((M.real_members _).mpr ⟨h,rfl⟩))\n  )"))
            }
            P::OpenGuards {
                domain: saved,
                base,
                guards,
            } => {
                let Obj::SetFormer(SetFormer::SetBuilder(builder)) = domain else {
                    return Err(invalid("Builder"));
                };
                if saved != domain || guards.len() != builder.facts.len() {
                    return Err(invalid("GuardCount"));
                }
                let base_term = self.compile_multivariable_path_neighborhood(
                    &builder.param_set,
                    point,
                    dimension,
                    base,
                    position,
                    lines,
                )?;
                let base_raw = self.compile_function_raw_expression_bound(
                    &builder.param_set,
                    position,
                    &HashMap::new(),
                )?;
                let base_name = format!("_guard_base_i{}", builder.param_binding.id.value());
                lines.push(format!("  have {base_name} : ∀ᶠ h : ℝ in nhds 0, M.mem (_smooth_path h) {base_raw} := {base_term}"));
                let mut events = Vec::new();
                for (guard, source) in guards.iter().zip(&builder.facts) {
                    if !matches!(source,QuantifierFreeFact::AtomicFact(f) if *f==guard.guard) {
                        return Err(invalid("GuardSubject"));
                    }
                    let args = atomic_fact_args_ref(&guard.guard);
                    let operands = if matches!(guard.guard, AtomicFact::InFact(_)) {
                        &args[..1]
                    } else {
                        args.as_slice()
                    };
                    if operands.len() != guard.operands.len() || operands.is_empty() {
                        return Err(invalid("GuardArity"));
                    }
                    let mut children = Vec::new();
                    for (operand, source) in guard.operands.iter().zip(operands) {
                        if operand.expression != **source {
                            return Err(invalid("GuardOperand"));
                        }
                        children.push(self.compile_guard_continuity(
                            operand,
                            builder.param_binding.id,
                            point,
                            dimension,
                            position,
                            lines,
                        )?);
                    }
                    let a = &guard.operands[0].value;
                    let b = guard.operands.get(1).map(|p| &p.value);
                    let correct = match (&guard.guard, &guard.point_condition) {
                        (
                            AtomicFact::LessFact(_) | AtomicFact::LessEqualFact(_),
                            Fact::AtomicFact(AtomicFact::LessFact(f)),
                        ) => &f.left == a && Some(&f.right) == b,
                        (
                            AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_),
                            Fact::AtomicFact(AtomicFact::GreaterFact(f)),
                        ) => &f.left == a && Some(&f.right) == b,
                        (
                            AtomicFact::NotEqualFact(_),
                            Fact::AtomicFact(AtomicFact::NotEqualFact(f)),
                        ) => &f.left == a && Some(&f.right) == b,
                        (AtomicFact::InFact(s), Fact::AtomicFact(AtomicFact::InFact(f))) => {
                            &f.element == a && f.set == s.set
                        }
                        _ => false,
                    };
                    if !correct || source_subject(&guard.point_proof)? != guard.point_condition {
                        return Err(invalid("StrictPointCondition"));
                    }
                    lines.push(self.compile_smooth_checked(&guard.point_proof, position)?);
                    let gid = guard.point_condition.fact_id().value();
                    let raw_args = args
                        .iter()
                        .map(|arg| {
                            self.compile_function_raw_expression_bound(
                                arg,
                                position,
                                &HashMap::from([(
                                    builder.param_binding.id,
                                    "(_smooth_path _guard_input)".into(),
                                )]),
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let prop =
                        self.compile_atomic_raw_proposition(&guard.guard, &raw_args, position)?;
                    let (a, aa, ha) = &children[0];
                    let step = match &guard.guard {
                        AtomicFact::LessFact(_)
                        | AtomicFact::LessEqualFact(_)
                        | AtomicFact::GreaterFact(_)
                        | AtomicFact::GreaterEqualFact(_) => {
                            let (b, ba, hb) = &children[1];
                            let (a, aa, ha, b, ba, hb) = if matches!(
                                guard.guard,
                                AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_)
                            ) {
                                (b, ba, hb, a, aa, ha)
                            } else {
                                (a, aa, ha, b, ba, hb)
                            };
                            let term=format!("Litex.semanticContinuousLt {a} {b} 0 {ha} {hb} (by rw [{aa},{ba}]; exact h_{gid})");
                            if matches!(
                                guard.guard,
                                AtomicFact::LessEqualFact(_) | AtomicFact::GreaterEqualFact(_)
                            ) {
                                format!("({term}).mono (fun _ h => by obtain ⟨r,s,hr,hs,hl⟩ := h; exact ⟨r,s,hr,hs,le_of_lt hl⟩)")
                            } else {
                                term
                            }
                        }
                        AtomicFact::NotEqualFact(_) => {
                            let (b, ba, hb) = &children[1];
                            format!("Litex.semanticContinuousNe {a} {b} 0 {ha} {hb} (by rw [{aa},{ba}]; exact h_{gid})")
                        }
                        AtomicFact::InFact(f) => {
                            let law = match f.set {
                                Obj::StandardSet(StandardSet::R) => "realDomainOpen",
                                Obj::StandardSet(StandardSet::RPos) => "positiveRealDomainOpen",
                                Obj::StandardSet(StandardSet::RNeg) => "negativeRealDomainOpen",
                                Obj::StandardSet(StandardSet::RStar) => "nonzeroRealDomainOpen",
                                _ => return Err(invalid("GuardCarrier")),
                            };
                            format!("Litex.semanticContinuousMembership {a} 0 {} {ha} (by rw [{aa}]; exact h_{gid}) Litex.{law}",raw_args[1])
                        }
                        _ => return Err(invalid("GuardKind")),
                    };
                    let event = format!("_guard_event_{gid}");
                    lines.push(format!(
                        "  have {event} : ∀ᶠ _guard_input : ℝ in nhds 0, {prop} := {step}"
                    ));
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
                Ok(format!("(by\n    filter_upwards [{}] with _guard_input {}\n    apply (Litex.SetSemantics.sep_members _ _ _).mpr\n    exact ⟨{}⟩\n  )",filters.join(","),hypotheses.join(" "),pair.join(",")))
            }
        }
    }
}
