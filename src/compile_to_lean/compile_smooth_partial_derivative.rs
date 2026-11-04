//! Replay the selected coordinate calculus; domain and derivative evidence stay explicit.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::expression::{
    depends_on, MultivariableReductionProof, SmoothCoordinateConstructorProof as C,
    SmoothCoordinateExpressionProof as E,
};
use crate::execute::execute_fact_stmt::multivariable::strategy::{
    MultivariableInteriorProof, PartialDerivativeAtStrategyProof,
};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SmoothPartialDerivative/{stage}"))
}
pub(super) fn number(n: i64) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.to_string())))
}
// These are the producer's finite syntactic simplifications, not proof search.
pub(super) fn plus(a: Obj, b: Obj) -> Obj {
    if a == number(0) {
        b
    } else if b == number(0) {
        a
    } else {
        add_objs(a, b)
    }
}
pub(super) fn times(a: Obj, b: Obj) -> Obj {
    if a == number(0) || b == number(0) {
        number(0)
    } else if a == number(1) {
        b
    } else if b == number(1) {
        a
    } else {
        mul_objs(a, b)
    }
}
pub(super) fn minus(a: Obj, b: Obj) -> Obj {
    if a == b {
        number(0)
    } else if b == number(0) {
        a
    } else {
        sub_objs(a, b)
    }
}
pub(super) fn id(p: &E) -> Result<u64, LeanCompileError> {
    Ok(source_subject(&p.value_real)?.fact_id().value())
}
pub(super) fn indices(n: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(number(1)),
        end: Box::new(n.clone()),
    }))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_smooth_checked(
        &self,
        p: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let prior = position.atomic_search_verify_prior(p)?;
        self.compile_smooth_checked_at(p, &prior)
    }

    pub(super) fn compile_smooth_value_checked(
        &self,
        p: &VerifyFactResult,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let value = self.compile_wd(wd, &position.atomic_search_wd_prior(wd)?)?;
        let prior = position.atomic_search_verify_prior(p)?;
        // The earlier source WD is a real local constructor. Use the existing
        // cursor's child projections when replaying the following value fact.
        let bound = SourcePosition::new(Some(&prior), SourceOwner::ObjectLocal(wd), 0);
        Ok(format!(
            "  let {} := {value}\n{}",
            bound.object_local_name(),
            self.compile_smooth_checked_at(p, &bound)?
        ))
    }

    fn compile_smooth_checked_at(
        &self,
        p: &VerifyFactResult,
        prior: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (mut ty, term) = self.compile_verify(p, prior)?;
        let fact = source_subject(p)?;
        if matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(f))
            if matches!(f.set, Obj::StandardSet(_)))
        {
            // The original term still checks all WD. Its numeric membership
            // type only needs the denotation, not a second copy of that WD.
            // Keep represented types for nonstandard carriers: later calls
            // may infer their constructor from the membership citation.
            ty = self.compile_function_raw_predicate(&fact, prior, &HashMap::new())?;
        }
        Ok(format!(
            "  have h_{} : {ty} := {term}",
            fact.fact_id().value()
        ))
    }
    fn compile_smooth_reduction(
        &self,
        p: &MultivariableReductionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_multivariable_reduction(p, position, &HashMap::new())
    }
    fn compile_smooth_coordinate_tree(
        &self,
        p: &E,
        parameter: IdentifierId,
        point: &Obj,
        n: &Obj,
        axis: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if !instantiated_object_matches(
            &p.expression,
            &p.value_reduction.source,
            &HashMap::from([(parameter, point.clone())]),
        ) || !instantiated_object_matches(
            &p.derivative_expression,
            &p.derivative_reduction.source,
            &HashMap::from([(parameter, point.clone())]),
        ) || p.value.ir() != p.value_reduction.result.ir()
            || p.derivative_value.ir() != p.derivative_reduction.result.ir()
        {
            return Err(invalid("PointSubstitution"));
        }
        let i = id(p)?;
        for (subject, wd) in [
            (&p.value_reduction.source, &p.value_source_well_defined),
            (
                &p.derivative_reduction.source,
                &p.derivative_source_well_defined,
            ),
        ] {
            ensure_object(subject, wd)?;
        }
        for (subject, checked) in [
            (&p.value, &p.value_real),
            (&p.derivative_value, &p.derivative_real),
        ] {
            if !matches!(source_subject(checked)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir()&&f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("RealMembershipSubject"));
            }
        }
        let mut lines = vec![self.compile_smooth_value_checked(
            &p.value_real,
            &p.value_source_well_defined,
            position,
        )?];
        let raw = self.compile_function_raw_expression_bound(
            &p.expression,
            position,
            &HashMap::from([(parameter, "(_smooth_path _smooth_input)".into())]),
        )?;
        let value =
            self.compile_function_raw_expression_bound(&p.value, position, &HashMap::new())?;
        let slope = self.compile_function_raw_expression_bound(
            &p.derivative_value,
            position,
            &HashMap::new(),
        )?;
        let source_value = self.compile_function_raw_expression_bound(
            &p.value_reduction.source,
            position,
            &HashMap::new(),
        )?;
        let source_slope = self.compile_function_raw_expression_bound(
            &p.derivative_reduction.source,
            position,
            &HashMap::new(),
        )?;
        let value_reduction = self.compile_smooth_reduction(&p.value_reduction, position)?;
        let slope_reduction = self.compile_smooth_reduction(&p.derivative_reduction, position)?;
        let mut rewrites = Vec::new();
        let mut coefficient_reductions = String::new();
        let (expected, coefficient, step) = match &p.constructor {
            C::Constant => {
                if depends_on(&p.expression, parameter) {
                    return Err(invalid("ConstantCapture"));
                }
                (number(0),"M.number 0".into(),format!("(by\n    have h := Litex.semanticDerivativeConstant {value} 0 h_{i}\n    have eq : {source_value}={value} := {value_reduction}\n    simpa only [_smooth_raw_{i},eq] using h\n  )"))
            }
            C::Coordinate {
                index,
                index_member,
                axis_comparison,
            } => {
                let Obj::FnObj(call) = &p.expression else {
                    return Err(invalid("CoordinateExpression"));
                };
                if !matches!(crate::execute::execute_fact_stmt::multivariable::expression::call_head(&call.head),Obj::Identifier(IdentifierObj::Plain {id,..}) if id==parameter)
                    || call.body.len() != 1
                    || call.body[0].len() != 1
                    || call.body[0][0].ir() != index.ir()
                {
                    return Err(invalid("CoordinateExpression"));
                }
                if depends_on(index, parameter)
                    || !matches!(source_subject(index_member)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==index.ir()&&f.set.ir()==indices(n).ir())
                {
                    return Err(invalid("CoordinateIndex"));
                }
                let same = match source_subject(axis_comparison)? {
                    Fact::AtomicFact(AtomicFact::EqualFact(f))
                        if f.left.ir() == index.ir() && f.right.ir() == axis.ir() =>
                    {
                        true
                    }
                    Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if f.left.ir() == index.ir() && f.right.ir() == axis.ir() =>
                    {
                        false
                    }
                    _ => return Err(invalid("CoordinateAxisComparison")),
                };
                lines.push(self.compile_smooth_checked(index_member, position)?);
                lines.push(self.compile_smooth_checked(axis_comparison, position)?);
                let index =
                    self.compile_function_raw_expression_bound(index, position, &HashMap::new())?;
                let comparison = source_subject(axis_comparison)?.fact_id().value();
                let index_id = source_subject(index_member)?.fact_id().value();
                let entry = if same {
                    format!("(congrArg (fun index => Litex.matrixIdentityEntry (M := M) index _smooth_axis) h_{comparison}).trans (Litex.matrixIdentityEntrySelf _smooth_axis)")
                } else {
                    format!(
                        "Litex.matrixIdentityEntryDifferent {index} _smooth_axis h_{comparison}"
                    )
                };
                let slope_value = if same { 1 } else { 0 };
                (number(slope_value),format!("M.number {}",if same {1} else {0}),format!("(by\n    have h := Litex.semanticDerivativeCoordinatePath _smooth_point _smooth_dimension _smooth_axis {index} _smooth_natural _smooth_point_vector _smooth_axis_member h_{index_id}\n    have he : Litex.matrixIdentityEntry {index} _smooth_axis=M.number {slope_value} := {entry}\n    rw [he] at h\n    exact h\n  )"))
            }
            C::Neg { argument } => {
                if !matches!(&p.expression,Obj::ArithmeticOperator(ArithmeticOperator::Neg(f)) if f.arg.ir()==argument.expression.ir())
                {
                    return Err(invalid("NegSubject"));
                }
                lines.extend(self.compile_smooth_coordinate_tree(
                    argument, parameter, point, n, axis, position,
                )?);
                let a = id(argument)?;
                (Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {arg:Box::new(argument.derivative_expression.clone())})),format!("M.negValue _smooth_slope_{a}"),format!("Litex.semanticDerivativeNeg _smooth_raw_{a} 0 _smooth_slope_{a} _smooth_node_{a}"))
            }
            C::Add { left, right }
            | C::Subtract { left, right }
            | C::Multiply { left, right }
            | C::Divide { left, right, .. } => {
                let (a, b, law) = match (&p.constructor, &p.expression) {
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
                if a.ir() != left.expression.ir() || b.ir() != right.expression.ir() {
                    return Err(invalid("BinaryChildren"));
                }
                lines.extend(
                    self.compile_smooth_coordinate_tree(left, parameter, point, n, axis, position)?,
                );
                lines.extend(
                    self.compile_smooth_coordinate_tree(
                        right, parameter, point, n, axis, position,
                    )?,
                );
                let a = id(left)?;
                let b = id(right)?;
                let (expected,coefficient)=match p.constructor {
                    C::Add {..}=>(plus(left.derivative_expression.clone(),right.derivative_expression.clone()),format!("M.addValue _smooth_slope_{a} _smooth_slope_{b}")),
                    C::Subtract {..}=>(minus(left.derivative_expression.clone(),right.derivative_expression.clone()),format!("M.subValue _smooth_slope_{a} _smooth_slope_{b}")),
                    C::Multiply {..}=>(plus(times(left.derivative_expression.clone(),right.expression.clone()),times(left.expression.clone(),right.derivative_expression.clone())),format!("M.addValue (M.mulValue _smooth_slope_{a} _smooth_value_{b}) (M.mulValue _smooth_value_{a} _smooth_slope_{b})")),
                    C::Divide {..}=>(div_objs(div_objs(minus(times(left.derivative_expression.clone(),right.expression.clone()),times(left.expression.clone(),right.derivative_expression.clone())),right.expression.clone()),right.expression.clone()),format!("M.divValue (M.divValue (M.subValue (M.mulValue _smooth_slope_{a} _smooth_value_{b}) (M.mulValue _smooth_value_{a} _smooth_slope_{b})) _smooth_value_{b}) _smooth_value_{b}")),
                    _=>unreachable!(),
                };
                let mut step=format!("Litex.semanticDerivative{law} _smooth_raw_{a} _smooth_raw_{b} 0 _smooth_slope_{a} _smooth_slope_{b} _smooth_node_{a} _smooth_node_{b}");
                if let C::Divide { nonzero, .. } = &p.constructor {
                    ensure_nonzero_subject(&source_subject(nonzero)?, &right.value)?;
                    lines.push(self.compile_smooth_checked(nonzero, position)?);
                    let nid = source_subject(nonzero)?.fact_id().value();
                    let (native, observation) =
                        if let Obj::Literal(Literal::Number(n)) = &right.value {
                            (number_literal(n, "ℂ")?, String::new())
                        } else {
                            (
                                format!("(_smooth_value_real_{b} : ℂ)"),
                                format!("    rw [_smooth_value_observe_{b}]\n"),
                            )
                        };
                    let denominator = self.compile_function_raw_expression_bound(
                        &right.value,
                        position,
                        &HashMap::new(),
                    )?;
                    lines.push(format!("  have _smooth_denominator_nonzero_{i} : {native}≠0 := by\n    intro hz\n    apply h_{nid}\n    change {denominator}=M.number 0\n{observation}    exact congrArg M.number hz"));
                    lines.push(format!("  have _smooth_division_numbers_{i} : ∀ z : ℂ, M.divValue (M.number z) (M.number {native})=M.number (z/{native}) := fun z => M.div_numbers z {native} _smooth_denominator_nonzero_{i}"));
                    rewrites.push(format!("_smooth_division_numbers_{i}"));
                    step.push_str(&format!(" (by rw [_smooth_at_{b}]; exact h_{nid})"));
                }
                if law == "Mul" || law == "Div" {
                    step=format!("(by\n    have h := {step}\n    rw [_smooth_at_{a},_smooth_at_{b}] at h\n    exact h\n  )");
                }
                (expected, coefficient, step)
            }
            C::NaturalPower {
                base,
                exponent_natural,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &p.expression else {
                    return Err(invalid("PowerSubject"));
                };
                if power.base.ir() != base.expression.ir() || depends_on(&power.exponent, parameter)
                {
                    return Err(invalid("PowerBase"));
                }
                if !matches!(source_subject(exponent_natural)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==power.exponent.ir()&&f.set==Obj::StandardSet(StandardSet::N))
                {
                    return Err(invalid("PowerExponent"));
                }
                lines.push(self.compile_smooth_checked(exponent_natural, position)?);
                lines.extend(
                    self.compile_smooth_coordinate_tree(base, parameter, point, n, axis, position)?,
                );
                let a = id(base)?;
                let eid = source_subject(exponent_natural)?.fact_id().value();
                let exponent = self.compile_object_reference(&power.exponent, position)?;
                let exponent_raw = self.compile_function_raw_expression_bound(
                    &power.exponent,
                    position,
                    &HashMap::new(),
                )?;
                let index = sub_objs(
                    Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                        left: power.exponent.clone(),
                        right: Box::new(number(1)),
                    })),
                    number(1),
                );
                let index_raw =
                    self.compile_function_raw_expression_bound(&index, position, &HashMap::new())?;
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
                lines.push(format!("  let _smooth_exponent_{i} := Litex.NativeBridge.asNat {exponent} h_{eid}\n  have _smooth_exponent_value_{i} : {exponent_raw}=M.number (_smooth_exponent_{i} : ℂ) := Litex.NativeBridge.asNat_spec {exponent} h_{eid}\n  have _smooth_index_value_{i} : {index_raw}=M.number ((_smooth_exponent_{i}-1 : ℕ) : ℂ) := by\n    change Litex.derivativePowerIndexValue {exponent_raw}=_\n    rw [_smooth_exponent_value_{i}]\n    exact Litex.derivativePowerIndex_number _smooth_exponent_{i}"));
                // Reduce the safe index before rewriting its exponent. Otherwise
                // bottom-up simplification would erase the retained index's lhs.
                coefficient_reductions = format!(
                    "    simp only [Litex.derivativePowerIndexValue,_smooth_index_value_{i}]\n"
                );
                if !matches!(power.exponent.as_ref(), Obj::Literal(Literal::Number(_))) {
                    rewrites.push(format!("_smooth_exponent_value_{i}"));
                }
                rewrites.push("M.pow_numbers_nat".into());
                let coefficient = format!("M.mulValue (M.mulValue {exponent_raw} (M.powValue _smooth_value_{a} (Litex.derivativePowerIndexValue {exponent_raw}))) _smooth_slope_{a}");
                let step = format!("(by\n    have h := Litex.semanticDerivativePower _smooth_raw_{a} 0 _smooth_slope_{a} {exponent_raw} _smooth_exponent_{i} _smooth_exponent_value_{i} _smooth_node_{a}\n    rw [_smooth_at_{a}] at h\n    exact h\n  )");
                (expected, coefficient, step)
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
                lines.extend(self.compile_smooth_coordinate_tree(
                    argument, parameter, point, n, axis, position,
                )?);
                let positive = matches!(kind, K::Ln | K::Sqrt);
                let carrier = Obj::StandardSet(if positive {
                    StandardSet::RPos
                } else {
                    StandardSet::R
                });
                if !matches!(source_subject(domain)?, Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element == argument.value && f.set == carrier)
                {
                    return Err(invalid("ElementaryDomain"));
                }
                lines.push(self.compile_smooth_checked(domain, position)?);
                let a = id(argument)?;
                let did = source_subject(domain)?.fact_id().value();
                let (law, coefficient) = match kind {
                    K::Exp => ("Exp", format!("M.mulValue (Litex.realUnaryValue Real.exp _smooth_value_{a}) _smooth_slope_{a}")),
                    K::Sin => ("Sin", format!("M.mulValue (Litex.realUnaryValue Real.cos _smooth_value_{a}) _smooth_slope_{a}")),
                    K::Cos => ("Cos", format!("M.mulValue (M.negValue (Litex.realUnaryValue Real.sin _smooth_value_{a})) _smooth_slope_{a}")),
                    K::Ln => ("Ln", format!("M.divValue _smooth_slope_{a} _smooth_value_{a}")),
                    K::Sqrt => ("Sqrt", format!("M.divValue (M.divValue _smooth_slope_{a} (M.number 2)) (Litex.sqrtValue _smooth_value_{a})")),
                };
                if matches!(kind, K::Sqrt) {
                    // The original formula divides by the literal two before
                    // dividing by sqrt. Its closed reduction is exact.
                    lines.push(format!("  have _smooth_divide_two_{i} : ∀ z : ℂ, M.divValue (M.number z) (M.number 2)=M.number (z/2) := fun z => M.div_numbers z 2 (by norm_num)"));
                    rewrites.push(format!("_smooth_divide_two_{i}"));
                }
                rewrites.extend(
                    ["Litex.realUnaryValue_number", "Litex.sqrtValue_number"].map(str::to_owned),
                );
                let domain = if positive {
                    format!(" (by rw [_smooth_at_{a}]; exact h_{did})")
                } else {
                    String::new()
                };
                let step = format!("(by\n    have h := Litex.semanticDerivative{law} _smooth_raw_{a} 0 _smooth_slope_{a}{domain} _smooth_node_{a}\n    rw [_smooth_at_{a}] at h\n    exact h\n  )");
                (
                    kind.derivative(
                        argument.expression.clone(),
                        argument.derivative_expression.clone(),
                    ),
                    coefficient,
                    step,
                )
            }
        };
        if expected.ir() != p.derivative_expression.ir() {
            return Err(invalid("DerivativeFormula"));
        }
        lines.push(self.compile_smooth_value_checked(
            &p.derivative_real,
            &p.derivative_source_well_defined,
            position,
        )?);
        let at_point = if matches!(p.constructor, C::Constant) {
            format!("exact {value_reduction}")
        } else {
            format!("simp only [_smooth_raw_{i},_smooth_path,Complex.ofReal_zero,Litex.coordinatePathValueZero _smooth_point _smooth_dimension _smooth_axis _smooth_natural _smooth_point_vector _smooth_axis_member]\n    exact {value_reduction}")
        };
        lines.push(format!("  let _smooth_raw_{i} : ℝ → M.Value := fun _smooth_input => {raw}\n  let _smooth_value_{i} : M.Value := {value}\n  let _smooth_slope_{i} : M.Value := {slope}\n  have _smooth_at_{i} : _smooth_raw_{i} 0=_smooth_value_{i} := by\n    {at_point}"));
        // Each parent sees only its immediate children's point/derivative equations.
        // This keeps certificate references local instead of copying the prior tree prefix.
        lines.push(format!("  have _smooth_value_eval_{i} : {source_value}={value} := {value_reduction}\n  have _smooth_slope_eval_{i} : {source_slope}={slope} := {slope_reduction}"));
        for (label, object, raw, checked) in [
            ("value", &p.value, &value, &p.value_real),
            ("slope", &p.derivative_value, &slope, &p.derivative_real),
        ] {
            if !matches!(object, Obj::Literal(Literal::Number(_))) {
                let member = source_subject(checked)?.fact_id().value();
                lines.push(format!("  obtain ⟨_smooth_{label}_real_{i},_smooth_{label}_observe_{i}⟩ := (M.real_members _).mp h_{member}\n  change {raw}=M.number (_smooth_{label}_real_{i} : ℂ) at _smooth_{label}_observe_{i}"));
            }
        }
        let children: Vec<&E> = match &p.constructor {
            C::Neg { argument } | C::Elementary { argument, .. } => vec![argument],
            C::NaturalPower { base, .. } => vec![base],
            C::Add { left, right }
            | C::Subtract { left, right }
            | C::Multiply { left, right }
            | C::Divide { left, right, .. } => {
                vec![left, right]
            }
            _ => vec![],
        };
        for child in children {
            let child_id = id(child)?;
            for (label, object) in [("value", &child.value), ("slope", &child.derivative_value)] {
                rewrites.push(format!("_smooth_{label}_{child_id}"));
                rewrites.push(format!("_smooth_{label}_eval_{child_id}"));
                if !matches!(object, Obj::Literal(Literal::Number(_))) {
                    rewrites.push(format!("_smooth_{label}_observe_{child_id}"));
                }
            }
        }
        rewrites.extend(
            [
                "M.add_numbers",
                "M.sub_numbers",
                "M.mul_numbers",
                "M.neg_numbers",
            ]
            .map(str::to_owned),
        );
        lines.push(format!("  have _smooth_node_{i} : Litex.SemanticDerivativeAtValue M _smooth_raw_{i} 0 _smooth_slope_{i} := by\n    apply Litex.semanticDerivativeCoefficient _smooth_raw_{i} 0 ({coefficient}) _smooth_slope_{i} ({step})\n    apply Eq.trans (b := {source_slope}) _ ({slope_reduction})\n{coefficient_reductions}    litex_normalize_smooth_coefficient [{}]",rewrites.join(",")));
        Ok(lines)
    }

    pub(super) fn compile_smooth_partial_derivative(
        &self,
        goal: &AtomicFact,
        proof: &PartialDerivativeAtStrategyProof,
        wd: Option<&AtomicFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (r, negative) =
            super::compile_partial_derivative::parts(goal).ok_or_else(|| invalid("Goal"))?;
        let p = &proof.stages;
        if negative || p.relation != MultivariableAnalysisRelation::PartialDerivativeAt(r.clone()) {
            return Err(invalid("Relation"));
        }
        let [coordinate] = p.coordinates.as_slice() else {
            return Err(invalid("Coordinates"));
        };
        let [conclusion] = p.conclusion_equalities.as_slice() else {
            return Err(invalid("Conclusions"));
        };
        let [group] = p.body.body.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("Signature"));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(invalid("Arity"));
        };
        if coordinate.row != 1
            || coordinate.first_axis.ir() != r.coordinate.ir()
            || coordinate.second_axis.is_some()
            || coordinate.second.is_some()
            || !crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(
                &p.function_domain.signature,
                &p.body.body,
            )
        {
            return Err(invalid("CoordinateSelection"));
        }
        if coordinate.reduction.source.ir() != p.body.equal_to.ir()
            || coordinate.first.expression.ir() != coordinate.reduction.result.ir()
        {
            return Err(invalid("BodyExpression"));
        }
        let wd = wd.ok_or_else(|| invalid("Formation"))?;
        let PredicateDomainProof::MultivariableAnalysis(formation) =
            &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("FormationDomain"));
        };
        if formation.requirements.len() != 7 {
            return Err(invalid("FormationArity"));
        }
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &p.function_domain.signature,
        )
        .ok_or_else(|| invalid("Domain"))?;
        let (view, domain_eq) =
            self.compile_multivariable_limit_view(&r.function, &p.function_domain, position)?;
        let mut lines = vec![view];
        let f = self.compile_object_reference(&r.function, position)?;
        let point = self.compile_object_reference(&r.point, position)?;
        let n = self.compile_object_reference(&r.dimension, position)?;
        let axis = self.compile_object_reference(&r.coordinate, position)?;
        let hn = formation.requirements[0].requirement.fact_id().value();
        let hp = formation.requirements[3].requirement.fact_id().value();
        let hk = formation.requirements[5].requirement.fact_id().value();
        lines.push(format!("  let _smooth_point := Litex.denote {point}\n  let _smooth_dimension := Litex.denote {n}\n  let _smooth_axis := Litex.denote {axis}\n  have _smooth_natural := Litex.inNPos_natural {n} h_{hn}\n  have _smooth_point_vector := h_{hp}\n  have _smooth_axis_member := h_{hk}\n  let _smooth_path := fun h : ℝ => Litex.coordinatePathValue _smooth_point _smooth_dimension _smooth_axis (M.number (h : ℂ))"));
        match &p.geometry {
            MultivariableInteriorProof::FullEuclideanSpace {
                domain_equal,
                point_member,
            } => {
                let ambient = super::compile_multivariable_scalar_limit::vector_set(&r.dimension);
                if !matches!(source_subject(point_member)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==r.point.ir()&&f.set.ir()==ambient.ir())
                {
                    return Err(invalid("InteriorMember"));
                }
                let q = EqualFact {
                    fact_id: goal.fact_id(),
                    left: domain,
                    right: ambient,
                    line_file: None,
                };
                let equal = self.compile_equality_search(&q, domain_equal, position)?;
                lines.push(self.compile_smooth_checked(point_member, position)?);
                lines.push(format!("  have _smooth_domain : Litex.FunctionSemantics.domainValue (Litex.denote {f})=Litex.realVectorSetValue _smooth_dimension := ({domain_eq}).symm.trans {equal}\n  have _smooth_interior := Litex.partialInteriorOfVectorDomain (Litex.denote {f}) _smooth_point _smooth_dimension _smooth_axis _smooth_natural _smooth_point_vector _smooth_axis_member _smooth_domain"));
            }
            MultivariableInteriorProof::OpenGuards { .. }
            | MultivariableInteriorProof::ExactFiniteFunctionSpace { .. }
            | MultivariableInteriorProof::Known { .. } => {
                let neighborhood = self.compile_multivariable_path_neighborhood(
                    &domain,
                    &r.point,
                    &r.dimension,
                    &p.geometry,
                    position,
                    &mut lines,
                )?;
                let raw_domain =
                    self.compile_function_raw_expression_bound(&domain, position, &HashMap::new())?;
                lines.push(format!("  have _smooth_neighborhood : ∀ᶠ h : ℝ in nhds 0, M.mem (_smooth_path h) {raw_domain} := {neighborhood}\n  have _smooth_interior := Litex.partialInteriorOfNeighborhood (Litex.denote {f}) _smooth_point _smooth_dimension _smooth_axis (by\n    have hd : {raw_domain}=Litex.FunctionSemantics.domainValue (Litex.denote {f}) := {domain_eq}\n    simpa only [← hd] using _smooth_neighborhood)"));
            }
        }
        let body_obj = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.body.clone()));
        ensure_object(&body_obj, &p.body_well_defined)?;
        let body = self.compile_wd(
            &p.body_well_defined,
            &position.atomic_search_wd_prior(&p.body_well_defined)?,
        )?;
        let equal = self.compile_equality_path(&r.function, &body_obj, &p.body_equal, position)?;
        lines.push(format!("  let _smooth_literal := {body}\n  have _smooth_body_eq : Litex.Same {f} _smooth_literal := {equal}"));
        lines.extend(self.compile_smooth_coordinate_tree(
            &coordinate.first,
            parameter.id,
            &r.point,
            &r.dimension,
            &r.coordinate,
            position,
        )?);
        let i = id(&coordinate.first)?;
        let body_reduction = if coordinate.reduction.steps.iter().any(|step| matches!(step,
            crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionStep::AnonymousBeta {..}
            | crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionStep::PeriodicTrig {..})) {
            let reduction = self.compile_multivariable_literal_reduction(&p.body, &coordinate.reduction, position)?;
            format!("({reduction} (_smooth_path h) (_smooth_graph_domain ▸ hh))")
        } else { self.compile_multivariable_reduction(
            &coordinate.reduction,
            position,
            &HashMap::from([(parameter.id, "(_smooth_path h)".into())]),
        )? };
        lines.push(format!("  have _smooth_graph_domain : Litex.FunctionSemantics.domainValue (Litex.denote {f})=_smooth_literal.val.signature.domain := by\n    rw [_smooth_body_eq]\n    exact Litex.FunctionSemantics.domainValue_eq _smooth_literal.val.signature.domain_isSet (Litex.formulaFnInFnSet _smooth_literal)\n  have _smooth_body : ∀ h : ℝ, M.mem (_smooth_path h) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) → Litex.FunctionSemantics.callValue (Litex.denote {f}) (_smooth_path h)=_smooth_raw_{i} h := by\n    intro h hh\n    exact (congrArg (fun g => Litex.FunctionSemantics.callValue g (_smooth_path h)) _smooth_body_eq).trans ((Litex.FunctionSemantics.call_graphValue _ _ _ _smooth_literal.wd _ (_smooth_graph_domain ▸ hh)).trans ({body_reduction}))\n  have _smooth_zero : _smooth_raw_{i} 0=Litex.FunctionSemantics.callValue (Litex.denote {f}) _smooth_point := by\n    have hp : _smooth_path 0=_smooth_point := Litex.coordinatePathValueZero _smooth_point _smooth_dimension _smooth_axis _smooth_natural _smooth_point_vector _smooth_axis_member\n    exact (_smooth_body 0 (hp.symm ▸ _partial_point_domain)).symm.trans (congrArg (Litex.FunctionSemantics.callValue (Litex.denote {f})) hp)\n  have _smooth_candidate := Litex.partialDerivativeOfSemanticPath (Litex.denote {f}) _smooth_point _smooth_dimension _smooth_axis _smooth_slope_{i} _smooth_raw_{i} (fun x hx => Litex.multivariableFunctionReturnsReal _ _ x _multivariable_real hx) _partial_point_domain _smooth_interior _smooth_zero _smooth_body _smooth_node_{i}"));
        if conclusion.target_reduction.source.ir() != r.value.ir()
            || !matches!(source_subject(&conclusion.equality)?,Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==coordinate.first.derivative_value.ir()&&f.right.ir()==conclusion.target_reduction.result.ir())
        {
            return Err(invalid("ConclusionSubject"));
        }
        let reduce = self.compile_smooth_reduction(&conclusion.target_reduction, position)?;
        lines.push(self.compile_smooth_checked(&conclusion.equality, position)?);
        let cid = source_subject(&conclusion.equality)?.fact_id().value();
        let value =
            self.compile_function_raw_expression_bound(&r.value, position, &HashMap::new())?;
        lines.push(format!("  have _smooth_result : _smooth_slope_{i}={value} := h_{cid}.trans ({reduce}).symm\n  exact (congrArg (fun v => Litex.HasPartialDerivativeAtValue M (Litex.denote {f}) _smooth_point _smooth_dimension _smooth_axis v) _smooth_result).mp _smooth_candidate"));
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}
