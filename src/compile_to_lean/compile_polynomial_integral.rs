//! Replay bounded polynomial integration and its checked pointwise normalization.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_riemann_integral::validate_domain_requirement;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::structural_riemann_integral::{
    power_integral, RiemannConclusionProof, RiemannConstructorProof as C, RiemannExpressionProof,
    StructuralRiemannIntegralProof,
};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("PolynomialIntegral/{stage}"))
}

fn num(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(value.into())))
}

struct CompiledIntegralExpression {
    raw: String,
    value: String,
    proof: String,
    definitions: Vec<String>,
}

impl LitexToLeanCompiler {
    fn compile_integral_real(
        &self,
        object: &Obj,
        proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::InFact(p))
            if p.element.ir()==object.ir() && p.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("RealMembershipSubject"));
        }
        let (ty, term) =
            self.compile_verify(proof, &position.atomic_search_verify_prior(proof)?)?;
        let name = format!("h_{}", source_subject(proof)?.fact_id().value());
        lines.push(format!("have {name} : {ty} := {term}"));
        Ok(name)
    }

    fn compile_integral_expression(
        &self,
        p: &RiemannExpressionProof,
        variable: IdentifierId,
        lower: &Obj,
        upper: &Obj,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
        allow_polynomial: bool,
    ) -> Result<CompiledIntegralExpression, LeanCompileError> {
        let id = source_subject(&p.integral_real)?.fact_id().value();
        let raw = format!("_integral_expression_{id}");
        let value = format!("_integral_value_{id}");
        let proof = format!("_integral_proof_{id}");
        let value_expression =
            self.compile_function_raw_expression_bound(&p.integral, position, &HashMap::new())?;
        let mut rewrites = vec![
            "← _integral_lower_eq".to_string(),
            "← _integral_upper_eq".to_string(),
        ];
        let mut definitions = Vec::new();
        let (raw_body, expected, rule) = match &p.constructor {
            C::Constant { value_real } => {
                if contains_parameter(&p.expression, variable) {
                    return Err(invalid("ConstantScope"));
                }
                let real =
                    self.compile_integral_real(&p.expression, value_real, position, lines)?;
                let constant = self.compile_function_raw_expression_bound(
                    &p.expression,
                    position,
                    &HashMap::new(),
                )?;
                (constant.clone(), mul_objs(p.expression.clone(), sub_objs(upper.clone(), lower.clone())),
                    format!("Litex.polynomialIntegralConstant (M := M) ({constant}) {real} _integral_lower _integral_upper"))
            }
            C::Variable => {
                if !matches!(&p.expression, Obj::Identifier(IdentifierObj::Plain {id,..}) if *id==variable)
                {
                    return Err(invalid("VariableSubject"));
                }
                (
                    "M.number (_integral_input : ℂ)".into(),
                    power_integral(lower, upper, num("1")),
                    "Litex.polynomialIntegralVariable (M := M) _integral_lower _integral_upper"
                        .into(),
                )
            }
            C::NaturalPower { exponent_natural } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &p.expression else {
                    return Err(invalid("PowerSubject"));
                };
                if !matches!(power.base.as_ref(),Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==variable)
                    || contains_parameter(&power.exponent, variable)
                {
                    return Err(invalid("PowerVariable"));
                }
                if !matches!(source_subject(exponent_natural)?,Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir()==power.exponent.ir()&&f.set==Obj::StandardSet(StandardSet::N))
                {
                    return Err(invalid("PowerNatural"));
                }
                let (ty, term) = self.compile_verify(
                    exponent_natural,
                    &position.atomic_search_verify_prior(exponent_natural)?,
                )?;
                let natural = format!("h_{}", source_subject(exponent_natural)?.fact_id().value());
                lines.push(format!("have {natural} : {ty} := {term}"));
                let exponent = self.compile_object_reference(&power.exponent, position)?;
                let raw_exponent = self.compile_function_raw_expression_bound(
                    &power.exponent,
                    position,
                    &HashMap::new(),
                )?;
                let n = format!("_integral_exponent_{id}");
                lines.push(format!(
                    "let {n} := Litex.NativeBridge.asNat {exponent} {natural}"
                ));
                let eq = format!("_integral_exponent_eq_{id}");
                lines.push(format!("have {eq} : {raw_exponent}=M.number ({n} : ℂ) := Litex.NativeBridge.asNat_spec {exponent} {natural}"));
                rewrites.push(format!("← {eq}"));
                (
                    format!("M.powValue (M.number (_integral_input : ℂ)) ({raw_exponent})"),
                    power_integral(lower, upper, *power.exponent.clone()),
                    format!("Litex.polynomialIntegralPower (M := M) _integral_lower _integral_upper {n}"),
                )
            }
            C::Add { left, right } | C::Sub { left, right } => {
                let (a, b, op, theorem) = match &p.expression {
                    Obj::ArithmeticOperator(ArithmeticOperator::Add(e))
                        if matches!(p.constructor, C::Add { .. }) =>
                    {
                        (&e.left, &e.right, "addValue", "Add")
                    }
                    Obj::ArithmeticOperator(ArithmeticOperator::Sub(e))
                        if matches!(p.constructor, C::Sub { .. }) =>
                    {
                        (&e.left, &e.right, "subValue", "Sub")
                    }
                    _ => return Err(invalid("BinarySubject")),
                };
                if a.ir() != left.expression.ir() || b.ir() != right.expression.ir() {
                    return Err(invalid("BinaryChildren"));
                }
                let l = self.compile_integral_expression(
                    left, variable, lower, upper, position, lines, false,
                )?;
                let r = self.compile_integral_expression(
                    right, variable, lower, upper, position, lines, false,
                )?;
                definitions.extend(l.definitions.iter().cloned());
                definitions.extend(r.definitions.iter().cloned());
                let expected = if theorem == "Add" {
                    add_objs(left.integral.clone(), right.integral.clone())
                } else {
                    sub_objs(left.integral.clone(), right.integral.clone())
                };
                (format!("M.{op} ({} _integral_input) ({} _integral_input)",l.raw,r.raw),expected,
                    format!("Litex.polynomialIntegral{theorem} (M := M) {} {} _integral_lower _integral_upper {} {} {} {}",l.raw,r.raw,l.value,r.value,l.proof,r.proof))
            }
            C::Neg { argument } => {
                if !matches!(&p.expression,Obj::ArithmeticOperator(ArithmeticOperator::Neg(e)) if e.arg.ir()==argument.expression.ir())
                {
                    return Err(invalid("NegSubject"));
                }
                let a = self.compile_integral_expression(
                    argument, variable, lower, upper, position, lines, false,
                )?;
                definitions.extend(a.definitions.iter().cloned());
                (
                    format!("M.negValue ({} _integral_input)", a.raw),
                    sub_objs(num("0"), argument.integral.clone()),
                    format!(
                        "Litex.polynomialIntegralNeg (M := M) {} _integral_lower _integral_upper {} {}",
                        a.raw, a.value, a.proof
                    ),
                )
            }
            C::Scale {
                scalar,
                scalar_real,
                argument,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(e)) = &p.expression else {
                    return Err(invalid("ScaleSubject"));
                };
                if contains_parameter(scalar, variable) {
                    return Err(invalid("ScaleParameter"));
                };
                let reversed =
                    e.left.ir() == argument.expression.ir() && e.right.ir() == scalar.ir();
                if !reversed
                    && !(e.right.ir() == argument.expression.ir() && e.left.ir() == scalar.ir())
                {
                    return Err(invalid("ScaleChildren"));
                }
                let real = self.compile_integral_real(scalar, scalar_real, position, lines)?;
                let c =
                    self.compile_function_raw_expression_bound(scalar, position, &HashMap::new())?;
                let a = self.compile_integral_expression(
                    argument, variable, lower, upper, position, lines, false,
                )?;
                definitions.extend(a.definitions.iter().cloned());
                let body = if reversed {
                    format!("M.mulValue ({} _integral_input) ({c})", a.raw)
                } else {
                    format!("M.mulValue ({c}) ({} _integral_input)", a.raw)
                };
                let theorem = if reversed { "ScaleRight" } else { "Scale" };
                (body,mul_objs(scalar.clone(),argument.integral.clone()),
                    format!("Litex.polynomialIntegral{theorem} (M := M) {} _integral_lower _integral_upper {} ({c}) {real} {}",a.raw,a.value,a.proof))
            }
            C::Divide {
                argument,
                denominator_real,
                denominator_nonzero,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Div(e)) = &p.expression else {
                    return Err(invalid("DivideSubject"));
                };
                if e.left.ir() != argument.expression.ir() || contains_parameter(&e.right, variable)
                {
                    return Err(invalid("DivideChildren"));
                }
                let real =
                    self.compile_integral_real(&e.right, denominator_real, position, lines)?;
                if !matches!(source_subject(denominator_nonzero)?,Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir()==e.right.ir()&&is_zero(&f.right))
                {
                    return Err(invalid("DenominatorNonzero"));
                }
                let (ty, term) = self.compile_verify(
                    denominator_nonzero,
                    &position.atomic_search_verify_prior(denominator_nonzero)?,
                )?;
                let nz = format!(
                    "h_{}",
                    source_subject(denominator_nonzero)?.fact_id().value()
                );
                lines.push(format!("have {nz} : {ty} := {term}"));
                let c = self.compile_function_raw_expression_bound(
                    &e.right,
                    position,
                    &HashMap::new(),
                )?;
                let a = self.compile_integral_expression(
                    argument, variable, lower, upper, position, lines, false,
                )?;
                definitions.extend(a.definitions.iter().cloned());
                (format!("M.divValue ({} _integral_input) ({c})",a.raw),div_objs(argument.integral.clone(),*e.right.clone()),
                    format!("Litex.polynomialIntegralDivide (M := M) {} _integral_lower _integral_upper {} ({c}) {real} {nz} {}",a.raw,a.value,a.proof))
            }
            C::Polynomial {
                equality,
                normalized,
            } => {
                if !allow_polynomial {
                    return Err(invalid("NestedPolynomial"));
                }
                if p.integral.ir() != normalized.integral.ir() {
                    return Err(invalid("NormalizedIntegral"));
                }
                let prior = position.atomic_search_verify_prior(equality)?;
                let local = SourcePosition::new(Some(&prior), SourceOwner::Term, 0);
                let (ty, term) = self.compile_verify(equality, &local)?;
                lines.push(format!("have _integral_normalization : {ty} := {term}"));
                let compiled = self.compile_integral_expression(
                    normalized, variable, lower, upper, position, lines, false,
                )?;
                self.compile_integral_real(&p.integral, &p.integral_real, position, lines)?;
                return Ok(compiled);
            }
            C::Application { .. } => return Err(invalid("NonPolynomialLeaf")),
        };
        if expected.ir() != p.integral.ir() {
            return Err(invalid("ConstructedIntegral"));
        }
        self.compile_integral_real(&p.integral, &p.integral_real, position, lines)?;
        lines.push(format!(
            "let {raw} : ℝ → M.Value := fun _integral_input => {raw_body}"
        ));
        lines.push(format!("let {value} : M.Value := {value_expression}"));
        definitions.push(raw.clone());
        definitions.push(value.clone());
        lines.push(format!("have {proof} : Litex.PolynomialIntegralFormula {raw} _integral_lower _integral_upper {value} := by\n  simpa only [{}, {}, M.add_numbers, one_add_one_eq_two] using ({rule})",definitions.join(", "),rewrites.join(", ")));
        Ok(CompiledIntegralExpression {
            raw,
            value,
            proof,
            definitions,
        })
    }

    pub(super) fn compile_polynomial_integral(
        &self,
        goal: &AtomicFact,
        p: &StructuralRiemannIntegralProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (function, lower, upper, selected) = match goal {
            AtomicFact::HasRiemannIntegralFact(f) => {
                (&f.function, &f.lower, &f.upper, Some(&f.value))
            }
            AtomicFact::FunctionRiemannIntegrableFact(f) => (&f.function, &f.lower, &f.upper, None),
            _ => return Err(invalid("Goal")),
        };
        if function.ir() != p.function.ir()
            || lower.ir() != p.lower.ir()
            || upper.ir() != p.upper.ir()
            || p.expression.expression.ir() != p.body.equal_to.ir()
            || !crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(
                &p.domain.source.signature,
                &p.body.body,
            )
        {
            return Err(invalid("OriginalSubject"));
        }
        let [group] = p.body.body.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("Signature"));
        };
        let [variable] = group.params.as_slice() else {
            return Err(invalid("Arity"));
        };
        let mut lines = Vec::new();
        for checked in [&p.domain.input_real, &p.domain.output_real] {
            let (ty, term) =
                self.compile_verify(checked, &position.atomic_search_verify_prior(checked)?)?;
            lines.push(format!(
                "have h_{} : {ty} := {term}",
                source_subject(checked)?.fact_id().value()
            ));
        }
        let real = self.compile_real_function_domain(function, &p.domain, position)?;
        let function_object = self.compile_object_reference(function, position)?;
        let f = format!("Litex.denote ({function_object})");
        let a = self.compile_function_raw_expression_bound(lower, position, &HashMap::new())?;
        let b = self.compile_function_raw_expression_bound(upper, position, &HashMap::new())?;
        let (view, domain_equal) =
            self.compile_function_limit_domain_view(function, &p.domain, position)?;
        lines.push(
            view.lines()
                .map(|line| line.strip_prefix("  ").unwrap_or(line))
                .collect::<Vec<_>>()
                .join("\n"),
        );
        if p.interval_requirements.len() != 3 {
            return Err(invalid("IntervalRequirements"));
        }
        let mut requirements = Vec::new();
        for (i, checked) in p.interval_requirements.iter().enumerate() {
            let fact = source_subject(checked)?;
            validate_domain_requirement(&fact, i, lower, upper, &p.domain.domain)?;
            let (ty, term) =
                self.compile_verify(checked, &position.atomic_search_verify_prior(checked)?)?;
            let name = format!("h_{}", fact.fact_id().value());
            lines.push(format!("have {name} : {ty} := {term}"));
            requirements.push(name);
        }
        lines.push(format!("let _integral_lower := Litex.observeRealValue ({a})\nlet _integral_upper := Litex.observeRealValue ({b})\nhave _integral_lower_eq : {a}=M.number (_integral_lower : ℂ) := Litex.riemannRealObservation {}\nhave _integral_upper_eq : {b}=M.number (_integral_upper : ℂ) := Litex.riemannRealObservation {}",requirements[0],requirements[1]));
        let expression = self.compile_integral_expression(
            &p.expression,
            variable.id,
            lower,
            upper,
            position,
            &mut lines,
            true,
        )?;
        let body_obj = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.body.clone()));
        let literal = self.compile_checked_function_body(
            function,
            &body_obj,
            &p.body_well_defined,
            position,
        )?;
        lines.push(format!("let _integral_literal := {literal}"));
        let path = self.compile_equality_path(function, &body_obj, &p.body_equal, position)?;
        lines.push(format!(
            "have _integral_function_eq : {f}=Litex.denote _integral_literal := {path}"
        ));
        let interval_fold = if let Some((proofs, names)) =
            self.compile_riemann_endpoint_reductions(lower, upper, position)?
        {
            format!(
                "\n  {}\n  unfold Litex.riemannIntervalValue\n  {}",
                proofs.replace('\n', "\n  "),
                super::compile_riemann_integral::endpoint_rewrites(&names, "")
            )
        } else {
            String::new()
        };
        lines.push(format!("have _integral_cover : ∀ x, M.mem x (Litex.riemannIntervalValue ({a}) ({b})) → M.mem x (Litex.FunctionSemantics.domainValue ({f})) := by\n  rw [← {domain_equal}]{interval_fold}\n  exact {}",requirements[2]));
        lines.push(format!("have _integral_graph_domain : Litex.FunctionSemantics.domainValue ({f})=_integral_literal.val.signature.domain := by\n  rw [_integral_function_eq]\n  exact Litex.FunctionSemantics.domainValue_eq _integral_literal.val.signature.domain_isSet (Litex.formulaFnInFnSet _integral_literal)"));
        let mut body_formula=format!("intro x hx\nhave hxD := _integral_cover (M.number (x : ℂ)) hx\nhave hxLiteral := _integral_graph_domain ▸ hxD\nhave original := (congrArg (fun f => Litex.FunctionSemantics.callValue f (M.number (x : ℂ))) _integral_function_eq).trans (Litex.FunctionSemantics.call_graphValue _ _ _ _integral_literal.wd _ hxLiteral)");
        if let C::Polynomial {
            equality,
            normalized,
        } = &p.expression.constructor
        {
            let Fact::ForallFact(universal) = source_subject(equality)? else {
                return Err(invalid("NormalizationUniversal"));
            };
            let binder = parameter(&universal.typed_parameters, &p.domain.domain)?;
            let Some(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))) =
                universal.then_facts.last()
            else {
                return Err(invalid("NormalizationEquation"));
            };
            let substitution = HashMap::from([(
                variable.id,
                Obj::Identifier(IdentifierObj::from_bound_name(binder)),
            )]);
            if !universal.dom_facts.is_empty()
                || !instantiated_object_matches(&p.expression.expression, &eq.left, &substitution)
                || !instantiated_object_matches(&normalized.expression, &eq.right, &substitution)
            {
                return Err(invalid("NormalizationSubject"));
            }
            let application = "(_integral_normalization (Litex.semanticObject (M := M) (M.number (x : ℂ)) (M.member_isSet (Litex.NativeBridge.numberInR x))) hxSource)";
            let equality = conjunction_projection(
                application,
                universal.then_facts.len() - 1,
                universal.then_facts.len(),
            );
            body_formula.push_str(&format!("\nhave hxSource : M.mem (M.number (x : ℂ)) _source_domain := by\n  rw [{domain_equal}]\n  exact hxD\nexact original.trans ({equality})"));
        } else {
            body_formula.push_str("\nexact original");
        }
        lines.push(format!("have _integral_formula : ∀ x : ℝ, M.mem (M.number (x : ℂ)) (Litex.riemannIntervalValue ({a}) ({b})) → Litex.FunctionSemantics.callValue ({f}) (M.number (x : ℂ))={} x := by\n  {}",expression.raw,body_formula.replace('\n',"\n  ")));
        lines.push(format!("have _integral_candidate : Litex.HasRiemannIntegralValue M ({f}) ({a}) ({b}) {} := Litex.riemannIntegralOfPolynomialFormula ({f}) ({a}) ({b}) {} ({real}) {} {} _integral_cover {} _integral_formula {}",expression.value,expression.value,requirements[0],requirements[1],expression.raw,expression.proof));
        match (&p.conclusion,selected) {
            (RiemannConclusionProof::Candidate(equality),Some(value)) => {
                if !matches!(source_subject(equality)?,Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==p.expression.integral.ir()&&eq.right.ir()==value.ir()) {return Err(invalid("ConclusionSubject"));}
                let (ty,term)=self.compile_verify(equality,&position.atomic_search_verify_prior(equality)?)?;
                let result=self.compile_function_raw_expression_bound(value,position,&HashMap::new())?;
                lines.push(format!("have _integral_result_eq : {}={result} := (show {ty} from {term})\nexact (congrArg (fun value => Litex.HasRiemannIntegralValue M ({f}) ({a}) ({b}) value) _integral_result_eq).mp _integral_candidate",expression.value));
            }
            (RiemannConclusionProof::Integrable,None) => lines.push(format!("exact Litex.riemannIntegralExistsOfCandidate ({f}) ({a}) ({b}) {} _integral_candidate", expression.value)),
            _ => return Err(invalid("ConclusionKind")),
        }
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    pub(super) fn compile_integral_value_strategy(
        &self,
        fact: &EqualFact,
        p: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_riemann_integral::RiemannIntegralValueStrategyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(candidate)) =
            source_subject(&p.candidate)?
        else {
            return Err(invalid("ValueCandidate"));
        };
        let (selected, value, reverse) = match (&fact.left, &fact.right) {
            (Obj::IntegralOperator(IntegralOperator::Riemann(i)), v) => (i, v, false),
            (v, Obj::IntegralOperator(IntegralOperator::Riemann(i))) => (i, v, true),
            _ => return Err(invalid("ValueSubject")),
        };
        if selected.function.ir() != candidate.function.ir()
            || selected.lower.ir() != candidate.lower.ir()
            || selected.upper.ir() != candidate.upper.ir()
            || value.ir() != candidate.value.ir()
        {
            return Err(invalid("ValueCandidateSubject"));
        }
        let (ty, term) =
            self.compile_verify(&p.candidate, &position.search_verify_prior(&p.candidate)?)?;
        let object = self
            .compile_object_reference(if reverse { &fact.right } else { &fact.left }, position)?;
        let value = self.compile_object_reference(value, position)?;
        let eq = format!(
            "Litex.riemannIntegralEqCandidate {object} (Litex.denote ({value})) (show {ty} from {term})"
        );
        Ok(if reverse { format!("({eq}).symm") } else { eq })
    }
}
