//! Replay the selected joint-continuity expression tree without derivative evidence.
use super::compile_multivariable_scalar_limit::vector_set;
use super::compile_smooth_partial_derivative::{indices, number};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::continuity::{
    ContinuousExpressionConstructorProof as C, ContinuousExpressionProof as E,
};
use crate::execute::execute_fact_stmt::multivariable::expression::{call_head, depends_on};
use crate::execute::execute_fact_stmt::multivariable::strategy::{
    ContinuousMultivariableProof, MultivariableInteriorProof,
};
use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("JointContinuity/{stage}"))
}
fn id(p: &E) -> Result<u64, LeanCompileError> {
    Ok(source_subject(&p.value_real)?.fact_id().value())
}
impl LitexToLeanCompiler {
    fn compile_joint_expression(
        &self,
        p: &E,
        parameter: IdentifierId,
        point: &Obj,
        n: &Obj,
        position: &SourcePosition<'_>,
        lines: &mut Vec<String>,
    ) -> Result<(), LeanCompileError> {
        if !instantiated_object_matches(
            &p.expression,
            &p.value_reduction.source,
            &HashMap::from([(parameter, point.clone())]),
        ) || p.value.ir() != p.value_reduction.result.ir()
        {
            return Err(invalid("PointSubstitution"));
        }
        ensure_object(&p.value_reduction.source, &p.value_source_well_defined)?;
        if !matches!(source_subject(&p.value_real)?, Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir()==p.value.ir() && f.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("RealMembershipSubject"));
        }
        let i = id(p)?;
        lines.push(self.compile_smooth_value_checked(
            &p.value_real,
            &p.value_source_well_defined,
            position,
        )?);
        let raw = self.compile_function_raw_expression_bound(
            &p.expression,
            position,
            &HashMap::from([(parameter, "_joint_input".into())]),
        )?;
        let value =
            self.compile_function_raw_expression_bound(&p.value, position, &HashMap::new())?;
        let reduce =
            self.compile_multivariable_reduction(&p.value_reduction, position, &HashMap::new())?;
        lines.push(format!("  let _joint_raw_{i} : M.Value → M.Value := fun _joint_input => {raw}\n  have _joint_at_{i} : _joint_raw_{i} _joint_point={value} := {reduce}"));
        let common = "_joint_domain _joint_point _joint_dimension";
        let (step, mut unfold): (String, Vec<String>) = match &p.constructor {
            C::Constant => {
                if depends_on(&p.expression, parameter) {
                    return Err(invalid("ConstantCapture"));
                }
                let source = self.compile_function_raw_expression_bound(
                    &p.expression,
                    position,
                    &HashMap::new(),
                )?;
                (format!("Litex.semanticEuclideanContinuousConstant {common} ({source}) (by rw [show {source}={value} from {reduce}]; exact h_{i})"),vec![])
            }
            C::Coordinate {
                index,
                index_member,
            } => {
                let valid = matches!(&p.expression, Obj::FnObj(call)
                    if matches!(call_head(&call.head),Obj::Identifier(IdentifierObj::Plain {id,..}) if id==parameter)
                    && call.body.len()==1 && call.body[0].len()==1 && call.body[0][0].ir()==index.ir());
                if !valid
                    || depends_on(index, parameter)
                    || !matches!(source_subject(index_member)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==index.ir()&&f.set.ir()==indices(n).ir())
                {
                    return Err(invalid("CoordinateIndex"));
                }
                lines.push(self.compile_smooth_checked(index_member, position)?);
                let index =
                    self.compile_function_raw_expression_bound(index, position, &HashMap::new())?;
                let k = source_subject(index_member)?.fact_id().value();
                (format!("Litex.semanticEuclideanContinuousCoordinate {common} ({index}) _joint_natural _joint_point_vector _joint_inputs h_{k}"),vec![])
            }
            C::Neg { argument } => {
                if !matches!(&p.expression,Obj::ArithmeticOperator(ArithmeticOperator::Neg(q)) if q.arg.ir()==argument.expression.ir())
                {
                    return Err(invalid("NegationSubject"));
                }
                self.compile_joint_expression(argument, parameter, point, n, position, lines)?;
                let a = id(argument)?;
                (format!("Litex.semanticEuclideanContinuousNeg {common} _joint_raw_{a} _joint_node_{a}"),vec![format!("_joint_raw_{a}")])
            }
            C::Add { left, right }
            | C::Subtract { left, right }
            | C::Multiply { left, right }
            | C::Divide { left, right, .. } => {
                let (a, b, law) = match (&p.constructor, &p.expression) {
                    (C::Add { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Add(q))) => {
                        (&q.left, &q.right, "Add")
                    }
                    (C::Subtract { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Sub(q))) => {
                        (&q.left, &q.right, "Sub")
                    }
                    (C::Multiply { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Mul(q))) => {
                        (&q.left, &q.right, "Mul")
                    }
                    (C::Divide { .. }, Obj::ArithmeticOperator(ArithmeticOperator::Div(q))) => {
                        (&q.left, &q.right, "Div")
                    }
                    _ => return Err(invalid("BinarySubject")),
                };
                if a.ir() != left.expression.ir() || b.ir() != right.expression.ir() {
                    return Err(invalid("BinaryChildren"));
                }
                self.compile_joint_expression(left, parameter, point, n, position, lines)?;
                self.compile_joint_expression(right, parameter, point, n, position, lines)?;
                let a = id(left)?;
                let b = id(right)?;
                let mut step=format!("Litex.semanticEuclideanContinuous{law} {common} _joint_raw_{a} _joint_raw_{b} _joint_node_{a} _joint_node_{b}");
                if let C::Divide { nonzero, .. } = &p.constructor {
                    ensure_nonzero_subject(&source_subject(nonzero)?, &right.value)?;
                    lines.push(self.compile_smooth_checked(nonzero, position)?);
                    let z = source_subject(nonzero)?.fact_id().value();
                    step.push_str(&format!(" (by rw [_joint_at_{b}]; exact h_{z})"));
                }
                (
                    step,
                    vec![format!("_joint_raw_{a}"), format!("_joint_raw_{b}")],
                )
            }
            C::NaturalPower {
                base,
                exponent_natural,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(q)) = &p.expression else {
                    return Err(invalid("PowerSubject"));
                };
                if q.base.ir() != base.expression.ir()
                    || depends_on(&q.exponent, parameter)
                    || !matches!(source_subject(exponent_natural)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==q.exponent.ir()&&f.set==Obj::StandardSet(StandardSet::N))
                {
                    return Err(invalid("PowerExponent"));
                }
                lines.push(self.compile_smooth_checked(exponent_natural, position)?);
                self.compile_joint_expression(base, parameter, point, n, position, lines)?;
                let a = id(base)?;
                let e = source_subject(exponent_natural)?.fact_id().value();
                let exponent = self.compile_object_reference(&q.exponent, position)?;
                let raw = self.compile_function_raw_expression_bound(
                    &q.exponent,
                    position,
                    &HashMap::new(),
                )?;
                lines.push(format!("  let _joint_exponent_{i} := Litex.NativeBridge.asNat {exponent} h_{e}\n  have _joint_exponent_value_{i} : {raw}=M.number (_joint_exponent_{i} : ℂ) := Litex.NativeBridge.asNat_spec {exponent} h_{e}"));
                (format!("Litex.semanticEuclideanContinuousPower {common} _joint_raw_{a} ({raw}) _joint_exponent_{i} _joint_exponent_value_{i} _joint_node_{a}"),vec![format!("_joint_raw_{a}")])
            }
            C::Elementary {
                kind,
                argument,
                domain,
            } => {
                if p.expression.ir() != kind.apply(argument.expression.clone()).ir() {
                    return Err(invalid("ElementarySubject"));
                }
                let valid = match (kind, source_subject(domain)?) {
                    (K::Sqrt, Fact::AtomicFact(AtomicFact::LessEqualFact(f))) => {
                        f.left == number(0) && f.right.ir() == argument.value.ir()
                    }
                    (_, Fact::AtomicFact(AtomicFact::InFact(f))) => {
                        f.element.ir() == argument.value.ir()
                            && f.set
                                == Obj::StandardSet(if *kind == K::Ln {
                                    StandardSet::RPos
                                } else {
                                    StandardSet::R
                                })
                    }
                    _ => false,
                };
                if !valid {
                    return Err(invalid("ElementaryDomain"));
                }
                self.compile_joint_expression(argument, parameter, point, n, position, lines)?;
                lines.push(self.compile_smooth_checked(domain, position)?);
                let a = id(argument)?;
                let d = source_subject(domain)?.fact_id().value();
                let law = match kind {
                    K::Exp => "Exp",
                    K::Ln => "Ln",
                    K::Sin => "Sin",
                    K::Cos => "Cos",
                    K::Sqrt => "Sqrt",
                };
                let positive = if *kind == K::Ln {
                    format!(" (by rw [_joint_at_{a}]; exact h_{d})")
                } else {
                    String::new()
                };
                (format!("Litex.semanticEuclideanContinuous{law} {common} _joint_raw_{a}{positive} _joint_node_{a}"),vec![format!("_joint_raw_{a}")])
            }
        };
        unfold.insert(0, format!("_joint_raw_{i}"));
        lines.push(format!("  have _joint_node_{i} : Litex.SemanticEuclideanContinuousAtValue M {common} _joint_raw_{i} := by\n    simpa only [{}] using ({step})",unfold.join(",")));
        Ok(())
    }

    pub(super) fn compile_joint_continuity(
        &self,
        goal: &AtomicFact,
        p: &ContinuousMultivariableProof,
        wd: Option<&AtomicFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::MultivariableAnalysisFact(goal) = goal else {
            return Err(invalid("Goal"));
        };
        if goal.relation != p.relation {
            return Err(invalid("Relation"));
        }
        let (function, point, n, target) = match &p.relation {
            MultivariableAnalysisRelation::ScalarContinuousAt(q) => {
                (&q.function, &q.point, &q.dimension, None)
            }
            MultivariableAnalysisRelation::ScalarLimit(q) => {
                (&q.function, &q.point, &q.dimension, Some(&q.value))
            }
            _ => return Err(invalid("ScalarRelation")),
        };
        let [coordinate] = p.coordinates.as_slice() else {
            return Err(invalid("Coordinates"));
        };
        let [group] = p.body.body.set_bound_parameters.groups.as_slice() else {
            return Err(invalid("Signature"));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(invalid("Arity"));
        };
        if coordinate.row != 1
            || coordinate.reduction.source.ir() != p.body.equal_to.ir()
            || coordinate.expression.expression.ir() != coordinate.reduction.result.ir()
            || !crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(
                &p.function_domain.signature,
                &p.body.body,
            )
            || p.conclusion_equalities.len() != usize::from(target.is_some())
        {
            return Err(invalid("BodyExpression"));
        }
        let wd = wd.ok_or_else(|| invalid("Formation"))?;
        let PredicateDomainProof::MultivariableAnalysis(formation) =
            &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("FormationDomain"));
        };
        if formation.requirements.len() != 5
            || !crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(
                &formation.function_domain.signature,
                &p.function_domain.signature,
            )
        {
            return Err(invalid("FormationStages"));
        }
        let domain = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &p.function_domain.signature,
        )
        .ok_or_else(|| invalid("Domain"))?;
        let f = self.compile_object_reference(function, position)?;
        let point_obj = self.compile_object_reference(point, position)?;
        let n_obj = self.compile_object_reference(n, position)?;
        let (view, domain_eq) =
            self.compile_multivariable_limit_view(function, &p.function_domain, position)?;
        let mut lines = vec![view];
        let hn = formation.requirements[0].requirement.fact_id().value();
        let hp = formation.requirements[3].requirement.fact_id().value();
        lines.push(format!("  let _joint_domain := Litex.FunctionSemantics.domainValue (Litex.denote {f})\n  let _joint_point := Litex.denote {point_obj}\n  let _joint_dimension := Litex.denote {n_obj}\n  have _joint_natural := Litex.inNPos_natural {n_obj} h_{hn}\n  have _joint_point_vector := h_{hp}\n  have _joint_inputs : ∀ x, M.mem x _joint_domain → M.mem x (Litex.realVectorSetValue _joint_dimension) := by\n    obtain ⟨s,hs,hi,ho⟩ := _multivariable_real\n    intro x hx\n    exact hi x ((Litex.FunctionSemantics.domainValue_eq s.domain_isSet hs) ▸ hx)"));
        // Replay the selected complete-domain certificate. Guard/interior conversion
        // is separately unsupported until its joint neighborhood evidence is compiled.
        let (left, right, equality, point_member) = match &p.geometry {
            MultivariableInteriorProof::FullEuclideanSpace {
                domain_equal,
                point_member,
            } => (domain.clone(), vector_set(n), domain_equal, point_member),
            MultivariableInteriorProof::ExactFiniteFunctionSpace {
                source,
                target,
                signature_equal,
                point_member,
            } => {
                self.validate_function_carrier_signature(&domain, source)?;
                Self::validate_finite_seq_signature(
                    &FiniteSeqSet {
                        set: Box::new(Obj::StandardSet(StandardSet::R)),
                        n: Box::new(n.clone()),
                    },
                    target,
                )?;
                (
                    Obj::FunctionSpace(FunctionSpace::FnSet(source.clone())),
                    Obj::FunctionSpace(FunctionSpace::FnSet(target.clone())),
                    signature_equal,
                    point_member,
                )
            }
            _ => return Err(invalid("JointInterior")),
        };
        if !matches!(source_subject(point_member)?,Fact::AtomicFact(AtomicFact::InFact(q)) if q.element.ir()==point.ir()&&q.set.ir()==vector_set(n).ir())
        {
            return Err(invalid("InteriorMember"));
        }
        let equality = self.compile_equality_search(
            &EqualFact {
                fact_id: goal.fact_id,
                left,
                right,
                line_file: None,
            },
            equality,
            position,
        )?;
        lines.push(self.compile_smooth_checked(point_member, position)?);
        lines.push(format!("  have _joint_full_domain : _joint_domain=Litex.realVectorSetValue _joint_dimension := ({domain_eq}).symm.trans ({equality})\n  have _joint_point_domain : M.mem _joint_point _joint_domain := _joint_full_domain.symm ▸ _joint_point_vector"));
        let body_obj = Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.body.clone()));
        ensure_object(&body_obj, &p.body_well_defined)?;
        let body = self.compile_wd(
            &p.body_well_defined,
            &position.atomic_search_wd_prior(&p.body_well_defined)?,
        )?;
        let equal = self.compile_equality_path(function, &body_obj, &p.body_equal, position)?;
        lines.push(format!("  let _joint_literal := {body}\n  have _joint_body_eq : Litex.Same {f} _joint_literal := {equal}"));
        self.compile_joint_expression(
            &coordinate.expression,
            parameter.id,
            point,
            n,
            position,
            &mut lines,
        )?;
        let i = id(&coordinate.expression)?;
        let body_reduction=if coordinate.reduction.steps.iter().any(|step|matches!(step,crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionStep::AnonymousBeta{..}|crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionStep::PeriodicTrig{..})) {
            format!("({} input (_joint_graph_domain ▸ hi))",self.compile_multivariable_literal_reduction(&p.body,&coordinate.reduction,position)?)
        }else{self.compile_multivariable_reduction(&coordinate.reduction,position,&HashMap::from([(parameter.id,"input".into())]))?};
        lines.push(format!("  have _joint_graph_domain : _joint_domain=_joint_literal.val.signature.domain := by\n    change Litex.FunctionSemantics.domainValue (Litex.denote {f})=_\n    rw [_joint_body_eq]\n    exact Litex.FunctionSemantics.domainValue_eq _joint_literal.val.signature.domain_isSet (Litex.formulaFnInFnSet _joint_literal)\n  have _joint_body : ∀ input, M.mem input _joint_domain → Litex.FunctionSemantics.callValue (Litex.denote {f}) input=_joint_raw_{i} input := by\n    intro input hi\n    exact (congrArg (fun g => Litex.FunctionSemantics.callValue g input) _joint_body_eq).trans ((Litex.FunctionSemantics.call_graphValue _ _ _ _joint_literal.wd _ (_joint_graph_domain ▸ hi)).trans ({body_reduction}))\n  have _joint_continuous := Litex.scalarMultivariableContinuousOfExpression _joint_domain (Litex.denote {f}) _joint_point _joint_dimension _joint_raw_{i} rfl _joint_point_domain _joint_body _joint_node_{i}"));
        if let Some(target) = target {
            let conclusion = &p.conclusion_equalities[0];
            if conclusion.target_reduction.source.ir() != target.ir()
                || !matches!(source_subject(&conclusion.equality)?,Fact::AtomicFact(AtomicFact::EqualFact(q)) if q.left.ir()==coordinate.expression.value.ir()&&q.right.ir()==conclusion.target_reduction.result.ir())
            {
                return Err(invalid("ConclusionSubject"));
            }
            let reduce = self.compile_multivariable_reduction(
                &conclusion.target_reduction,
                position,
                &HashMap::new(),
            )?;
            lines.push(self.compile_smooth_checked(&conclusion.equality, position)?);
            let c = source_subject(&conclusion.equality)?.fact_id().value();
            let value =
                self.compile_function_raw_expression_bound(target, position, &HashMap::new())?;
            lines.push(format!("  have _joint_accumulation := Litex.multivariableAccumulationOfVectorDomain _joint_domain _joint_point _joint_dimension h_{hn} _joint_point_vector _joint_full_domain\n  have _joint_limit := Litex.scalarContinuityToMultivariableLimit (Litex.denote {f}) _joint_point _joint_dimension (Litex.multivariableFunctionReturnsReal _ _ _ _multivariable_real _joint_point_domain) _joint_continuous _joint_accumulation\n  have _joint_result : Litex.FunctionSemantics.callValue (Litex.denote {f}) _joint_point={value} := (_joint_body _joint_point _joint_point_domain).trans (_joint_at_{i}.trans (h_{c}.trans ({reduce}).symm))\n  exact (congrArg (fun v => Litex.HasMultivariableScalarLimitValue M (Litex.denote {f}) _joint_point _joint_dimension v) _joint_result).mp _joint_limit"));
        } else {
            lines.push("  exact _joint_continuous".into());
        }
        Ok(format!("(by\n{}\n)", lines.join("\n")))
    }
}
