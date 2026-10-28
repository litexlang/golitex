//! Bounded smooth-expression calculus, outside selector WD.
//! Smooth constructors supply full differentiability; partials alone never do.
use super::super::function_domain::{function_domains_alpha_equal, CompleteFunctionDomainProof};
use super::super::well_defined_results::verify_obj::*;
use super::expression::*;
use super::helper::*;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, sub_objs};

pub enum MultivariableStrategyProof {
    ScalarLimit(ScalarLimitStrategyProof),
    VectorLimit(VectorLimitStrategyProof),
    ScalarContinuousAt(ScalarContinuousAtStrategyProof),
    VectorContinuousAt(VectorContinuousAtStrategyProof),
    PartialDerivativeAt(PartialDerivativeAtStrategyProof),
    SecondPartialDerivativeAt(SecondPartialDerivativeAtStrategyProof),
    ScalarDifferentialAt(ScalarDifferentialAtStrategyProof),
    TotalDerivativeAt(TotalDerivativeAtStrategyProof),
    ScalarDifferentiableAt(ScalarDifferentiableAtStrategyProof),
    TotalDifferentiableAt(TotalDifferentiableAtStrategyProof),
    GradientAt(GradientAtStrategyProof),
    JacobianAt(JacobianAtStrategyProof),
    HessianAt(HessianAtStrategyProof),
    DivergenceAt(DivergenceAtStrategyProof),
    CurlAt(CurlAtStrategyProof),
    LaplacianAt(LaplacianAtStrategyProof),
}
pub struct ScalarLimitStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct VectorLimitStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct ScalarContinuousAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct VectorContinuousAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct PartialDerivativeAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct SecondPartialDerivativeAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct ScalarDifferentialAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct TotalDerivativeAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct ScalarDifferentiableAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct TotalDifferentiableAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct GradientAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct JacobianAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct HessianAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct DivergenceAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct CurlAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct LaplacianAtStrategyProof {
    pub stages: SmoothMultivariableStages,
}
pub struct SmoothMultivariableStages {
    pub relation: MultivariableAnalysisRelation,
    pub function_domain: Box<CompleteFunctionDomainProof>,
    pub body: AnonymousFn,
    pub body_equal: KnownEqualityPathProof,
    pub body_well_defined: Box<ObjWellDefinedProof>,
    pub geometry: MultivariableInteriorProof,
    pub coordinates: Vec<MultivariableCoordinateProof>,
    pub conclusion_equalities: Vec<MultivariableReducedEqualityProof>,
}
pub struct MultivariableOpenGuardProof {
    pub guard: AtomicFact,
    pub operands: Vec<SmoothCoordinateExpressionProof>,
    pub point_condition: Fact,
    pub point_proof: Box<VerifyFactResult>,
}
pub enum MultivariableInteriorProof {
    ExactFiniteFunctionSpace {
        source: FnSet,
        target: FnSet,
        signature_equal: Box<EqualFactSearchedProof>,
        point_member: Box<VerifyFactResult>,
    },
    OpenGuards {
        domain: Obj,
        base: Box<MultivariableInteriorProof>,
        guards: Vec<MultivariableOpenGuardProof>,
    },
    FullEuclideanSpace {
        domain_equal: Box<EqualFactSearchedProof>,
        point_member: Box<VerifyFactResult>,
    },
    Known {
        condition: Fact,
        proof: Box<VerifyFactResult>,
    },
}
pub struct MultivariableReducedEqualityProof {
    pub target_reduction: MultivariableReductionProof,
    pub equality: Box<VerifyFactResult>,
}
pub struct MultivariableCoordinateProof {
    pub row: usize,
    pub first_axis: Obj,
    pub second_axis: Option<Obj>,
    pub reduction: MultivariableReductionProof,
    pub first: SmoothCoordinateExpressionProof,
    pub second: Option<SmoothCoordinateExpressionProof>,
}
impl MultivariableStrategyProof {
    pub fn stages(&self) -> &SmoothMultivariableStages {
        match self {
            Self::ScalarLimit(p) => &p.stages,
            Self::VectorLimit(p) => &p.stages,
            Self::ScalarContinuousAt(p) => &p.stages,
            Self::VectorContinuousAt(p) => &p.stages,
            Self::PartialDerivativeAt(p) => &p.stages,
            Self::SecondPartialDerivativeAt(p) => &p.stages,
            Self::ScalarDifferentialAt(p) => &p.stages,
            Self::TotalDerivativeAt(p) => &p.stages,
            Self::ScalarDifferentiableAt(p) => &p.stages,
            Self::TotalDifferentiableAt(p) => &p.stages,
            Self::GradientAt(p) => &p.stages,
            Self::JacobianAt(p) => &p.stages,
            Self::HessianAt(p) => &p.stages,
            Self::DivergenceAt(p) => &p.stages,
            Self::CurlAt(p) => &p.stages,
            Self::LaplacianAt(p) => &p.stages,
        }
    }
}
impl Runtime {
    fn prove_multivariable_interior(
        &mut self,
        domain: &Obj,
        point: &Obj,
        n: &Obj,
        state: VerifyState,
        depth: usize,
    ) -> RuntimeResult<Option<MultivariableInteriorProof>> {
        if depth >= 16 {
            return Ok(None);
        }
        let ambient = vector(n.clone());
        let equation = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: domain.clone(),
            right: ambient.clone(),
            line_file: None,
        };
        let domain_equal = self.search_equal_fact_proof_directly(&equation).or_else(|| {
            self.search_homogeneous_cartesian_equality(&equation).map(|proof| {
                EqualFactSearchedProof::ByBuiltinRule(
                    EqualitySearchProofByBuiltinRule::HomogeneousCartesianEqualsFiniteSequence(proof),
                )
            })
        });
        if let Some(domain_equal) = domain_equal {
            let condition = member(self, point.clone(), ambient.clone());
            let point_member = self.verify_fact(&condition, state)?;
            if !point_member.is_failed() {
                return Ok(Some(MultivariableInteriorProof::FullEuclideanSpace {
                    domain_equal: Box::new(domain_equal),
                    point_member: Box::new(point_member),
                }));
            }
        }
        if let (Some(source), Some(target)) = (
            self.function_space_signature(domain),
            self.function_space_signature(&ambient),
        ) {
            if super::super::fn_sets_alpha_equal(&source, &target) {
                let equation = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: Obj::FunctionSpace(FunctionSpace::FnSet(source.clone())),
                    right: Obj::FunctionSpace(FunctionSpace::FnSet(target.clone())),
                    line_file: None,
                };
                if let Some(signature_equal) = self.search_equal_fact_proof_directly(&equation) {
                    let member = member(self, point.clone(), ambient);
                    let point_member = self.verify_fact(&member, state)?;
                    if !point_member.is_failed() {
                        return Ok(Some(MultivariableInteriorProof::ExactFiniteFunctionSpace {
                            source,
                            target,
                            signature_equal: Box::new(signature_equal),
                            point_member: Box::new(point_member),
                        }));
                    }
                }
            }
        }
        let condition = self.multivariable_interior(domain.clone(), point.clone(), n.clone());
        let proof = self.verify_fact(&condition, state)?;
        if !proof.is_failed() {
            return Ok(Some(MultivariableInteriorProof::Known {
                condition,
                proof: Box::new(proof),
            }));
        }
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = domain else {
            return Ok(None);
        };
        let Some(base) =
            self.prove_multivariable_interior(&builder.param_set, point, n, state, depth + 1)?
        else {
            return Ok(None);
        };
        // Base interior and each strict point guard construct membership and
        // an open neighbourhood; no weaker-ceiling re-proof of the whole builder.
        let mut guards = Vec::new();
        let mut budget = 512;
        for fact in builder.facts.iter().take(33) {
            if guards.len() >= 32 {
                return Ok(None);
            }
            let QuantifierFreeFact::AtomicFact(guard) = fact else {
                return Ok(None);
            };
            let expressions: Vec<&Obj> = match guard {
                AtomicFact::LessFact(x) => vec![&x.left, &x.right],
                AtomicFact::GreaterFact(x) => vec![&x.left, &x.right],
                AtomicFact::LessEqualFact(x) => vec![&x.left, &x.right],
                AtomicFact::GreaterEqualFact(x) => vec![&x.left, &x.right],
                AtomicFact::NotEqualFact(x) => vec![&x.left, &x.right],
                AtomicFact::InFact(x)
                    if matches!(
                        x.set,
                        Obj::StandardSet(
                            StandardSet::R
                                | StandardSet::RPos
                                | StandardSet::RNeg
                                | StandardSet::RStar
                        )
                    ) =>
                {
                    vec![&x.element]
                }
                _ => return Ok(None),
            };
            let mut operands = Vec::new();
            for expression in expressions {
                let Some(proof) = self.prove_smooth_coordinate_expression(
                    expression,
                    builder.param_binding.id,
                    point,
                    n,
                    &number(1),
                    state,
                    0,
                    &mut budget,
                )?
                else {
                    return Ok(None);
                };
                operands.push(proof);
            }
            let left = operands[0].value.clone();
            let id = self.global_ids.allocate_fact_id();
            let point_condition: Fact = match guard {
                AtomicFact::LessFact(_) | AtomicFact::LessEqualFact(_) => LessFact {
                    fact_id: id,
                    left,
                    right: operands[1].value.clone(),
                    line_file: None,
                }
                .into(),
                AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_) => GreaterFact {
                    fact_id: id,
                    left,
                    right: operands[1].value.clone(),
                    line_file: None,
                }
                .into(),
                AtomicFact::NotEqualFact(_) => NotEqualFact {
                    fact_id: id,
                    left,
                    right: operands[1].value.clone(),
                    line_file: None,
                }
                .into(),
                AtomicFact::InFact(x) => InFact {
                    fact_id: id,
                    element: left,
                    set: x.set.clone(),
                    line_file: None,
                }
                .into(),
                _ => unreachable!("open guard constructor checked above"),
            };
            let point_proof = self.verify_fact(&point_condition, state)?;
            if point_proof.is_failed() {
                return Ok(None);
            }
            guards.push(MultivariableOpenGuardProof {
                guard: guard.clone(),
                operands,
                point_condition,
                point_proof: Box::new(point_proof),
            });
        }
        Ok(Some(MultivariableInteriorProof::OpenGuards {
            domain: domain.clone(),
            base: Box::new(base),
            guards,
        }))
    }
    pub(crate) fn search_multivariable_strategy(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MultivariableStrategyProof>> {
        let AtomicFact::MultivariableAnalysisFact(goal) = goal else {
            return Ok(None);
        };
        let relation = &goal.relation;
        let args = relation.argument_refs();
        let function = args[0];
        let point = args[1];
        let n = input_dimension(relation);
        let Some((source, _)) = self.multivariable_signature_requirements(relation, state)? else {
            return Ok(None);
        };
        let domain = actual_domain(&source.signature).unwrap();
        let Some(geometry) = self.prove_multivariable_interior(&domain, point, &n, state, 0)?
        else {
            return Ok(None);
        };
        let bodies =
            self.exact_property_object_values_of_shapes(function, &[EqualToObjShape::AnonymousFn]);
        for (literal, path) in bodies.into_iter().take(16) {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)) = &literal else {
                continue;
            };
            if !function_domains_alpha_equal(&source.signature, &body.body) {
                continue;
            }
            let parameters: Vec<_> = body
                .body
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .collect();
            if parameters.len() != 1 {
                continue;
            }
            let VerifyObjWellDefinedResult::Success(body_well_defined) =
                self.verify_obj_well_definedness(&literal, state)?
            else {
                continue;
            };
            let Some((coordinates, conclusion_equalities)) =
                self.prove_multivariable_body(relation, body, parameters[0].id, point, &n, state)?
            else {
                continue;
            };
            let stages = SmoothMultivariableStages {
                relation: relation.clone(),
                function_domain: Box::new(source),
                body: body.clone(),
                body_equal: KnownEqualityPathProof::new(path),
                body_well_defined: Box::new(body_well_defined),
                geometry,
                coordinates,
                conclusion_equalities,
            };
            return Ok(Some(match relation {
                MultivariableAnalysisRelation::ScalarLimit(_) => {
                    MultivariableStrategyProof::ScalarLimit(ScalarLimitStrategyProof { stages })
                }
                MultivariableAnalysisRelation::VectorLimit(_) => {
                    MultivariableStrategyProof::VectorLimit(VectorLimitStrategyProof { stages })
                }
                MultivariableAnalysisRelation::ScalarContinuousAt(_) => {
                    MultivariableStrategyProof::ScalarContinuousAt(
                        ScalarContinuousAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::VectorContinuousAt(_) => {
                    MultivariableStrategyProof::VectorContinuousAt(
                        VectorContinuousAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::PartialDerivativeAt(_) => {
                    MultivariableStrategyProof::PartialDerivativeAt(
                        PartialDerivativeAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::SecondPartialDerivativeAt(_) => {
                    MultivariableStrategyProof::SecondPartialDerivativeAt(
                        SecondPartialDerivativeAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::ScalarDifferentialAt(_) => {
                    MultivariableStrategyProof::ScalarDifferentialAt(
                        ScalarDifferentialAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::TotalDerivativeAt(_) => {
                    MultivariableStrategyProof::TotalDerivativeAt(TotalDerivativeAtStrategyProof {
                        stages,
                    })
                }
                MultivariableAnalysisRelation::ScalarDifferentiableAt(_) => {
                    MultivariableStrategyProof::ScalarDifferentiableAt(
                        ScalarDifferentiableAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::TotalDifferentiableAt(_) => {
                    MultivariableStrategyProof::TotalDifferentiableAt(
                        TotalDifferentiableAtStrategyProof { stages },
                    )
                }
                MultivariableAnalysisRelation::GradientAt(_) => {
                    MultivariableStrategyProof::GradientAt(GradientAtStrategyProof { stages })
                }
                MultivariableAnalysisRelation::JacobianAt(_) => {
                    MultivariableStrategyProof::JacobianAt(JacobianAtStrategyProof { stages })
                }
                MultivariableAnalysisRelation::HessianAt(_) => {
                    MultivariableStrategyProof::HessianAt(HessianAtStrategyProof { stages })
                }
                MultivariableAnalysisRelation::DivergenceAt(_) => {
                    MultivariableStrategyProof::DivergenceAt(DivergenceAtStrategyProof { stages })
                }
                MultivariableAnalysisRelation::CurlAt(_) => {
                    MultivariableStrategyProof::CurlAt(CurlAtStrategyProof { stages })
                }
                MultivariableAnalysisRelation::LaplacianAt(_) => {
                    MultivariableStrategyProof::LaplacianAt(LaplacianAtStrategyProof { stages })
                }
            }));
        }
        Ok(None)
    }
    fn prove_multivariable_body(
        &mut self,
        relation: &MultivariableAnalysisRelation,
        body: &AnonymousFn,
        parameter: IdentifierId,
        point: &Obj,
        n: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<
        Option<(
            Vec<MultivariableCoordinateProof>,
            Vec<MultivariableReducedEqualityProof>,
        )>,
    > {
        use MultivariableAnalysisRelation::*;
        let mut requested: Vec<(usize, Obj, Option<Obj>, Option<Obj>)> = Vec::new();
        let mut sum_kind = false;
        let mut curl_kind = false;
        let n_literal = literal_dimension(n);
        let output = function_output_dimension(relation);
        let row_count = match output.as_ref() {
            Some(m) => {
                let Some(m) = literal_dimension(m) else {
                    return Ok(None);
                };
                m
            }
            None => 1,
        };
        match relation {
            PartialDerivativeAt(x) => {
                requested.push((1, x.coordinate.clone(), None, Some(x.value.clone())))
            }
            SecondPartialDerivativeAt(x) => requested.push((
                1,
                x.first_coordinate.clone(),
                Some(x.second_coordinate.clone()),
                Some(x.value.clone()),
            )),
            GradientAt(x) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for k in 1..=count {
                    requested.push((
                        1,
                        number(k as i64),
                        None,
                        Some(apply(&x.value, vec![number(k as i64)])),
                    ));
                }
            }
            HessianAt(x) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for r in 1..=count {
                    for c in 1..=count {
                        requested.push((
                            1,
                            number(r as i64),
                            Some(number(c as i64)),
                            Some(apply(&x.value, vec![number(r as i64), number(c as i64)])),
                        ));
                    }
                }
            }
            ScalarDifferentialAt(x) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for k in 1..=count {
                    requested.push((
                        1,
                        number(k as i64),
                        None,
                        Some(apply(&x.value, vec![number(1), number(k as i64)])),
                    ));
                }
            }
            TotalDerivativeAt(x) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for r in 1..=row_count {
                    for c in 1..=count {
                        requested.push((
                            r,
                            number(c as i64),
                            None,
                            Some(apply(&x.value, vec![number(r as i64), number(c as i64)])),
                        ));
                    }
                }
            }
            JacobianAt(x) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for r in 1..=row_count {
                    for c in 1..=count {
                        requested.push((
                            r,
                            number(c as i64),
                            None,
                            Some(apply(&x.value, vec![number(r as i64), number(c as i64)])),
                        ));
                    }
                }
            }
            DivergenceAt(_) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for k in 1..=count {
                    requested.push((k, number(k as i64), None, None));
                }
                sum_kind = true;
            }
            LaplacianAt(_) => {
                let Some(count) = n_literal else {
                    return Ok(None);
                };
                for k in 1..=count {
                    requested.push((1, number(k as i64), Some(number(k as i64)), None));
                }
                sum_kind = true;
            }
            CurlAt(_) => {
                for (r, c) in [(3, 2), (2, 3), (1, 3), (3, 1), (2, 1), (1, 2)] {
                    requested.push((r, number(c), None, None));
                }
                curl_kind = true;
            }
            // One axis certificate inspects every input-dependent constructor.
            // It certifies smoothness of the entire scalar expression, not only that axis.
            ScalarLimit(_)
            | VectorLimit(_)
            | ScalarContinuousAt(_)
            | VectorContinuousAt(_)
            | ScalarDifferentiableAt(_)
            | TotalDifferentiableAt(_) => {
                for r in 1..=row_count {
                    requested.push((r, number(1), None, None));
                }
            }
        }
        let mut coordinates = Vec::new();
        let mut equalities = Vec::new();
        let mut results = Vec::new();
        let mut budget = 4096;
        for (row, axis, second_axis, target) in requested {
            let raw = if output.is_some() {
                apply(&body.equal_to, vec![number(row as i64)])
            } else {
                *body.equal_to.clone()
            };
            let Some(reduction) = self.reduce_multivariable_expression(&raw, state)? else {
                return Ok(None);
            };
            let Some(first) = self.prove_smooth_coordinate_expression(
                &reduction.result,
                parameter,
                point,
                n,
                &axis,
                state,
                0,
                &mut budget,
            )?
            else {
                return Ok(None);
            };
            let second = if let Some(second_axis) = &second_axis {
                let Some(second) = self.prove_smooth_coordinate_expression(
                    &first.derivative_expression,
                    parameter,
                    point,
                    n,
                    second_axis,
                    state,
                    0,
                    &mut budget,
                )?
                else {
                    return Ok(None);
                };
                Some(second)
            } else {
                None
            };
            let result = second
                .as_ref()
                .map(|p| p.derivative_value.clone())
                .unwrap_or_else(|| first.derivative_value.clone());
            if let Some(target) = target {
                let Some(target_reduced) = self.reduce_multivariable_expression(&target, state)?
                else {
                    return Ok(None);
                };
                let equation = equal(self, result.clone(), target_reduced.result.clone());
                let proof = self.verify_fact(&equation, state)?;
                if proof.is_failed() {
                    return Ok(None);
                }
                equalities.push(MultivariableReducedEqualityProof {
                    target_reduction: target_reduced,
                    equality: Box::new(proof),
                });
            }
            results.push(result);
            coordinates.push(MultivariableCoordinateProof {
                row,
                first_axis: axis,
                second_axis,
                reduction,
                first,
                second,
            });
        }
        let mut conclusions = Vec::new();
        if sum_kind {
            let sum = results.iter().cloned().fold(number(0), add_objs);
            conclusions.push((sum, value(relation).unwrap().clone()));
        }
        if curl_kind {
            for k in 0..3 {
                conclusions.push((
                    sub_objs(results[k * 2].clone(), results[k * 2 + 1].clone()),
                    apply(value(relation).unwrap(), vec![number(k as i64 + 1)]),
                ));
            }
        }
        match relation {
            ScalarLimit(x) => {
                conclusions.push((coordinates[0].first.value.clone(), x.value.clone()))
            }
            VectorLimit(x) => {
                for (i, proof) in coordinates.iter().enumerate() {
                    conclusions.push((
                        proof.first.value.clone(),
                        apply(&x.value, vec![number(i as i64 + 1)]),
                    ));
                }
            }
            _ => {}
        }
        for (left, right) in conclusions {
            let Some(right) = self.reduce_multivariable_expression(&right, state)? else {
                return Ok(None);
            };
            let equation = equal(self, left, right.result.clone());
            let proof = self.verify_fact(&equation, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            equalities.push(MultivariableReducedEqualityProof {
                target_reduction: right,
                equality: Box::new(proof),
            });
        }
        Ok(Some((coordinates, equalities)))
    }
}
