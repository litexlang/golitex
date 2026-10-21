//! Finite relative punctured limits; selection consumes independently proved convergence.
use crate::ast::names::{AtomicName, BoundName};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::*;
use crate::prelude::*;
use crate::rational_expression::helper::sub_objs;

impl Runtime {
    pub(crate) fn verify_function_limit_well_definedness(
        &mut self,
        limit: &FunctionLimit,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let obj: Obj = limit.clone().into();
        let function_wd = match self.verify_obj_well_definedness(&limit.function, state)? {
            VerifyObjWellDefinedResult::Success(p) => p,
            VerifyObjWellDefinedResult::Failed { reason, .. } => {
                return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
            }
        };
        let approach_wd = match limit.approach.point() {
            Some(point) => {
                let point_wd = match self.verify_obj_well_definedness(point, state)? {
                    VerifyObjWellDefinedResult::Success(p) => p,
                    VerifyObjWellDefinedResult::Failed { reason, .. } => {
                        return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
                    }
                };
                FunctionLimitApproachWellDefinedProof::Finite {
                    point_wd: Box::new(point_wd),
                }
            }
            None => match limit.approach {
                LimitApproach::AtPositiveInfinity => {
                    FunctionLimitApproachWellDefinedProof::AtPositiveInfinity
                }
                LimitApproach::AtNegativeInfinity => {
                    FunctionLimitApproachWellDefinedProof::AtNegativeInfinity
                }
                _ => unreachable!("finite approaches have points"),
            },
        };
        let Some(function_domain) =
            self.checked_real_function_limit_domain(&limit.function, state)?
        else {
            return Ok(function_limit_wd_failure(
                obj,
                FunctionLimitWDFailure::Domain,
            ));
        };
        // Preserve the finite pipeline: point WD, checked function domain, then point carrier.
        use super::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof;
        let approach_real = match limit.approach.point() {
            Some(point) => {
                let requirement = self.function_limit_real_member(point.clone());
                let proof = self.verify_fact(&requirement, state)?;
                if proof.is_failed() {
                    return Ok(function_limit_wd_failure(
                        obj,
                        FunctionLimitWDFailure::PointReal(Box::new(proof)),
                    ));
                }
                FunctionLimitApproachRealProof::Finite(Box::new(proof))
            }
            None => match limit.approach {
                LimitApproach::AtPositiveInfinity => {
                    FunctionLimitApproachRealProof::AtPositiveInfinity
                }
                LimitApproach::AtNegativeInfinity => {
                    FunctionLimitApproachRealProof::AtNegativeInfinity
                }
                _ => unreachable!("finite approach has a point"),
            },
        };
        let mut convergence = None;
        for candidate in self.known_function_limit_candidates() {
            let query = self.function_limit_candidate(
                *limit.function.clone(),
                limit.approach.clone(),
                candidate.value,
            );
            if let Some(proof) = self.lookup_known_atomic_premise(query.into()) {
                convergence = Some(FunctionConvergenceProof::Candidate(proof));
                break;
            }
        }
        let convergence = match convergence {
            Some(proof) => proof,
            None => {
                let fact =
                    self.function_limit_existence(*limit.function.clone(), limit.approach.clone());
                let proof = self.verify_fact(&fact, state)?;
                if proof.is_failed() {
                    return Ok(function_limit_wd_failure(
                        obj,
                        FunctionLimitWDFailure::Convergence(Box::new(proof)),
                    ));
                }
                FunctionConvergenceProof::Existence {
                    fact,
                    proof: Box::new(proof),
                }
            }
        };
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj,
                proof: ObjWellDefinedProofByDef::LimitOperator(
                    LimitOperatorObjWellDefinedProofByDef::Function(
                        FunctionLimitObjWellDefinedProof {
                            function_wd: Box::new(function_wd),
                            approach_wd,
                            approach: limit.approach.clone(),
                            function_domain,
                            approach_real,
                            convergence,
                        },
                    ),
                ),
            },
        ))
    }

    // Complete checked signatures are authoritative; a domain view cannot be guessed.
    pub(crate) fn checked_real_function_limit_domain(
        &mut self,
        function: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<RealFunctionLimitDomainProof>> {
        let sources = self.complete_function_domains(function, state)?;
        let mut selected = None;
        for source in sources {
            let parameters: Vec<_> = source
                .signature
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|group| {
                    group
                        .params
                        .iter()
                        .map(move |p| (p, group.param_type.as_ref()))
                })
                .collect();
            if parameters.len() != 1 {
                return Ok(None);
            }
            if let Some(previous) = &selected {
                let previous: &CompleteFunctionDomainProof = previous;
                if !function_domains_alpha_equal(&previous.signature, &source.signature) {
                    return Ok(None);
                }
            } else {
                selected = Some(source);
            }
        }
        let Some(source) = selected else {
            return Ok(None);
        };
        let group = source
            .signature
            .set_bound_parameters
            .groups
            .iter()
            .find(|g| !g.params.is_empty())
            .expect("one parameter");
        let domain = if source.signature.dom_facts.is_empty() {
            *group.param_type.clone()
        } else {
            Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
                param_binding: group.params[0].clone(),
                param_set: group.param_type.clone(),
                facts: source.signature.dom_facts.clone(),
            }))
        };
        let input_fact = self.function_limit_real_subset(*group.param_type.clone());
        let input_real = self.verify_fact(&input_fact, state)?;
        if input_real.is_failed() {
            return Ok(None);
        }
        let output_fact = self.function_limit_real_subset(*source.signature.ret_set.clone());
        let output_real = self.verify_fact(&output_fact, state)?;
        if output_real.is_failed() {
            return Ok(None);
        }
        Ok(Some(RealFunctionLimitDomainProof {
            source: Box::new(source),
            domain,
            input_real: Box::new(input_real),
            output_real: Box::new(output_real),
        }))
    }

    pub(crate) fn known_function_limit_candidates(&self) -> Vec<HasFunctionLimitFact> {
        let mut candidates = Vec::new();
        for name in [
            "has_limit_at",
            "has_limit_left",
            "has_limit_right",
            "has_limit_pos_inf",
            "has_limit_neg_inf",
        ] {
            let key = (AtomicName::Plain { name: name.into() }, true);
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(facts) = env
                    .facts
                    .known_atomic_except_equality_facts
                    .by_prop
                    .get(&key)
                {
                    for fact in facts {
                        if let AtomicFact::HasFunctionLimitFact(f) = fact {
                            candidates.push(f.clone());
                        }
                    }
                }
            }
        }
        candidates
    }

    pub(crate) fn function_limit_candidate(
        &mut self,
        function: Obj,
        approach: LimitApproach,
        value: Obj,
    ) -> HasFunctionLimitFact {
        HasFunctionLimitFact {
            fact_id: self.global_ids.allocate_fact_id(),
            function,
            approach,
            value,
            line_file: None,
        }
    }

    pub(crate) fn function_limit_existence(
        &mut self,
        function: Obj,
        approach: LimitApproach,
    ) -> Fact {
        let l = self.fresh_internal_param();
        let body = self.function_limit_candidate(function, approach, function_limit_identifier(&l));
        function_limit_exists(self, l, real(), vec![body.into()])
    }

    pub(crate) fn function_limit_accumulation(
        &mut self,
        domain: Obj,
        approach: LimitApproach,
    ) -> Fact {
        let r = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        if approach.point().is_none() {
            let beyond = match approach {
                LimitApproach::AtPositiveInfinity => function_limit_less(
                    self,
                    function_limit_identifier(&r),
                    function_limit_identifier(&x),
                ),
                LimitApproach::AtNegativeInfinity => function_limit_less(
                    self,
                    function_limit_identifier(&x),
                    function_limit_identifier(&r),
                ),
                _ => unreachable!("infinity branch"),
            };
            let exists = function_limit_exists(self, x, domain, vec![beyond]);
            return function_limit_forall(self, r, real(), vec![], vec![exists]);
        }
        let distance = approach_distance(function_limit_identifier(&x), &approach);
        let positive = function_limit_less(self, zero(), distance.clone());
        let close = function_limit_less(self, distance, function_limit_identifier(&r));
        let exists = function_limit_exists(self, x, domain, vec![positive, close]);
        function_limit_forall(self, r, positive_real(), vec![], vec![exists])
    }

    pub(crate) fn function_limit_epsilon(
        &mut self,
        function: Obj,
        domain: Obj,
        approach: LimitApproach,
        value: Obj,
    ) -> Fact {
        let epsilon = self.fresh_internal_param();
        let delta = self.fresh_internal_param();
        let threshold_set = approach.threshold_set();
        let inclusion = self.function_limit_control(
            function,
            domain,
            approach,
            value,
            function_limit_identifier(&epsilon),
            function_limit_identifier(&delta),
        );
        let exists = function_limit_exists(self, delta, threshold_set, vec![inclusion]);
        function_limit_forall(self, epsilon, positive_real(), vec![], vec![exists])
    }

    pub(crate) fn function_limit_control(
        &mut self,
        function: Obj,
        domain: Obj,
        approach: LimitApproach,
        value: Obj,
        epsilon: Obj,
        delta: Obj,
    ) -> AtomicFact {
        let neighborhood = self.function_limit_neighborhood(domain, approach, delta);
        let y = self.fresh_internal_param();
        let close = function_limit_less(
            self,
            distance(function_limit_identifier(&y), value),
            epsilon,
        );
        let ball: Obj = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: y,
            param_set: Box::new(real()),
            facts: vec![QuantifierFreeFact::AtomicFact(close)],
        }));
        SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: neighborhood,
            right: PreimageSet::new(function, ball).into(),
            line_file: None,
        }
        .into()
    }

    pub(crate) fn function_limit_neighborhood(
        &mut self,
        domain: Obj,
        approach: LimitApproach,
        radius: Obj,
    ) -> Obj {
        let x = self.fresh_internal_param();
        if approach.point().is_none() {
            let beyond = match approach {
                LimitApproach::AtPositiveInfinity => {
                    function_limit_less(self, radius, function_limit_identifier(&x))
                }
                LimitApproach::AtNegativeInfinity => {
                    function_limit_less(self, function_limit_identifier(&x), radius)
                }
                _ => unreachable!("infinity branch"),
            };
            return Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
                param_binding: x,
                param_set: Box::new(domain),
                facts: vec![QuantifierFreeFact::AtomicFact(beyond)],
            }));
        }
        let d = approach_distance(function_limit_identifier(&x), &approach);
        let positive = function_limit_less(self, zero(), d.clone());
        let close = function_limit_less(self, d, radius);
        Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: x,
            param_set: Box::new(domain),
            facts: vec![QuantifierFreeFact::AndFact(AndFact {
                fact_id: self.global_ids.allocate_fact_id(),
                facts: vec![positive, close],
                line_file: None,
            })],
        }))
    }

    pub(crate) fn function_limit_real_member(&mut self, element: Obj) -> Fact {
        InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element,
            set: real(),
            line_file: None,
        }
        .into()
    }

    fn function_limit_real_subset(&mut self, set: Obj) -> Fact {
        SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: set,
            right: real(),
            line_file: None,
        }
        .into()
    }
}

pub struct RealFunctionLimitDomainProof {
    pub source: Box<CompleteFunctionDomainProof>,
    pub domain: Obj,
    pub input_real: Box<VerifyFactResult>,
    pub output_real: Box<VerifyFactResult>,
}
pub enum FunctionConvergenceProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Existence {
        fact: Fact,
        proof: Box<VerifyFactResult>,
    },
}
pub enum FunctionLimitWDFailure {
    Domain,
    PointReal(Box<VerifyFactResult>),
    Convergence(Box<VerifyFactResult>),
}

fn function_limit_wd_failure(
    obj: Obj,
    reason: FunctionLimitWDFailure,
) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj: obj.clone(),
        reason: FailToVerifyObjWellDefinedResult::LimitOperator(
            FailToVerifyLimitOperatorObjWellDefinedResult::Function(
                FailToVerifyFunctionLimitObjWellDefined { obj, reason },
            ),
        ),
    }
}
pub(crate) fn function_limit_identifier(name: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(name))
}
pub(crate) fn function_limit_typed(name: BoundName, set: Obj) -> TypedParameterList {
    TypedParameterList {
        groups: vec![TypedParameterGroup {
            params: vec![name],
            param_type: ParamType::Obj(set),
        }],
    }
}
pub(crate) fn function_limit_forall(
    rt: &mut Runtime,
    name: BoundName,
    set: Obj,
    dom_facts: Vec<AtomicFact>,
    then: Vec<Fact>,
) -> Fact {
    let then_facts = then
        .into_iter()
        .map(|f| match f {
            Fact::AtomicFact(f) => ExistOrAndChainAtomicFact::AtomicFact(f),
            Fact::ExistFact(f) => ExistOrAndChainAtomicFact::ExistFact(f),
            Fact::ChainFact(f) => ExistOrAndChainAtomicFact::ChainFact(f),
            _ => unreachable!("function limit clauses are atomic or existential"),
        })
        .collect();
    Fact::ForallFact(ForallFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: function_limit_typed(name, set),
        dom_facts: dom_facts.into_iter().map(Into::into).collect(),
        then_facts,
        line_file: None,
    })
}
pub(crate) fn function_limit_exists(
    rt: &mut Runtime,
    name: BoundName,
    set: Obj,
    facts: Vec<AtomicFact>,
) -> Fact {
    let facts = if facts.len() > 1 {
        vec![QuantifierFreeFact::AndFact(AndFact {
            fact_id: rt.global_ids.allocate_fact_id(),
            facts,
            line_file: None,
        })]
    } else {
        facts
            .into_iter()
            .map(QuantifierFreeFact::AtomicFact)
            .collect()
    };
    Fact::ExistFact(PlainExistFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: function_limit_typed(name, set),
        facts,
        line_file: None,
    })
}
pub(crate) fn function_limit_less(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn positive_real() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
fn zero() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }))
}
fn distance(x: Obj, y: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(sub_objs(x, y)),
    }))
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/function_limit_sides/tests.rs"]
mod function_limit_sides_tests;

#[cfg(test)]
#[path = "../../../tests/unit/execute/function_limit/tests.rs"]
mod function_limit_tests;

// A side uses its positive signed displacement; output error always uses abs.
// Example: at x0=0 the left approach is 0 < -x < delta.
fn approach_distance(x: Obj, approach: &LimitApproach) -> Obj {
    match approach {
        LimitApproach::AtPoint(point) => distance(x, *point.clone()),
        LimitApproach::FromLeft(point) => sub_objs(*point.clone(), x),
        LimitApproach::FromRight(point) => sub_objs(x, *point.clone()),
        LimitApproach::AtPositiveInfinity | LimitApproach::AtNegativeInfinity => {
            unreachable!("finite distance requested for infinity")
        }
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/function_limit_infinity/tests.rs"]
mod function_limit_infinity_tests;
