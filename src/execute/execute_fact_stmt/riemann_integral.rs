//! Finite real oriented Riemann integration; selection consumes proved existence.
#[cfg(test)]
#[path = "../../../tests/unit/execute/riemann_integral/native.rs"]
mod tests;
use super::function_limit::{
    function_limit_exists, function_limit_forall, RealFunctionLimitDomainProof,
};
use super::real_analysis::analysis_apply;
use super::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use super::well_defined_results::verify_obj::*;
use crate::prelude::*;
pub(crate) mod helper;
use helper::*;

pub enum IntegralOperatorWellDefinedProof {
    Riemann(RiemannIntegralWellDefinedProof),
}
pub struct RiemannIntegralWellDefinedProof {
    pub function_wd: Box<ObjWellDefinedProof>,
    pub lower_wd: Box<ObjWellDefinedProof>,
    pub upper_wd: Box<ObjWellDefinedProof>,
    pub domain: Box<RealFunctionLimitDomainProof>,
    pub requirements:
        Vec<super::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof>,
    pub selection: RiemannIntegralSelectionProof,
}
pub enum RiemannIntegralSelectionProof {
    Candidate(AtomicExceptEqualityFactKnownProof),
    Existence {
        fact: Fact,
        proof: Box<VerifyFactResult>,
    },
}
pub enum IntegralOperatorWellDefinedFailure {
    Riemann(RiemannIntegralWellDefinedFailure),
}
pub struct RiemannIntegralWellDefinedFailure {
    pub obj: Obj,
    pub stage: RiemannIntegralFailureStage,
}
pub enum RiemannIntegralFailureStage {
    Domain,
    Requirement {
        requirement: Fact,
        result: Box<VerifyFactResult>,
    },
    Selection(Box<VerifyFactResult>),
}

impl Runtime {
    pub(crate) fn verify_riemann_integral_well_definedness(
        &mut self,
        integral: &RiemannIntegral,
        state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let obj: Obj = integral.clone().into();
        let mut children = Vec::new();
        for child in [&integral.function, &integral.lower, &integral.upper] {
            match self.verify_obj_well_definedness(child, state)? {
                VerifyObjWellDefinedResult::Success(p) => children.push(p),
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(VerifyObjWellDefinedResult::Failed { obj, reason })
                }
            }
        }
        let Some(domain) = self.checked_real_function_limit_domain(&integral.function, state)?
        else {
            return Ok(failure(obj, RiemannIntegralFailureStage::Domain));
        };
        let requirements = self.riemann_domain_requirements(
            *integral.lower.clone(),
            *integral.upper.clone(),
            domain.domain.clone(),
        );
        let mut completed = Vec::new();
        for requirement in requirements {
            let result = self.verify_fact(&requirement, state)?;
            if result.is_failed() {
                return Ok(failure(
                    obj,
                    RiemannIntegralFailureStage::Requirement {
                        requirement,
                        result: Box::new(result),
                    },
                ));
            }
            completed.push(
                super::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof {
                    requirement,
                    result: Box::new(result),
                },
            );
        }
        let mut selection = None;
        for candidate in self.known_riemann_integral_candidates() {
            let query = self.riemann_integral_candidate(
                *integral.function.clone(),
                *integral.lower.clone(),
                *integral.upper.clone(),
                candidate.value,
            );
            if let Some(proof) = self.lookup_known_atomic_premise(query) {
                selection = Some(RiemannIntegralSelectionProof::Candidate(proof));
                break;
            }
        }
        let selection = match selection {
            Some(p) => p,
            None => {
                let fact = self.riemann_integral_existence(
                    *integral.function.clone(),
                    *integral.lower.clone(),
                    *integral.upper.clone(),
                );
                // The selector may consume stored existence, never construct an integral.
                let proof =
                    self.verify_fact(&fact, state.capped_at(VerifyStateLevel::BuiltinRule))?;
                if proof.is_failed() {
                    return Ok(failure(
                        obj,
                        RiemannIntegralFailureStage::Selection(Box::new(proof)),
                    ));
                }
                RiemannIntegralSelectionProof::Existence {
                    fact,
                    proof: Box::new(proof),
                }
            }
        };
        let mut children = children.into_iter();
        Ok(VerifyObjWellDefinedResult::Success(
            ObjWellDefinedProof::ByDef {
                obj,
                proof: ObjWellDefinedProofByDef::IntegralOperator(
                    IntegralOperatorWellDefinedProof::Riemann(RiemannIntegralWellDefinedProof {
                        function_wd: Box::new(children.next().unwrap()),
                        lower_wd: Box::new(children.next().unwrap()),
                        upper_wd: Box::new(children.next().unwrap()),
                        domain: Box::new(domain),
                        requirements: completed,
                        selection,
                    }),
                ),
            },
        ))
    }
    pub(crate) fn riemann_integral_candidate(
        &mut self,
        function: Obj,
        lower: Obj,
        upper: Obj,
        value: Obj,
    ) -> AtomicFact {
        HasRiemannIntegralFact {
            fact_id: self.global_ids.allocate_fact_id(),
            function,
            lower,
            upper,
            value,
            line_file: None,
        }
        .into()
    }
    pub(crate) fn riemann_integrable(
        &mut self,
        function: Obj,
        lower: Obj,
        upper: Obj,
    ) -> AtomicFact {
        FunctionRiemannIntegrableFact {
            fact_id: self.global_ids.allocate_fact_id(),
            function,
            lower,
            upper,
            line_file: None,
        }
        .into()
    }
    pub(crate) fn riemann_integral_existence(
        &mut self,
        function: Obj,
        lower: Obj,
        upper: Obj,
    ) -> Fact {
        let name = self.fresh_internal_param();
        let candidate = self.riemann_integral_candidate(function, lower, upper, id(&name));
        function_limit_exists(self, name, real(), vec![candidate])
    }
    pub(crate) fn known_riemann_integral_candidates(&self) -> Vec<HasRiemannIntegralFact> {
        let key = (AtomicName::plain("has_riemann_integral".into()), true);
        let mut result = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(facts) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for fact in facts {
                    if let AtomicFact::HasRiemannIntegralFact(f) = fact {
                        result.push(f.clone());
                    }
                }
            }
        }
        result
    }
    pub(crate) fn riemann_domain_requirements(&mut self, a: Obj, b: Obj, domain: Obj) -> Vec<Fact> {
        vec![
            member(self, a.clone(), real()).into(),
            member(self, b.clone(), real()).into(),
            subset(self, sorted_interval(a, b), domain).into(),
        ]
    }
    pub(crate) fn riemann_enclosure_signature_requirements(&mut self, args: &[Obj]) -> Vec<Fact> {
        let n = args[3].clone();
        let mut requirements =
            vec![member(self, n.clone(), Obj::StandardSet(StandardSet::NPos)).into()];
        for (index, start) in [(4, "0"), (5, "1"), (6, "1")] {
            let space = function_space(self, num(start), n.clone());
            requirements.push(member(self, args[index].clone(), space).into());
        }
        requirements
    }
    pub(crate) fn riemann_integral_defining_clauses(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        match fact {
            AtomicFact::FunctionRiemannIntegrableFact(f) => Ok(Some(vec![self
                .riemann_integral_existence(
                    f.function.clone(),
                    f.lower.clone(),
                    f.upper.clone(),
                )])),
            AtomicFact::HasRiemannIntegralFact(f) => {
                let Some(domain) = self.checked_real_function_limit_domain(&f.function, state)?
                else {
                    return Ok(None);
                };
                let a = f.lower.clone();
                let b = f.upper.clone();
                let interval = sorted_interval(a.clone(), b.clone());
                let x = self.fresh_internal_param();
                let restricted = literal(
                    x.clone(),
                    interval.clone(),
                    analysis_apply(f.function.clone(), id(&x)),
                );
                let bounded: Fact = RealSetBoundedFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: Obj::FunctionSpace(FunctionSpace::FnRange(FnRange {
                        function: Box::new(restricted),
                    })),
                    boundedness: RealBoundedness::Both,
                    line_file: None,
                }
                .into();
                // One definition: Darboux step-function enclosures of arbitrary precision.
                // Inf/sup sums give these enclosures; conversely every enclosure bounds
                // the lower/upper Darboux integrals. Refinement proves uniqueness.
                // Sorted endpoints handle reversal; the singleton branch requires I=0.
                let zero_guard = eq(self, a.clone(), b.clone());
                let zero_value = eq(self, f.value.clone(), num("0"));
                let nonzero = crate::ast::fact::negate_atomic_fact(
                    &zero_guard,
                    self.global_ids.allocate_fact_id(),
                )
                .expect("equality negation");
                let zero = Fact::OrFact(OrFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    facts: vec![
                        AndChainAtomicFact::AtomicFact(nonzero),
                        AndChainAtomicFact::AtomicFact(zero_value),
                    ],
                    line_file: None,
                });
                let epsilon = self.fresh_internal_param();
                let n = self.fresh_internal_param();
                let p = self.fresh_internal_param();
                let l = self.fresh_internal_param();
                let u = self.fresh_internal_param();
                let lower_sum = self.fresh_internal_param();
                let upper_sum = self.fresh_internal_param();
                let n_obj = id(&n);
                let p_obj = id(&p);
                let l_obj = id(&l);
                let u_obj = id(&u);
                let left = min(a.clone(), b.clone());
                let right = max(a.clone(), b.clone());
                let enclosure = certificate(
                    self,
                    "is_darboux_enclosure",
                    vec![
                        f.function.clone(),
                        left.clone(),
                        right.clone(),
                        n_obj.clone(),
                        p_obj.clone(),
                        l_obj.clone(),
                        u_obj.clone(),
                    ],
                );
                let ls = darboux_sum(self, n_obj.clone(), p_obj.clone(), l_obj);
                let us = darboux_sum(self, n_obj.clone(), p_obj, u_obj);
                // The positive-length branch quantifies over orientation separately.
                let oriented_value =
                    oriented_candidate(self, a.clone(), b.clone(), f.value.clone());
                let lower_equation = eq(self, id(&lower_sum), ls);
                let upper_equation = eq(self, id(&upper_sum), us);
                let bracket_lower = le(self, id(&lower_sum), oriented_value.clone());
                let bracket_upper = le(self, oriented_value, id(&upper_sum));
                let gap = lt(self, sub(id(&upper_sum), id(&lower_sum)), id(&epsilon));
                let witness = Fact::ExistFact(PlainExistFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters: crate::ast::param::TypedParameterList {
                        groups: vec![
                            typed(n, Obj::StandardSet(StandardSet::NPos)),
                            typed(p, function_space(self, num("0"), n_obj.clone())),
                            typed(l, function_space(self, num("1"), n_obj.clone())),
                            typed(u, function_space(self, num("1"), n_obj)),
                            typed(lower_sum, real()),
                            typed(upper_sum, real()),
                        ],
                    },
                    facts: vec![
                        enclosure,
                        lower_equation,
                        upper_equation,
                        bracket_lower,
                        bracket_upper,
                        gap,
                    ]
                    .into_iter()
                    .map(QuantifierFreeFact::AtomicFact)
                    .collect(),
                    line_file: None,
                });
                let positive = lt(self, left, right);
                let epsilon_clause = function_limit_forall(
                    self,
                    epsilon,
                    Obj::StandardSet(StandardSet::RPos),
                    vec![positive],
                    vec![witness],
                );
                let mut clauses = self.riemann_domain_requirements(a, b, domain.domain);
                clauses.extend([bounded, zero, epsilon_clause]);
                Ok(Some(clauses))
            }
            _ => Ok(None),
        }
    }
}
fn failure(obj: Obj, stage: RiemannIntegralFailureStage) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed {
        obj: obj.clone(),
        reason: FailToVerifyObjWellDefinedResult::IntegralOperator(
            IntegralOperatorWellDefinedFailure::Riemann(RiemannIntegralWellDefinedFailure {
                obj,
                stage,
            }),
        ),
    }
}
