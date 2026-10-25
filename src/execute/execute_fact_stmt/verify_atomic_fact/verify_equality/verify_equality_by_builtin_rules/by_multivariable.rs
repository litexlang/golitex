//! Selection and uniqueness consume known candidates, never compute them.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub enum MultivariableEqualityProof {
    SelectedValue(MultivariableSelectedValueProof),
    SelectedComponent(MultivariableSelectedComponentProof),
    Uniqueness(MultivariableCandidateUniquenessProof),
}
pub struct MultivariableSelectedComponentProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub candidate_value_equal: KnownEqualityPathProof,
    pub reduction:
        crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionProof,
    pub value_equality: Box<VerifyFactResult>,
}
pub struct MultivariableSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
pub struct MultivariableCandidateUniquenessProof {
    pub left: AtomicExceptEqualityFactKnownProof,
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl MultivariableEqualityProof {
    pub fn law(&self) -> &'static str {
        match self {
            Self::SelectedComponent(_) => {
                "A component of a proved Euclidean candidate determines the selected component"
            }
            Self::SelectedValue(_) => {
                "A previously proved Euclidean candidate determines the selected value"
            }
            Self::Uniqueness(_) => {
                "Two candidates for the same Euclidean operation and arguments are equal"
            }
        }
    }
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SelectedComponent(_) => "MultivariableSelectedComponent",
            Self::SelectedValue(_) => "MultivariableSelectedValue",
            Self::Uniqueness(_) => "MultivariableCandidateUniqueness",
        }
    }
}
impl Runtime {
    pub(super) fn search_multivariable_selected_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<MultivariableEqualityProof> {
        for (selected, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if selected.multivariable_selector_name().is_none() {
                continue;
            }
            let Some((established, candidate)) =
                self.known_multivariable_selector_candidate(selected)
            else {
                continue;
            };
            let comparison = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: established,
                right: value.clone(),
                line_file: None,
            };
            if let Some(value_equality) = self.search_equal_fact_proof_directly(&comparison) {
                return Some(MultivariableEqualityProof::SelectedValue(
                    MultivariableSelectedValueProof {
                        candidate,
                        value_equality: Box::new(value_equality),
                    },
                ));
            }
        }
        let mut relations = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for name in crate::execute::execute_fact_stmt::multivariable::helper::CANDIDATE_NAMES {
                let key = (AtomicName::plain((*name).into()), true);
                let Some(facts) = env
                    .facts
                    .known_atomic_except_equality_facts
                    .by_prop
                    .get(&key)
                else {
                    continue;
                };
                for fact in facts {
                    if let AtomicFact::MultivariableAnalysisFact(f) = fact {
                        if crate::execute::execute_fact_stmt::multivariable::helper::value(
                            &f.relation,
                        )
                        .is_some()
                        {
                            relations.push(f.relation.clone());
                        }
                    }
                }
            }
        }
        for relation in relations {
            let mut args: Vec<_> = relation.argument_refs().into_iter().cloned().collect();
            *args.last_mut().unwrap() = fact.left.clone();
            let left: AtomicFact = MultivariableAnalysisFact {
                fact_id: self.global_ids.allocate_fact_id(),
                relation: relation.with_arguments(&args),
                line_file: None,
            }
            .into();
            *args.last_mut().unwrap() = fact.right.clone();
            let right: AtomicFact = MultivariableAnalysisFact {
                fact_id: self.global_ids.allocate_fact_id(),
                relation: relation.with_arguments(&args),
                line_file: None,
            }
            .into();
            if let (Some(left), Some(right)) = (
                self.lookup_known_atomic_premise(left),
                self.lookup_known_atomic_premise(right),
            ) {
                return Some(MultivariableEqualityProof::Uniqueness(
                    MultivariableCandidateUniquenessProof { left, right },
                ));
            }
        }
        None
    }
}

impl Runtime {
    pub(super) fn search_multivariable_component_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MultivariableEqualityProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::FnObj(call) = left else {
                continue;
            };
            let selected =
                crate::execute::execute_fact_stmt::multivariable::expression::call_head(&call.head);
            let Some((value, _)) = self.known_multivariable_selector_candidate(&selected) else {
                continue;
            };
            for (candidate_value, path) in self
                .exact_property_object_values(&value)
                .into_iter()
                .take(16)
            {
                let applied = Obj::FnObj(FnObj {
                    head: Box::new(FnObjHead::from_obj(candidate_value)),
                    body: call.body.clone(),
                });
                let Some(reduction) = self.reduce_multivariable_expression(&applied, state)? else {
                    continue;
                };
                let equation: Fact = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: reduction.result.clone(),
                    right: right.clone(),
                    line_file: None,
                }
                .into();
                let value_equality = self.verify_builtin_rule_premise(&equation, state)?;
                if value_equality.is_failed() {
                    continue;
                }
                let Some((_, candidate)) = self.known_multivariable_selector_candidate(&selected)
                else {
                    continue;
                };
                return Ok(Some(MultivariableEqualityProof::SelectedComponent(
                    MultivariableSelectedComponentProof {
                        candidate,
                        candidate_value_equal: KnownEqualityPathProof::new(path),
                        reduction,
                        value_equality: Box::new(value_equality),
                    },
                )));
            }
        }
        Ok(None)
    }
}
