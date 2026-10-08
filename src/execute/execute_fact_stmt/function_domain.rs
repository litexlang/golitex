//! Complete function domains, read from checked constructions and memberships.
//! This is proof consumption: no new Env state, signature cache or shape tag.

use super::{fn_sets_alpha_equal, ObjWellDefinedProof, VerifyFactResult,
    VerifyObjWellDefinedResult, VerifyState};
use crate::ast::fact::{negate_atomic_fact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, IsNonemptySetFact, LessEqualFact, LessFact, PlainExistFact, QuantifierFreeFact};
use crate::ast::obj::*;
use crate::ast::param::*;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::helper::set_bound_params_to_arg_map;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{Runtime, RuntimeResult};
use super::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use std::collections::{HashMap, HashSet};

pub(crate) fn function_domains_alpha_equal(source: &FnSet, target: &FnSet) -> bool {
    let mut source_domain = source.clone();
    let mut target_domain = target.clone();
    source_domain.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
    target_domain.ret_set = source_domain.ret_set.clone();
    fn_sets_alpha_equal(&source_domain, &target_domain)
}

pub struct FunctionCallDomainsAlphaMatchProof {
    pub layers: Vec<FunctionCallLayerDomainsAlphaMatchProof>,
}

pub struct FunctionCallLayerDomainsAlphaMatchProof {
    pub selected: FnSet,
    pub alternative: FnSet,
    pub return_carriers: Option<FunctionCallReturnCarriersProof>,
}

pub struct FunctionCallReturnCarriersProof {
    pub selected_equal: KnownEqualityPathProof,
    pub alternative_equal: KnownEqualityPathProof,
}

pub enum FunctionDomainEmptyProof {
    ParameterCarrier(FunctionDomainEmptyCarrierProof),
    GuardExclusion(FunctionDomainGuardExclusionProof),
}

pub struct FunctionDomainEmptyCarrierProof {
    pub signature: FnSet,
    pub parameter_group_index: usize,
    pub empty_carrier: Obj,
    pub carrier_equal: KnownEqualityPathProof,
    pub evidence: FunctionDomainEmptyCarrierEvidence,
}

pub enum FunctionDomainEmptyCarrierEvidence {
    EmptyList,
    EmptyIntegerRange,
    CheckedEquality(Box<VerifyFactResult>),
}

pub struct FunctionDomainGuardExclusionProof {
    pub signature: FnSet,
    pub excluded_guard_index: usize,
    // Typed assignments satisfying every other guard exclude this guard.
    // The forall result retains its fresh binders, WD and scoped evidence.
    pub exclusion: Box<VerifyFactResult>,
}

pub struct FunctionDomainNonemptyProof {
    pub signature: FnSet,
    pub evidence: FunctionDomainNonemptyEvidence,
}

pub enum FunctionDomainNonemptyEvidence {
    ParameterCarriers(Vec<VerifyFactResult>),
    ArgumentWitness {
        arguments: Vec<Obj>,
        memberships: Vec<FunctionDomainArgumentMembershipProof>,
        guards: Vec<VerifyFactResult>,
    },
    ExistingWitness(Box<VerifyFactResult>),
}

pub enum FunctionDomainArgumentMembershipProof {
    Verified(Box<VerifyFactResult>),
    IntegerRangeStart {
        integer: Box<VerifyFactResult>,
        endpoint_order: Box<VerifyFactResult>,
    },
}

pub enum FunctionSpaceNonemptyProof {
    BaseSet(Box<VerifyFactResult>),
    EmptyDomain(FunctionDomainEmptyProof),
    CarrierTransport {
        carrier: Obj,
        carrier_equal: KnownEqualityPathProof,
        nonempty: Box<FunctionSpaceNonemptyProof>,
    },
    FiniteCartesianProduct {
        cart: Cart,
        factors_nonempty: Vec<FunctionSpaceNonemptyProof>,
    },
    ConstantFunction {
        signature: FnSet,
        return_nonempty: Box<FunctionSpaceNonemptyProof>,
    },
}

impl Runtime {
    /// Constructive constant-function existence follows smaller return spaces
    /// and checked carrier equalities. Cycles cannot supply their own witness.
    pub(crate) fn verify_nonempty_function_space_return(
        &mut self,
        carrier: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<FunctionSpaceNonemptyProof>> {
        self.verify_nonempty_function_space_return_inner(carrier, state, &mut HashSet::new())
    }

    fn verify_nonempty_function_space_return_inner(
        &mut self,
        carrier: &Obj,
        state: VerifyState,
        active: &mut HashSet<crate::display_and_ir::ObjIR>,
    ) -> RuntimeResult<Option<FunctionSpaceNonemptyProof>> {
        let key = carrier.ir();
        if !active.insert(key.clone()) {
            return Ok(None);
        }
        let peers = self.exact_property_object_values(carrier);
        let mut result = None;
        for (peer, path) in peers {
            let proof = if let Some(signature) = self.function_space_signature(&peer) {
                if let Some(proof) = self.verify_function_domain_empty(&signature, state)? {
                    Some(FunctionSpaceNonemptyProof::EmptyDomain(proof))
                } else {
                    self.verify_nonempty_function_space_return_inner(
                        &signature.ret_set,
                        state,
                        active,
                    )?
                    .map(|return_nonempty| {
                        FunctionSpaceNonemptyProof::ConstantFunction {
                            signature,
                            return_nonempty: Box::new(return_nonempty),
                        }
                    })
                }
            } else if let Obj::ProductShape(ProductShape::Cart(cart)) = &peer {
                let mut factors_nonempty = Vec::new();
                for factor in &cart.args {
                    let Some(proof) =
                        self.verify_nonempty_function_space_return_inner(factor, state, active)?
                    else {
                        break;
                    };
                    factors_nonempty.push(proof);
                }
                if factors_nonempty.len() == cart.args.len() {
                    Some(FunctionSpaceNonemptyProof::FiniteCartesianProduct {
                        cart: cart.clone(),
                        factors_nonempty,
                    })
                } else {
                    None
                }
            } else {
                let nonempty: Fact = AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: peer.clone(),
                    line_file: None,
                })
                .into();
                let proof = self.verify_fact(&nonempty, state)?;
                if proof.is_failed() {
                    None
                } else {
                    Some(FunctionSpaceNonemptyProof::BaseSet(Box::new(proof)))
                }
            };
            if let Some(proof) = proof {
                result = Some(if path.is_empty() {
                    proof
                } else {
                    FunctionSpaceNonemptyProof::CarrierTransport {
                        carrier: peer,
                        carrier_equal: KnownEqualityPathProof::new(path),
                        nonempty: Box::new(proof),
                    }
                });
                break;
            }
        }
        active.remove(&key);
        Ok(result)
    }

    /// A used empty carrier, or a checked exclusion of one required guard,
    /// leaves no complete input assignment. Empty parameter lists instead
    /// form the unit input; only their actual guards may exclude that input.
    pub(crate) fn verify_function_domain_empty(
        &mut self,
        signature: &FnSet,
        state: VerifyState,
    ) -> RuntimeResult<Option<FunctionDomainEmptyProof>> {
        for (index, group) in signature.set_bound_parameters.groups.iter().enumerate() {
            if group.params.is_empty() {
                continue;
            }
            let peers = self.exact_property_object_values(&group.param_type);
            for (carrier, path) in peers {
                let evidence = match &carrier {
                    Obj::SetFormer(SetFormer::ListSet(set)) if set.list.is_empty() => {
                        Some(FunctionDomainEmptyCarrierEvidence::EmptyList)
                    }
                    Obj::SetFormer(SetFormer::ClosedRange(range))
                        if integer_endpoints_are_empty(&range.start, &range.end, false) =>
                    {
                        Some(FunctionDomainEmptyCarrierEvidence::EmptyIntegerRange)
                    }
                    Obj::SetFormer(SetFormer::Range(range))
                        if integer_endpoints_are_empty(&range.start, &range.end, true) =>
                    {
                        Some(FunctionDomainEmptyCarrierEvidence::EmptyIntegerRange)
                    }
                    _ => None,
                };
                if let Some(evidence) = evidence {
                    return Ok(Some(FunctionDomainEmptyProof::ParameterCarrier(
                        FunctionDomainEmptyCarrierProof {
                            signature: signature.clone(),
                            parameter_group_index: index,
                            empty_carrier: carrier,
                            carrier_equal: KnownEqualityPathProof::new(path),
                            evidence,
                        },
                    )));
                }
            }
            let empty = Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] }));
            let equality: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *group.param_type.clone(),
                right: empty,
                line_file: None,
            }
            .into();
            let proof = self.verify_fact(&equality, state)?;
            if !proof.is_failed() {
                return Ok(Some(FunctionDomainEmptyProof::ParameterCarrier(
                    FunctionDomainEmptyCarrierProof {
                        signature: signature.clone(),
                        parameter_group_index: index,
                        empty_carrier: *group.param_type.clone(),
                        carrier_equal: KnownEqualityPathProof::new(vec![]),
                        evidence: FunctionDomainEmptyCarrierEvidence::CheckedEquality(Box::new(
                            proof,
                        )),
                    },
                )));
            }
        }
        // Never assume the guard we are excluding. A successful universal
        // proves that the conjunction of ALL input guards has no assignment.
        // Its local assumptions are discarded by the existing forall owner.
        for excluded_guard_index in 0..signature.dom_facts.len() {
            let Ok(Some(exclusion)) =
                self.build_function_guard_exclusion(signature, excluded_guard_index)
            else {
                continue;
            };
            let proof = self.verify_forall_fact(&exclusion, state)?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(FunctionDomainEmptyProof::GuardExclusion(
                FunctionDomainGuardExclusionProof {
                    signature: signature.clone(),
                    excluded_guard_index,
                    exclusion: Box::new(proof),
                },
            )));
        }
        Ok(None)
    }

    fn build_function_guard_exclusion(
        &mut self,
        signature: &FnSet,
        excluded_guard_index: usize,
    ) -> Result<Option<ForallFact>, String> {
        let QuantifierFreeFact::AtomicFact(excluded) = &signature.dom_facts[excluded_guard_index]
        else {
            return Ok(None);
        };
        let mut subst = HashMap::new();
        let mut groups = Vec::new();
        for group in &signature.set_bound_parameters.groups {
            let mut params = Vec::new();
            for original in &group.params {
                let fresh = self.fresh_internal_param();
                subst.insert(
                    original.id,
                    Obj::Identifier(IdentifierObj::from_bound_name(&fresh)),
                );
                params.push(fresh);
            }
            let carrier = self
                .inst_obj(&group.param_type, &subst)
                .map_err(|e| e.to_string())?;
            groups.push(TypedParameterGroup {
                params,
                param_type: ParamType::Obj(carrier),
            });
        }
        let excluded = self
            .inst_atomic_fact(excluded, &subst)
            .map_err(|e| e.to_string())?;
        let Some(negated) = negate_atomic_fact(&excluded, self.global_ids.allocate_fact_id())
        else {
            return Ok(None);
        };
        let mut dom_facts = Vec::new();
        for (index, guard) in signature.dom_facts.iter().enumerate() {
            if index == excluded_guard_index {
                continue;
            }
            let instantiated = self
                .inst_quantifier_free_fact(guard, &subst)
                .map_err(|e| e.to_string())?;
            dom_facts.push(quantifier_free_fact_to_fact(instantiated));
        }
        Ok(Some(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList { groups },
            dom_facts,
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(negated)],
            line_file: None,
        }))
    }

    /// Certify an actual input, or the finite product of nonempty carriers.
    /// Every child keeps the caller's already restricted search permissions.
    pub(crate) fn verify_function_domain_nonempty(
        &mut self,
        signature: &FnSet,
        state: VerifyState,
    ) -> RuntimeResult<Option<FunctionDomainNonemptyProof>> {
        if signature.dom_facts.is_empty() {
            let mut proofs = Vec::new();
            let mut all_nonempty = true;
            for group in &signature.set_bound_parameters.groups {
                if group.params.is_empty() {
                    continue;
                }
                let fact: Fact = AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: *group.param_type.clone(),
                    line_file: None,
                })
                .into();
                let proof = self.verify_fact(&fact, state)?;
                if proof.is_failed() {
                    all_nonempty = false;
                    break;
                }
                proofs.push(proof);
            }
            if all_nonempty {
                return Ok(Some(FunctionDomainNonemptyProof {
                    signature: signature.clone(),
                    evidence: FunctionDomainNonemptyEvidence::ParameterCarriers(proofs),
                }));
            }
        }
        let mut arguments = Vec::new();
        let mut memberships = Vec::new();
        let mut substitution = HashMap::new();
        let mut witness_complete = true;
        for group in &signature.set_bound_parameters.groups {
            for parameter in &group.params {
                let argument = match group.param_type.as_ref() {
                    Obj::StandardSet(set) => Obj::Literal(Literal::Number(Number {
                        normalized_value: if *set == StandardSet::NPos { "1" } else { "0" }.into(),
                    })),
                    Obj::SetFormer(SetFormer::ListSet(set)) if !set.list.is_empty() => {
                        *set.list[0].clone()
                    }
                    Obj::SetFormer(SetFormer::ClosedRange(range)) => *range.start.clone(),
                    Obj::SetFormer(SetFormer::Range(range)) => *range.start.clone(),
                    _ => {
                        witness_complete = false;
                        break;
                    }
                };
                let membership: Fact = AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: argument.clone(),
                    set: *group.param_type.clone(),
                    line_file: None,
                })
                .into();
                let proof = self.verify_fact(&membership, state)?;
                let membership_proof = if !proof.is_failed() {
                    FunctionDomainArgumentMembershipProof::Verified(Box::new(proof))
                } else {
                    let endpoint_order: Fact = match group.param_type.as_ref() {
                        Obj::SetFormer(SetFormer::ClosedRange(range)) => {
                            AtomicFact::LessEqualFact(LessEqualFact {
                                fact_id: self.global_ids.allocate_fact_id(),
                                left: argument.clone(),
                                right: *range.end.clone(),
                                line_file: None,
                            })
                            .into()
                        }
                        Obj::SetFormer(SetFormer::Range(range)) => AtomicFact::LessFact(LessFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: argument.clone(),
                            right: *range.end.clone(),
                            line_file: None,
                        })
                        .into(),
                        _ => {
                            witness_complete = false;
                            break;
                        }
                    };
                    let integer: Fact = AtomicFact::InFact(InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: argument.clone(),
                        set: Obj::StandardSet(StandardSet::Z),
                        line_file: None,
                    })
                    .into();
                    let integer = self.verify_fact(&integer, state)?;
                    let endpoint_order = self.verify_fact(&endpoint_order, state)?;
                    if integer.is_failed() || endpoint_order.is_failed() {
                        witness_complete = false;
                        break;
                    }
                    FunctionDomainArgumentMembershipProof::IntegerRangeStart {
                        integer: Box::new(integer),
                        endpoint_order: Box::new(endpoint_order),
                    }
                };
                substitution.insert(parameter.id, argument.clone());
                arguments.push(argument);
                memberships.push(membership_proof);
            }
            if !witness_complete {
                break;
            }
        }
        if witness_complete {
            let mut guards = Vec::new();
            for guard in &signature.dom_facts {
                let guard = match self.inst_quantifier_free_fact(guard, &substitution) {
                    Ok(guard) => quantifier_free_fact_to_fact(guard),
                    Err(_) => {
                        witness_complete = false;
                        break;
                    }
                };
                let proof = self.verify_fact(&guard, state)?;
                if proof.is_failed() {
                    witness_complete = false;
                    break;
                }
                guards.push(proof);
            }
            if witness_complete {
                return Ok(Some(FunctionDomainNonemptyProof {
                    signature: signature.clone(),
                    evidence: FunctionDomainNonemptyEvidence::ArgumentWitness {
                        arguments,
                        memberships,
                        guards,
                    },
                }));
            }
        }
        if !signature.dom_facts.is_empty() {
            let witness = Fact::ExistFact(PlainExistFact {
                fact_id: self.global_ids.allocate_fact_id(),
                typed_parameters: TypedParameterList {
                    groups: signature
                        .set_bound_parameters
                        .groups
                        .iter()
                        .map(|group| TypedParameterGroup {
                            params: group.params.clone(),
                            param_type: ParamType::Obj(*group.param_type.clone()),
                        })
                        .collect(),
                },
                facts: signature.dom_facts.clone(),
                line_file: None,
            });
            let proof = self.verify_fact(&witness, state)?;
            if !proof.is_failed() {
                return Ok(Some(FunctionDomainNonemptyProof {
                    signature: signature.clone(),
                    evidence: FunctionDomainNonemptyEvidence::ExistingWitness(Box::new(proof)),
                }));
            }
        }
        Ok(None)
    }
}

fn integer_endpoints_are_empty(start: &Obj, end: &Obj, half_open: bool) -> bool {
    let (Obj::Literal(Literal::Number(start)), Obj::Literal(Literal::Number(end))) = (start, end)
    else {
        return false;
    };
    let (Ok(start), Ok(end)) = (
        start.normalized_value.parse::<i128>(),
        end.normalized_value.parse::<i128>(),
    ) else {
        return false;
    };
    if half_open {
        start >= end
    } else {
        start > end
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/exact_sequence_composition/tests.rs"]
mod exact_sequence_composition_tests;

#[cfg(test)]
#[path = "../../../tests/unit/execute/function_domain_graph/tests.rs"]
mod function_domain_graph_tests;

pub struct FunctionDomainMatchProof {
    pub function_wd: ObjWellDefinedProof,
    pub target_wd: ObjWellDefinedProof,
    pub source: CompleteFunctionDomainProof,
    pub target: FnSet,
    pub comparison: FunctionDomainComparisonProof,
}

pub struct CompleteFunctionDomainProof {
    pub signature: FnSet,
    pub source: CompleteFunctionDomainSourceProof,
}

pub enum CompleteFunctionDomainSourceProof {
    FiniteFunction(Box<super::finite_function::FiniteFunctionSignatureProof>),
    AnonymousFunction {
        function: AnonymousFn,
        subject_equal: KnownEqualityPathProof,
    },
    TemplateDefinition {
        instance: InstantiatedTemplateObj,
        instance_wd: ObjWellDefinedProof,
        subject_equal: KnownEqualityPathProof,
    },
    Membership {
        membership: InFact,
        subject_equal: KnownEqualityPathProof,
        carrier_equal: KnownEqualityPathProof,
    },
    ApplicationReturn {
        application: FnObj,
        subject_equal: KnownEqualityPathProof,
        signature_source: FnObjDomainFnSetEvidence,
        application_children: Vec<Box<ObjWellDefinedProof>>,
        application_requirements: Vec<VerifyFactResult>,
        return_space: Obj,
        carrier_equal: KnownEqualityPathProof,
    },
}

pub enum FunctionDomainComparisonProof {
    AlphaEquivalent,
    MutualInclusion {
        forward: Fact,
        forward_proof: Box<VerifyFactResult>,
        reverse: Fact,
        reverse_proof: Box<VerifyFactResult>,
    },
}

pub enum FunctionDomainMatchFailure {
    FunctionWd(VerifyObjWellDefinedResult),
    TargetWd(VerifyObjWellDefinedResult),
    NoCompleteDomain,
    Candidates(Vec<FunctionDomainCandidateFailure>),
}

pub struct FunctionDomainCandidateFailure {
    pub source: CompleteFunctionDomainProof,
    pub comparison: FunctionDomainComparisonFailure,
}

pub enum FunctionDomainComparisonFailure {
    Arity {
        source: usize,
        target: usize,
    },
    Instantiate(String),
    Forward {
        fact: Fact,
        result: Box<VerifyFactResult>,
    },
    Reverse {
        forward: Fact,
        forward_proof: Box<VerifyFactResult>,
        fact: Fact,
        result: Box<VerifyFactResult>,
    },
}

impl Runtime {
    // Cached application WD does not name the selected signature. Reusing
    // it for another return upper bound is safe only when each call layer
    // has the same parameters and guards. Return bounds themselves may differ.
    // This consumes checked aliases; it neither searches for new domain facts
    // nor flattens curried or nested function spaces.
    pub(crate) fn function_call_domains_alpha_match(
        &mut self,
        application: &FnObj,
        selected: &FnSet,
        alternative: &FnSet,
    ) -> Option<FunctionCallDomainsAlphaMatchProof> {
        let last = application.body.len().checked_sub(1)?;
        let mut selected = selected.clone();
        let mut alternative = alternative.clone();
        let mut layers = Vec::new();
        for (index, arguments) in application.body.iter().enumerate() {
            let arguments: Vec<_> = arguments.iter().map(|arg| arg.as_ref().clone()).collect();
            let arity: usize = selected
                .set_bound_parameters
                .groups
                .iter()
                .map(|group| group.params.len())
                .sum();
            if arguments.len() != arity || !function_domains_alpha_equal(&selected, &alternative) {
                return None;
            }
            let mut layer = FunctionCallLayerDomainsAlphaMatchProof {
                selected: selected.clone(),
                alternative: alternative.clone(),
                return_carriers: None,
            };
            if index < last {
                let selected_map =
                    set_bound_params_to_arg_map(&selected.set_bound_parameters, &arguments);
                let alternative_map =
                    set_bound_params_to_arg_map(&alternative.set_bound_parameters, &arguments);
                let selected_return = self
                    .inst_obj(selected.ret_set.as_ref(), &selected_map)
                    .ok()?;
                let alternative_return = self
                    .inst_obj(alternative.ret_set.as_ref(), &alternative_map)
                    .ok()?;
                let (next_selected, selected_carrier) =
                    self.returned_function_signature(&selected_return)?;
                let (next_alternative, alternative_carrier) =
                    self.returned_function_signature(&alternative_return)?;
                layer.return_carriers = Some(FunctionCallReturnCarriersProof {
                    selected_equal: KnownEqualityPathProof::new(
                        self.exact_property_equality_path(&selected_return, &selected_carrier)?,
                    ),
                    alternative_equal: KnownEqualityPathProof::new(
                        self.exact_property_equality_path(
                            &alternative_return,
                            &alternative_carrier,
                        )?,
                    ),
                });
                selected = next_selected;
                alternative = next_alternative;
            }
            layers.push(layer);
        }
        Some(FunctionCallDomainsAlphaMatchProof { layers })
    }

    /// Only checked function values supply complete domains. An equality to a
    /// FnSet supplies a set alias, not a function in that space.
    pub(crate) fn complete_function_domains(
        &mut self,
        function: &Obj,
        ctx: VerifyState,
    ) -> RuntimeResult<Vec<CompleteFunctionDomainProof>> {
        let mut domains: Vec<_> = self
            .finite_function_signatures(function)
            .into_iter()
            .map(|source| CompleteFunctionDomainProof {
                signature: source.signature.clone(),
                source: CompleteFunctionDomainSourceProof::FiniteFunction(Box::new(source)),
            })
            .collect();
        for (value, path) in self.exact_property_object_values(function) {
            if let Obj::FnObj(application) = &value {
                domains.extend(self.complete_application_return_domains(
                    application,
                    &path,
                    ctx,
                )?);
            }
            if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = &value {
                domains.push(CompleteFunctionDomainProof {
                    signature: anon.body.clone(),
                    source: CompleteFunctionDomainSourceProof::AnonymousFunction {
                        function: anon.clone(),
                        subject_equal: KnownEqualityPathProof::new(path.clone()),
                    },
                });
            }
            if let Obj::InstantiatedTemplateObj(instance) = &value {
                if let Some(signature) = self.instantiated_template_function_signature(instance) {
                    if let VerifyObjWellDefinedResult::Success(instance_wd) =
                        self.verify_obj_well_definedness(&value, ctx)?
                    {
                        domains.push(CompleteFunctionDomainProof {
                            signature,
                            source: CompleteFunctionDomainSourceProof::TemplateDefinition {
                                instance: instance.clone(),
                                instance_wd,
                                subject_equal: KnownEqualityPathProof::new(path.clone()),
                            },
                        });
                    }
                }
            }
        }
        // Do not read a neighbor's memberships: exact-subject properties are
        // the authority for complete domains, including checked space aliases.
        let mut seen_memberships = HashSet::new();
        for property in self.known_special_properties_of(function) {
            let SpecialProperty::Membership(membership) = property else {
                continue;
            };
            if !seen_memberships.insert(membership.fact_id) {
                continue;
            }
            for (carrier, carrier_path) in self.exact_property_object_values(&membership.set) {
                let Some(signature) = self.function_space_signature(&carrier) else {
                    continue;
                };
                domains.push(CompleteFunctionDomainProof {
                    signature,
                    source: CompleteFunctionDomainSourceProof::Membership {
                        membership: membership.clone(),
                        subject_equal: KnownEqualityPathProof::new(vec![]),
                        carrier_equal: KnownEqualityPathProof::new(carrier_path),
                    },
                });
            }
        }
        Ok(domains)
    }

    fn complete_application_return_domains(
        &mut self,
        application: &FnObj,
        path: &[(Obj, Obj, crate::runtime::FactId)],
        ctx: VerifyState,
    ) -> RuntimeResult<Vec<CompleteFunctionDomainProof>> {
        let head = match application.head.as_ref() {
            FnObjHead::Object(obj) => obj.as_ref().clone(),
            FnObjHead::Identifier(head) => Obj::Identifier(head.clone()),
            FnObjHead::AnonymousFnLiteral(function) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone()))
            }
            FnObjHead::FieldAccess(access) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()))
            }
            FnObjHead::InstantiatedTemplateObj(instance) => {
                Obj::InstantiatedTemplateObj(instance.clone())
            }
        };
        let mut signatures = Vec::new();
        if let FnObjHead::AnonymousFnLiteral(function) = application.head.as_ref() {
            signatures.push((
                function.body.clone(),
                FnObjDomainFnSetEvidence::AnonymousLiteral {
                    fn_set: function.body.clone(),
                },
                vec![],
            ));
        }
        for (peer, function_path) in self.exact_property_object_values(&head) {
            let Obj::InstantiatedTemplateObj(instance) = &peer else {
                continue;
            };
            let Some(signature) = self.instantiated_template_function_signature(instance) else {
                continue;
            };
            let VerifyObjWellDefinedResult::Success(head_wd) =
                self.verify_obj_well_definedness(&peer, ctx)?
            else {
                continue;
            };
            signatures.push((
                signature.clone(),
                FnObjDomainFnSetEvidence::TemplateDefinition {
                    fn_set: signature,
                    function_equal: KnownEqualityPathProof::new(function_path),
                },
                vec![Box::new(head_wd)],
            ));
        }
        for (signature, fact_id) in self.collect_in_function_set_candidates(&head) {
            let subject = match self.fact_by_id_in_stack(fact_id) {
                Some(Fact::AtomicFact(AtomicFact::InFact(fact))) => Some(fact.element.clone()),
                Some(Fact::AtomicFact(AtomicFact::EqualFact(fact))) => {
                    SpecialProperty::Equality(fact.clone())
                        .function_subject()
                        .cloned()
                }
                _ => None,
            };
            let Some(subject) = subject else {
                continue;
            };
            let Some(function_path) = self.exact_property_equality_path(&head, &subject) else {
                continue;
            };
            signatures.push((
                signature.clone(),
                FnObjDomainFnSetEvidence::InFunctionSet {
                    fn_set: signature,
                    fact_id,
                    function_equal: KnownEqualityPathProof::new(function_path),
                },
                vec![],
            ));
        }
        let mut domains = Vec::new();
        for (signature, signature_source, mut head_children) in signatures {
            // Returning a function space gives an exact domain only after
            // this actual application satisfies the selected input/guards.
            let Some(return_space) = self.applied_fn_set_return_set(application, &signature) else {
                continue;
            };
            let return_peers = self.exact_property_object_values(&return_space);
            let Some((carrier, carrier_path)) = return_peers.into_iter().find(|(carrier, _)| {
                matches!(
                    carrier,
                    Obj::FunctionSpace(FunctionSpace::FnSet(_))
                        | Obj::SetFormer(SetFormer::SeqSet(_) | SetFormer::FiniteSeqSet(_))
                )
            }) else {
                continue;
            };
            let Some(return_signature) = self.function_space_signature(&carrier) else {
                continue;
            };
            let Ok(applicability) =
                self.try_verify_fn_obj_against_fn_set(application, &signature, ctx)?
            else {
                continue;
            };
            let (application_children, application_requirements) =
                applicability.into_success_child_proofs();
            head_children.extend(application_children);
            domains.push(CompleteFunctionDomainProof {
                signature: return_signature,
                source: CompleteFunctionDomainSourceProof::ApplicationReturn {
                    application: application.clone(),
                    subject_equal: KnownEqualityPathProof::new(path.to_vec()),
                    signature_source,
                    application_children: head_children,
                    application_requirements,
                    return_space,
                    carrier_equal: KnownEqualityPathProof::new(carrier_path),
                },
            });
        }
        Ok(domains)
    }

    /// The same exact signature represents ordinary and sequence spaces.
    /// Return carriers remain upper bounds; they do not identify a function.
    pub(crate) fn function_space_signature(&mut self, space: &Obj) -> Option<FnSet> {
        let (domain, ret_set) = match space {
            Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => return Some(signature.clone()),
            Obj::SetFormer(SetFormer::SeqSet(sequence)) => {
                (Obj::StandardSet(StandardSet::NPos), sequence.set.clone())
            }
            Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) => (
                Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
                    start: Box::new(Obj::Literal(Literal::Number(Number {
                        normalized_value: "1".to_string(),
                    }))),
                    end: sequence.n.clone(),
                })),
                sequence.set.clone(),
            ),
            _ => return None,
        };
        Some(FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![self.fresh_internal_param()],
                    param_type: Box::new(domain),
                }],
            },
            dom_facts: vec![],
            ret_set,
        })
    }

    /// A function-valued result belongs to this checked return carrier.
    /// Resolve its existing set aliases before the next application layer.
    /// The caller's WD must retain carrier equality when unfolding an alias.
    /// This is not evidence that the carrier set itself is a function value.
    pub(crate) fn returned_function_signature(&mut self, space: &Obj) -> Option<(FnSet, Obj)> {
        let peers = self.exact_property_object_values(space);
        for (carrier, _) in peers {
            let signature = match &carrier {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                    Some(function.body.clone())
                }
                Obj::ProductShape(ProductShape::Cart(cart)) => {
                    Some(self.cart_function_signature(cart))
                }
                _ => self.function_space_signature(&carrier),
            };
            if let Some(signature) = signature {
                return Some((signature, carrier));
            }
        }
        None
    }

    pub(crate) fn verify_complete_function_domain(
        &mut self,
        function: &Obj,
        target: &FnSet,
        ctx: VerifyState,
    ) -> RuntimeResult<Result<FunctionDomainMatchProof, FunctionDomainMatchFailure>> {
        let function_wd = match self.verify_obj_well_definedness(function, ctx)? {
            VerifyObjWellDefinedResult::Success(proof) => proof,
            failed => return Ok(Err(FunctionDomainMatchFailure::FunctionWd(failed))),
        };
        let target_obj = Obj::FunctionSpace(FunctionSpace::FnSet(target.clone()));
        let target_wd = match self.verify_obj_well_definedness(&target_obj, ctx)? {
            VerifyObjWellDefinedResult::Success(proof) => proof,
            failed => return Ok(Err(FunctionDomainMatchFailure::TargetWd(failed))),
        };
        let sources = self.complete_function_domains(function, ctx)?;
        if sources.is_empty() {
            return Ok(Err(FunctionDomainMatchFailure::NoCompleteDomain));
        }
        let mut failures = Vec::new();
        for source in sources {
            match self.verify_function_domain_equivalence(&source.signature, target, ctx)? {
                Ok(comparison) => {
                    return Ok(Ok(FunctionDomainMatchProof {
                        function_wd,
                        target_wd,
                        source,
                        target: target.clone(),
                        comparison,
                    }))
                }
                Err(comparison) => {
                    failures.push(FunctionDomainCandidateFailure { source, comparison })
                }
            }
        }
        Ok(Err(FunctionDomainMatchFailure::Candidates(failures)))
    }

    fn verify_function_domain_equivalence(
        &mut self,
        source: &FnSet,
        target: &FnSet,
        ctx: VerifyState,
    ) -> RuntimeResult<Result<FunctionDomainComparisonProof, FunctionDomainComparisonFailure>> {
        // Compare binder/guard alpha identity independently of return bounds.
        // The original full FnSet equality helper keeps its original contract.
        if function_domains_alpha_equal(source, target) {
            return Ok(Ok(FunctionDomainComparisonProof::AlphaEquivalent));
        }
        let source_count: usize = source
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum();
        let target_count: usize = target
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum();
        if source_count != target_count {
            return Ok(Err(FunctionDomainComparisonFailure::Arity {
                source: source_count,
                target: target_count,
            }));
        }
        let forward = match self.build_function_domain_inclusion(source, target) {
            Ok(fact) => fact,
            Err(message) => return Ok(Err(FunctionDomainComparisonFailure::Instantiate(message))),
        };
        let forward_proof = self.verify_fact(&forward, ctx)?;
        if forward_proof.is_failed() {
            return Ok(Err(FunctionDomainComparisonFailure::Forward {
                fact: forward,
                result: Box::new(forward_proof),
            }));
        }
        let reverse = match self.build_function_domain_inclusion(target, source) {
            Ok(fact) => fact,
            Err(message) => return Ok(Err(FunctionDomainComparisonFailure::Instantiate(message))),
        };
        let reverse_proof = self.verify_fact(&reverse, ctx)?;
        if reverse_proof.is_failed() {
            return Ok(Err(FunctionDomainComparisonFailure::Reverse {
                forward,
                forward_proof: Box::new(forward_proof),
                fact: reverse,
                result: Box::new(reverse_proof),
            }));
        }
        Ok(Ok(FunctionDomainComparisonProof::MutualInclusion {
            forward,
            forward_proof: Box::new(forward_proof),
            reverse,
            reverse_proof: Box::new(reverse_proof),
        }))
    }

    fn build_function_domain_inclusion(
        &mut self,
        source: &FnSet,
        target: &FnSet,
    ) -> Result<Fact, String> {
        let mut source_subst = HashMap::new();
        let mut target_subst = HashMap::new();
        let mut groups = Vec::new();
        let target_bindings: Vec<_> = target
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter())
            .collect();
        let mut index = 0;
        for group in &source.set_bound_parameters.groups {
            let mut params = Vec::new();
            for old in &group.params {
                let fresh = self.fresh_internal_param();
                let value = Obj::Identifier(IdentifierObj::from_bound_name(&fresh));
                source_subst.insert(old.id, value.clone());
                target_subst.insert(target_bindings[index].id, value);
                index += 1;
                params.push(fresh);
            }
            let carrier = self
                .inst_obj(&group.param_type, &source_subst)
                .map_err(|e| e.to_string())?;
            groups.push(TypedParameterGroup {
                params,
                param_type: ParamType::Obj(carrier),
            });
        }
        let mut dom_facts = Vec::new();
        for guard in &source.dom_facts {
            dom_facts.push(quantifier_free_fact_to_fact(
                self.inst_quantifier_free_fact(guard, &source_subst)
                    .map_err(|e| e.to_string())?,
            ));
        }
        let mut then_facts = Vec::new();
        for group in &target.set_bound_parameters.groups {
            let carrier = self
                .inst_obj(&group.param_type, &target_subst)
                .map_err(|e| e.to_string())?;
            for old in &group.params {
                then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                    InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: target_subst[&old.id].clone(),
                        set: carrier.clone(),
                        line_file: None,
                    },
                )));
            }
        }
        for guard in &target.dom_facts {
            let fact = quantifier_free_fact_to_fact(
                self.inst_quantifier_free_fact(guard, &target_subst)
                    .map_err(|e| e.to_string())?,
            );
            then_facts.push(match fact {
                Fact::AtomicFact(f) => ExistOrAndChainAtomicFact::AtomicFact(f),
                Fact::AndFact(f) => ExistOrAndChainAtomicFact::AndFact(f),
                Fact::ChainFact(f) => ExistOrAndChainAtomicFact::ChainFact(f),
                Fact::OrFact(f) => ExistOrAndChainAtomicFact::OrFact(f),
                _ => unreachable!("quantifier-free domain guard"),
            });
        }
        Ok(Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList { groups },
            dom_facts,
            then_facts,
            line_file: None,
        }))
    }

    pub(crate) fn build_function_return_forall(
        &mut self,
        function: &Obj,
        target: &FnSet,
    ) -> Result<Fact, String> {
        let mut groups = Vec::new();
        let mut arguments = Vec::new();
        for group in &target.set_bound_parameters.groups {
            groups.push(TypedParameterGroup {
                params: group.params.clone(),
                param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            });
            arguments.extend(
                group
                    .params
                    .iter()
                    .map(|p| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(p)))),
            );
        }
        let value = function_application(function, arguments)?;
        Ok(Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList { groups },
            dom_facts: target
                .dom_facts
                .iter()
                .cloned()
                .map(quantifier_free_fact_to_fact)
                .collect(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: value,
                    set: target.ret_set.as_ref().clone(),
                    line_file: None,
                },
            ))],
            line_file: None,
        }))
    }

    pub(crate) fn build_function_return_requirements(
        &mut self,
        function: &Obj,
        target: &FnSet,
    ) -> Result<Vec<Fact>, String> {
        // Fixed coordinates are the literal graph's complete return values.
        // Domain matching is a separate prior proof; no vacuous coordinate
        // list may certify a nonempty-domain function as an empty function.
        if let Some(value) = self
            .known_literal_tuple_candidates(function)
            .into_iter()
            .next()
        {
            return Ok(value
                .value
                .args
                .into_iter()
                .map(|element| {
                    AtomicFact::InFact(InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: *element,
                        set: target.ret_set.as_ref().clone(),
                        line_file: None,
                    })
                    .into()
                })
                .collect());
        }
        Ok(vec![self.build_function_return_forall(function, target)?])
    }
}

pub(crate) fn function_application(
    function: &Obj,
    arguments: Vec<Box<Obj>>,
) -> Result<Obj, String> {
    if let Obj::FnObj(call) = function {
        let mut call = call.clone();
        call.body.push(arguments);
        return Ok(Obj::FnObj(call));
    }
    let head = match function {
        Obj::Identifier(x) => FnObjHead::Identifier(x.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(x)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(x.clone()))
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x)) => {
            FnObjHead::FieldAccess(x.clone())
        }
        Obj::InstantiatedTemplateObj(x) => FnObjHead::InstantiatedTemplateObj(x.clone()),
        other => FnObjHead::Object(Box::new(other.clone())),
    };
    Ok(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![arguments],
    }))
}
