//! Complete function domains, read from checked constructions and memberships.
//! This is proof consumption: no new Env state, signature cache or shape tag.

use super::{fn_sets_alpha_equal, ObjWellDefinedProof, VerifyFactResult,
    VerifyObjWellDefinedResult, VerifyState};
use crate::ast::fact::{AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact};
use crate::ast::obj::*;
use crate::ast::param::*;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
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

#[cfg(test)]
#[path = "../../../tests/unit/execute/exact_sequence_composition/tests.rs"]
mod exact_sequence_composition_tests;

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
    Arity { source: usize, target: usize },
    Instantiate(String),
    Forward { fact: Fact, result: Box<VerifyFactResult> },
    Reverse {
        forward: Fact,
        forward_proof: Box<VerifyFactResult>,
        fact: Fact,
        result: Box<VerifyFactResult>,
    },
}

impl Runtime {
    /// Only checked function values supply complete domains. An equality to a
    /// FnSet supplies a set alias, not a function in that space.
    pub(crate) fn complete_function_domains(
        &mut self, function: &Obj, ctx: VerifyState,
    ) -> RuntimeResult<Vec<CompleteFunctionDomainProof>> {
        let adjacency = self.visible_equivalence_class_adjacency();
        let peers = equivalence_class_members_with_paths_in_adjacency(&adjacency, function);
        let mut domains: Vec<_> = self.finite_function_signatures(function).into_iter().map(|source| {
            CompleteFunctionDomainProof { signature: source.signature.clone(),
                source: CompleteFunctionDomainSourceProof::FiniteFunction(Box::new(source)) }
        }).collect();
        let mut seen_memberships = HashSet::new();
        for (peer, path) in peers {
            if let Obj::FnObj(application) = &peer {
                domains.extend(self.complete_application_return_domains(application, &path, ctx)?);
            }
            if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = &peer {
                domains.push(CompleteFunctionDomainProof {
                    signature: anon.body.clone(),
                    source: CompleteFunctionDomainSourceProof::AnonymousFunction {
                        function: anon.clone(),
                        subject_equal: KnownEqualityPathProof::new(path.clone()),
                    },
                });
            }
            if let Obj::InstantiatedTemplateObj(instance) = &peer {
                if let Some(signature) = self.instantiated_template_function_signature(instance) {
                    if let VerifyObjWellDefinedResult::Success(instance_wd) = self.verify_obj_well_definedness(&peer, ctx)? {
                        domains.push(CompleteFunctionDomainProof {
                            signature,
                            source: CompleteFunctionDomainSourceProof::TemplateDefinition {
                                instance: instance.clone(), instance_wd,
                                subject_equal: KnownEqualityPathProof::new(path.clone()),
                            },
                        });
                    }
                }
            }
            let memberships: Vec<_> = self.execution_environments_stack.iter().rev()
                .filter_map(|env| env.special_properties.get(&peer.ir()))
                .flat_map(|properties| properties.iter())
                .filter_map(|property| match property {
                    SpecialProperty::Membership(fact) => Some(fact.clone()),
                    _ => None,
                }).collect();
            for membership in memberships {
                if !seen_memberships.insert(membership.fact_id) { continue; }
                let Some(subject_path) = self.equivalence_class_path(function, &membership.element)
                else { continue; };
                let carriers = equivalence_class_members_with_paths_in_adjacency(
                    &adjacency, &membership.set,
                );
                for (carrier, carrier_path) in carriers {
                    let Some(signature) = self.function_space_signature(&carrier) else { continue; };
                    domains.push(CompleteFunctionDomainProof {
                        signature,
                        source: CompleteFunctionDomainSourceProof::Membership {
                            membership: membership.clone(),
                            subject_equal: KnownEqualityPathProof::new(subject_path.clone()),
                            carrier_equal: KnownEqualityPathProof::new(carrier_path),
                        },
                    });
                }
            }
        }
        Ok(domains)
    }

    fn complete_application_return_domains(
        &mut self, application: &FnObj,
        path: &[(Obj, Obj, crate::runtime::FactId)], ctx: VerifyState,
    ) -> RuntimeResult<Vec<CompleteFunctionDomainProof>> {
        let head = match application.head.as_ref() {
            FnObjHead::Identifier(head) => Obj::Identifier(head.clone()),
            FnObjHead::AnonymousFnLiteral(function) => Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone())),
            FnObjHead::FieldAccess(access) => Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone())),
            FnObjHead::InstantiatedTemplateObj(instance) => Obj::InstantiatedTemplateObj(instance.clone()),
        };
        let mut signatures = Vec::new();
        if let FnObjHead::AnonymousFnLiteral(function) = application.head.as_ref() {
            signatures.push((function.body.clone(), FnObjDomainFnSetEvidence::AnonymousLiteral {
                fn_set: function.body.clone(),
            }, vec![]));
        }
        for (peer, function_path) in equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(), &head,
        ) {
            let Obj::InstantiatedTemplateObj(instance) = &peer else { continue; };
            let Some(signature) = self.instantiated_template_function_signature(instance) else { continue; };
            let VerifyObjWellDefinedResult::Success(head_wd) = self.verify_obj_well_definedness(&peer, ctx)? else { continue; };
            signatures.push((signature.clone(), FnObjDomainFnSetEvidence::TemplateDefinition {
                fn_set: signature, function_equal: KnownEqualityPathProof::new(function_path),
            }, vec![Box::new(head_wd)]));
        }
        for (signature, fact_id) in self.collect_in_function_set_candidates(&head) {
            let subject = match self.fact_by_id_in_stack(fact_id) {
                Some(Fact::AtomicFact(AtomicFact::InFact(fact))) => Some(fact.element.clone()),
                Some(Fact::AtomicFact(AtomicFact::EqualFact(fact))) =>
                    SpecialProperty::Equality(fact.clone()).function_subject().cloned(),
                _ => None,
            };
            let Some(subject) = subject else { continue; };
            let Some(function_path) = self.equivalence_class_path(&head, &subject) else { continue; };
            signatures.push((signature.clone(), FnObjDomainFnSetEvidence::InFunctionSet {
                fn_set: signature, fact_id,
                function_equal: KnownEqualityPathProof::new(function_path),
            }, vec![]));
        }
        let mut domains = Vec::new();
        for (signature, signature_source, mut head_children) in signatures {
            // Returning a function space gives an exact domain only after
            // this actual application satisfies the selected input/guards.
            let Some(return_space) = self.applied_fn_set_return_set(application, &signature) else { continue; };
            let return_peers = equivalence_class_members_with_paths_in_adjacency(
                &self.visible_equivalence_class_adjacency(), &return_space,
            );
            let Some((carrier, carrier_path)) = return_peers.into_iter().find(|(carrier, _)| {
                matches!(carrier, Obj::FunctionSpace(FunctionSpace::FnSet(_))
                    | Obj::SetFormer(SetFormer::SeqSet(_) | SetFormer::FiniteSeqSet(_)))
            }) else { continue; };
            let Some(return_signature) = self.function_space_signature(&carrier) else { continue; };
            let Ok(applicability) = self.try_verify_fn_obj_against_fn_set(application, &signature, ctx)?
            else { continue; };
            let (application_children, application_requirements) = applicability.into_success_child_proofs();
            head_children.extend(application_children);
            domains.push(CompleteFunctionDomainProof {
                signature: return_signature,
                source: CompleteFunctionDomainSourceProof::ApplicationReturn {
                    application: application.clone(), subject_equal: KnownEqualityPathProof::new(path.to_vec()),
                    signature_source, application_children: head_children, application_requirements, return_space,
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
            Obj::SetFormer(SetFormer::SeqSet(sequence)) =>
                (Obj::StandardSet(StandardSet::NPos), sequence.set.clone()),
            Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) => (
                Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
                    start: Box::new(Obj::Literal(Literal::Number(Number {
                        normalized_value: "1".to_string(),
                    }))), end: sequence.n.clone(),
                })), sequence.set.clone(),
            ),
            _ => return None,
        };
        Some(FnSet {
            set_bound_parameters: SetBoundParameterList { groups: vec![SetBoundParameterGroup {
                params: vec![self.fresh_internal_param()], param_type: Box::new(domain),
            }] }, dom_facts: vec![], ret_set,
        })
    }

    /// A function-valued result belongs to this checked return carrier.
    /// Resolve its existing set aliases before the next application layer.
    /// The caller's WD must retain carrier equality when unfolding an alias.
    /// This is not evidence that the carrier set itself is a function value.
    pub(crate) fn returned_function_signature(&mut self, space: &Obj) -> Option<(FnSet, Obj)> {
        let peers = equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(), space,
        );
        for (carrier, _) in peers {
            let signature = match &carrier {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => Some(function.body.clone()),
                Obj::ProductShape(ProductShape::Cart(cart)) => Some(self.cart_function_signature(cart)),
                _ => self.function_space_signature(&carrier),
            };
            if let Some(signature) = signature { return Some((signature, carrier)); }
        }
        None
    }

    pub(crate) fn verify_complete_function_domain(
        &mut self, function: &Obj, target: &FnSet, ctx: VerifyState,
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
        if sources.is_empty() { return Ok(Err(FunctionDomainMatchFailure::NoCompleteDomain)); }
        let mut failures = Vec::new();
        for source in sources {
            match self.verify_function_domain_equivalence(&source.signature, target, ctx)? {
                Ok(comparison) => return Ok(Ok(FunctionDomainMatchProof {
                    function_wd, target_wd, source, target: target.clone(), comparison,
                })),
                Err(comparison) => failures.push(FunctionDomainCandidateFailure { source, comparison }),
            }
        }
        Ok(Err(FunctionDomainMatchFailure::Candidates(failures)))
    }

    fn verify_function_domain_equivalence(
        &mut self, source: &FnSet, target: &FnSet, ctx: VerifyState,
    ) -> RuntimeResult<Result<FunctionDomainComparisonProof, FunctionDomainComparisonFailure>> {
        // Compare binder/guard alpha identity independently of return bounds.
        // The original full FnSet equality helper keeps its original contract.
        if function_domains_alpha_equal(source, target) {
            return Ok(Ok(FunctionDomainComparisonProof::AlphaEquivalent));
        }
        let source_count: usize = source.set_bound_parameters.groups.iter().map(|g| g.params.len()).sum();
        let target_count: usize = target.set_bound_parameters.groups.iter().map(|g| g.params.len()).sum();
        if source_count != target_count {
            return Ok(Err(FunctionDomainComparisonFailure::Arity { source: source_count, target: target_count }));
        }
        let forward = match self.build_function_domain_inclusion(source, target) {
            Ok(fact) => fact, Err(message) => return Ok(Err(FunctionDomainComparisonFailure::Instantiate(message))),
        };
        let forward_proof = self.verify_fact(&forward, ctx)?;
        if forward_proof.is_failed() {
            return Ok(Err(FunctionDomainComparisonFailure::Forward { fact: forward, result: Box::new(forward_proof) }));
        }
        let reverse = match self.build_function_domain_inclusion(target, source) {
            Ok(fact) => fact, Err(message) => return Ok(Err(FunctionDomainComparisonFailure::Instantiate(message))),
        };
        let reverse_proof = self.verify_fact(&reverse, ctx)?;
        if reverse_proof.is_failed() {
            return Ok(Err(FunctionDomainComparisonFailure::Reverse {
                forward, forward_proof: Box::new(forward_proof), fact: reverse, result: Box::new(reverse_proof),
            }));
        }
        Ok(Ok(FunctionDomainComparisonProof::MutualInclusion {
            forward, forward_proof: Box::new(forward_proof), reverse, reverse_proof: Box::new(reverse_proof),
        }))
    }

    fn build_function_domain_inclusion(&mut self, source: &FnSet, target: &FnSet) -> Result<Fact, String> {
        let mut source_subst = HashMap::new();
        let mut target_subst = HashMap::new();
        let mut groups = Vec::new();
        let target_bindings: Vec<_> = target.set_bound_parameters.groups.iter()
            .flat_map(|g| g.params.iter()).collect();
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
            let carrier = self.inst_obj(&group.param_type, &source_subst).map_err(|e| e.to_string())?;
            groups.push(TypedParameterGroup { params, param_type: ParamType::Obj(carrier) });
        }
        let mut dom_facts = Vec::new();
        for guard in &source.dom_facts {
            dom_facts.push(quantifier_free_fact_to_fact(
                self.inst_quantifier_free_fact(guard, &source_subst).map_err(|e| e.to_string())?,
            ));
        }
        let mut then_facts = Vec::new();
        for group in &target.set_bound_parameters.groups {
            let carrier = self.inst_obj(&group.param_type, &target_subst).map_err(|e| e.to_string())?;
            for old in &group.params {
                then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(), element: target_subst[&old.id].clone(),
                    set: carrier.clone(), line_file: None,
                })));
            }
        }
        for guard in &target.dom_facts {
            let fact = quantifier_free_fact_to_fact(
                self.inst_quantifier_free_fact(guard, &target_subst).map_err(|e| e.to_string())?,
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
            fact_id: self.global_ids.allocate_fact_id(), typed_parameters: TypedParameterList { groups },
            dom_facts, then_facts, line_file: None,
        }))
    }

    pub(crate) fn build_function_return_forall(&mut self, function: &Obj, target: &FnSet) -> Result<Fact, String> {
        let mut groups = Vec::new();
        let mut arguments = Vec::new();
        for group in &target.set_bound_parameters.groups {
            groups.push(TypedParameterGroup {
                params: group.params.clone(), param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            });
            arguments.extend(group.params.iter().map(|p| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(p)))));
        }
        let value = function_application(function, arguments)?;
        Ok(Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(), typed_parameters: TypedParameterList { groups },
            dom_facts: target.dom_facts.iter().cloned().map(quantifier_free_fact_to_fact).collect(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(), element: value,
                set: target.ret_set.as_ref().clone(), line_file: None,
            }))], line_file: None,
        }))
    }

    pub(crate) fn build_function_return_requirements(&mut self, function: &Obj, target: &FnSet) -> Result<Vec<Fact>, String> {
        // Fixed coordinates are the literal graph's complete return values.
        // Domain matching is a separate prior proof; no vacuous coordinate
        // list may certify a nonempty-domain function as an empty function.
        if let Some(value) = self.known_literal_tuple_candidates(function).into_iter().next() {
            return Ok(value.value.args.into_iter().map(|element| AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(), element: *element,
                set: target.ret_set.as_ref().clone(), line_file: None,
            }).into()).collect());
        }
        Ok(vec![self.build_function_return_forall(function, target)?])
    }
}

pub(crate) fn function_application(function: &Obj, arguments: Vec<Box<Obj>>) -> Result<Obj, String> {
    if let Obj::FnObj(call) = function {
        let mut call = call.clone(); call.body.push(arguments); return Ok(Obj::FnObj(call));
    }
    let head = match function {
        Obj::Identifier(x) => FnObjHead::Identifier(x.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(x)) => FnObjHead::AnonymousFnLiteral(Box::new(x.clone())),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x)) => FnObjHead::FieldAccess(x.clone()),
        Obj::InstantiatedTemplateObj(x) => FnObjHead::InstantiatedTemplateObj(x.clone()),
        _ => return Err("expected a callable function object".into()),
    };
    Ok(Obj::FnObj(FnObj { head: Box::new(head), body: vec![arguments] }))
}
