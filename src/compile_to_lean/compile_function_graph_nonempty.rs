//! Replay the original inhabited complete domain of the selected function graph.
use super::compile_function_template::function_guard_fact;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::{
    CompleteFunctionDomainSourceProof, FunctionDomainArgumentMembershipProof as A,
    FunctionDomainNonemptyEvidence as E, FunctionDomainNonemptyProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionGraphNonemptyFromDomainStrategySingleStep;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_graph_nonempty(
        &self,
        goal: &AtomicFact,
        proof: &FunctionGraphNonemptyFromDomainStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsNonemptySetFact(goal) = goal else {
            return Err(invalid("Goal"));
        };
        if proof.source.signature != proof.domain_nonempty.signature {
            return Err(invalid("OriginalSignature"));
        }
        let signature = &proof.source.signature;
        let ids: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        if ids.is_empty() || ids.iter().collect::<HashSet<_>>().len() != ids.len() {
            return Err(invalid("ParameterIdentity"));
        }
        let original_carrier = match &proof.source.source {
            CompleteFunctionDomainSourceProof::Membership {
                membership,
                carrier_equal,
                ..
            } => Some((&membership.set, carrier_equal)),
            CompleteFunctionDomainSourceProof::ApplicationReturn {
                return_space,
                carrier_equal,
                ..
            } => Some((return_space, carrier_equal)),
            _ => None,
        };
        if let Some((carrier, carrier_equal)) = original_carrier {
            let endpoint = carrier_equal
                .path
                .last()
                .map(|(_, to, _)| to)
                .unwrap_or(carrier);
            if let Obj::FunctionSpace(FunctionSpace::FnSet(actual)) = endpoint {
                if actual.ir() != signature.ir()
                    || actual.set_bound_parameters != signature.set_bound_parameters
                    || actual
                        .dom_facts
                        .iter()
                        .map(function_guard_fact)
                        .collect::<Result<Vec<_>, _>>()?
                        != signature
                            .dom_facts
                            .iter()
                            .map(function_guard_fact)
                            .collect::<Result<Vec<_>, _>>()?
                {
                    return Err(invalid("MembershipSignature"));
                }
            }
        }
        let member = self.compile_complete_domain_member(&goal.set, &proof.source, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::CompleteDomainSource(&proof.source),
            usize::MAX,
        );
        let semantic = self.compile_complete_domain_signature(&proof.source, &formed)?;
        let function = self.compile_object_reference(&goal.set, &formed)?;
        let inhabited =
            self.compile_function_domain_nonempty(&proof.domain_nonempty, position, &formed)?;
        Ok(format!(
            "(Litex.functionGraphNonemptyOfDomain {function} {semantic} {member} {inhabited})"
        ))
    }

    pub(in crate::compile_to_lean) fn compile_function_domain_nonempty(
        &self,
        proof: &FunctionDomainNonemptyProof,
        position: &SourcePosition<'_>,
        formed: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = &proof.signature;
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
            .collect();
        let mut lines = Vec::new();
        let (terms, certificates) = match &proof.evidence {
            E::ParameterCarriers(children) => {
                let groups: Vec<_> = signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .filter(|g| !g.params.is_empty())
                    .collect();
                if !signature.dom_facts.is_empty() || groups.len() != children.len() {
                    return Err(invalid("CarrierProofCount"));
                }
                let mut terms = Vec::new();
                let mut members = Vec::new();
                for (index, (group, child)) in groups.into_iter().zip(children).enumerate() {
                    if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==group.param_type.ir())
                    {
                        return Err(invalid("CarrierProofSubject"));
                    }
                    let prior = position.search_verify_prior(child)?;
                    let checked = self.compile_verify(child, &prior)?.1;
                    lines.push(format!("obtain ⟨_graph_carrier_{index}, _graph_carrier_member_{index}⟩ := {checked}"));
                    let object = format!("(Litex.semanticObject _graph_carrier_{index} (M.member_isSet _graph_carrier_member_{index}))");
                    for _ in &group.params {
                        terms.push(object.clone());
                        members.push(format!("_graph_carrier_member_{index}"));
                    }
                }
                (terms, members)
            }
            E::ArgumentWitness {
                arguments,
                memberships,
                guards,
            } => {
                if arguments.len() != parameters.len()
                    || memberships.len() != parameters.len()
                    || guards.len() != signature.dom_facts.len()
                {
                    return Err(invalid("WitnessProofCount"));
                }
                let substitution: HashMap<_, _> = parameters
                    .iter()
                    .zip(arguments)
                    .map(|((p, _), a)| (p.id, a.clone()))
                    .collect();
                let mut terms = Vec::new();
                let mut certificates = Vec::new();
                for ((argument, evidence), (_, carrier)) in
                    arguments.iter().zip(memberships).zip(&parameters)
                {
                    let checked = match evidence {
                        A::Verified(child) => {
                            if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::InFact(f))
                                if f.element.ir()==argument.ir() && instantiated_object_matches(carrier,&f.set,&substitution))
                            {
                                return Err(invalid("ArgumentMembershipSubject"));
                            }
                            self.compile_verify(child, &position.search_verify_prior(child)?)?
                                .1
                        }
                        A::IntegerRangeStart {
                            integer,
                            endpoint_order,
                        } => {
                            let (start, end, closed) = match carrier {
                                Obj::SetFormer(SetFormer::ClosedRange(r)) => {
                                    (r.start.as_ref(), r.end.as_ref(), true)
                                }
                                Obj::SetFormer(SetFormer::Range(r)) => {
                                    (r.start.as_ref(), r.end.as_ref(), false)
                                }
                                _ => return Err(invalid("RangeStartCarrier")),
                            };
                            if !instantiated_object_matches(start, argument, &substitution)
                                || !matches!(source_subject(integer)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==argument.ir() && f.set==Obj::StandardSet(StandardSet::Z))
                            {
                                return Err(invalid("RangeStartInteger"));
                            }
                            let ordered = source_subject(endpoint_order)?;
                            let valid = match &ordered {
                                Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if closed => {
                                    f.left.ir() == argument.ir()
                                        && instantiated_object_matches(end, &f.right, &substitution)
                                }
                                Fact::AtomicFact(AtomicFact::LessFact(f)) if !closed => {
                                    f.left.ir() == argument.ir()
                                        && instantiated_object_matches(end, &f.right, &substitution)
                                }
                                _ => false,
                            };
                            if !valid {
                                return Err(invalid("RangeStartOrder"));
                            }
                            let hi = self
                                .compile_verify(integer, &position.search_verify_prior(integer)?)?
                                .1;
                            let ho = self
                                .compile_verify(
                                    endpoint_order,
                                    &position.search_verify_prior(endpoint_order)?,
                                )?
                                .1;
                            let range = self.compile_object_reference(carrier, position)?;
                            let law = if closed {
                                "closedRangeStartMember"
                            } else {
                                "rangeStartMember"
                            };
                            format!("(Litex.{law} {range} {hi} {ho})")
                        }
                    };
                    // The child's original formation has now become visible.
                    let complete = match evidence {
                        A::Verified(child) => {
                            let prior = position.search_verify_prior(child)?;
                            SourcePosition {
                                before: prior.before + 1,
                                ..prior
                            }
                        }
                        A::IntegerRangeStart { endpoint_order, .. } => {
                            let prior = position.search_verify_prior(endpoint_order)?;
                            SourcePosition {
                                before: prior.before + 1,
                                ..prior
                            }
                        }
                    };
                    terms.push(self.compile_object_reference(argument, &complete)?);
                    certificates.push(checked);
                }
                for (guard, child) in signature.dom_facts.iter().zip(guards) {
                    if !instantiated_fact_matches(
                        &function_guard_fact(guard)?,
                        &source_subject(child)?,
                        &substitution,
                    ) {
                        return Err(invalid("ArgumentGuardSubject"));
                    }
                    certificates.push(
                        self.compile_verify(child, &position.search_verify_prior(child)?)?
                            .1,
                    );
                }
                (terms, certificates)
            }
            E::ExistingWitness(child) => {
                let Fact::ExistFact(witness) = source_subject(child)? else {
                    return Err(invalid("ExistingWitnessSubject"));
                };
                if witness.typed_parameters.groups.len()
                    != signature.set_bound_parameters.groups.len()
                    || witness.facts.len() != signature.dom_facts.len()
                    || witness.facts.is_empty()
                {
                    return Err(invalid("ExistingWitnessShape"));
                }
                for (actual, expected) in witness
                    .typed_parameters
                    .groups
                    .iter()
                    .zip(&signature.set_bound_parameters.groups)
                {
                    if actual.params != expected.params
                        || actual.param_type != ParamType::Obj(*expected.param_type.clone())
                    {
                        return Err(invalid("ExistingWitnessParameters"));
                    }
                }
                for (actual, expected) in witness.facts.iter().zip(&signature.dom_facts) {
                    if function_guard_fact(actual)? != function_guard_fact(expected)? {
                        return Err(invalid("ExistingWitnessGuards"));
                    }
                }
                let checked = self
                    .compile_verify(child, &position.search_verify_prior(child)?)?
                    .1;
                let mut pattern = Vec::new();
                let mut terms = Vec::new();
                let mut certificates = Vec::new();
                for index in 0..parameters.len() {
                    let name = format!("_graph_witness_{index}");
                    let member = format!("_graph_witness_member_{index}");
                    pattern.extend([name.clone(), member.clone()]);
                    terms.push(name);
                    certificates.push(member);
                }
                for index in 0..witness.facts.len() {
                    let guard = format!("_graph_witness_guard_{index}");
                    pattern.push(guard.clone());
                    certificates.push(guard);
                }
                lines.push(format!("obtain ⟨{}⟩ := {checked}", pattern.join(", ")));
                (terms, certificates)
            }
        };
        let (input, member) =
            self.compile_complete_input(signature, &terms, &certificates, formed)?;
        lines.push(format!("exact ⟨{input}, {member}⟩"));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}

fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FunctionGraphNonempty/{part}"))
}
