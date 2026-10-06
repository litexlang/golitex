//! Complete-domain certificates and failed comparison stages.
use super::searched::project_known_equality_path;
use super::verify::project_verify_fact;
use super::wd::{project_obj_wd_proof, project_verify_obj_wd};
use crate::ast::obj::{FunctionSpace, Obj};
use crate::execute::execute_fact_stmt::function_domain::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

fn signature(signature: &crate::ast::obj::FnSet) -> JsonValue {
    string(Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())).readable_string())
}

pub(super) fn project_domain_empty(proof: &FunctionDomainEmptyProof, rt: &Runtime) -> JsonValue {
    match proof {
        FunctionDomainEmptyProof::ParameterCarrier(proof) => project_empty_parameter_carrier(proof, rt),
        FunctionDomainEmptyProof::GuardExclusion(proof) => object_for(rt, vec![
            ("type", string("checked_guard_input_exclusion")),
            ("source_signature", signature(&proof.signature)),
            ("excluded_guard_index", string(proof.excluded_guard_index.to_string())),
            ("guard_exclusion", project_verify_fact(&proof.exclusion, rt)),
        ]),
    }
}

fn project_empty_parameter_carrier(proof: &FunctionDomainEmptyCarrierProof, rt: &Runtime) -> JsonValue {
    let evidence = match &proof.evidence {
        FunctionDomainEmptyCarrierEvidence::EmptyList => object_for(rt, vec![("type", string("empty_literal_carrier"))]),
        FunctionDomainEmptyCarrierEvidence::EmptyIntegerRange => object_for(rt, vec![("type", string("empty_integer_range_carrier"))]),
        FunctionDomainEmptyCarrierEvidence::CheckedEquality(result) => project_verify_fact(result, rt),
    };
    object_for(rt, vec![
        ("source_signature", signature(&proof.signature)),
        ("parameter_group_index", string(proof.parameter_group_index.to_string())),
        ("empty_carrier", string(proof.empty_carrier.readable_string())),
        ("carrier_equal", project_known_equality_path(&proof.carrier_equal, rt)),
        ("source", evidence),
    ])
}

pub(super) fn project_domain_nonempty(proof: &FunctionDomainNonemptyProof, rt: &Runtime) -> JsonValue {
    let evidence = match &proof.evidence {
        FunctionDomainNonemptyEvidence::ParameterCarriers(proofs) => object_for(rt, vec![
            ("type", string("nonempty_parameter_product")),
            ("proof_of_requirement_facts", super::store::project_verify_facts(proofs, rt)),
        ]),
        FunctionDomainNonemptyEvidence::ArgumentWitness { arguments, memberships, guards } => object_for(rt, vec![
            ("type", string("checked_domain_argument_witness")),
            ("arguments", JsonValue::Array(arguments.iter().map(|arg| string(arg.readable_string())).collect())),
            ("proof_of_requirement_facts", JsonValue::Array(memberships.iter().map(|proof| match proof {
                FunctionDomainArgumentMembershipProof::Verified(proof) => project_verify_fact(proof, rt),
                FunctionDomainArgumentMembershipProof::IntegerRangeStart { integer, endpoint_order } => object_for(rt, vec![
                    ("type", string("integer_range_start_witness")),
                    ("proof_of_requirement_facts", JsonValue::Array(vec![project_verify_fact(integer, rt), project_verify_fact(endpoint_order, rt)])),
                ]),
            }).collect())),
            ("domain_comparison", super::store::project_verify_facts(guards, rt)),
        ]),
        FunctionDomainNonemptyEvidence::ExistingWitness(proof) => project_verify_fact(proof, rt),
    };
    object_for(rt, vec![("source_signature", signature(&proof.signature)), ("source", evidence)])
}

pub(super) fn project_function_space_nonempty(proof: &FunctionSpaceNonemptyProof, rt: &Runtime) -> JsonValue {
    match proof {
        FunctionSpaceNonemptyProof::BaseSet(proof) => project_verify_fact(proof, rt),
        FunctionSpaceNonemptyProof::EmptyDomain(proof) => project_domain_empty(proof, rt),
        FunctionSpaceNonemptyProof::CarrierTransport { carrier, carrier_equal, nonempty } => object_for(rt, vec![
            ("type", string("checked_nonempty_return_carrier_transport")),
            ("return_space", string(carrier.readable_string())),
            ("carrier_equal", project_known_equality_path(carrier_equal, rt)),
            ("source", project_function_space_nonempty(nonempty, rt)),
        ]),
        FunctionSpaceNonemptyProof::FiniteCartesianProduct { cart, factors_nonempty } => object_for(rt, vec![
            ("type", string("finite_cartesian_product_exists")),
            ("return_space", string(Obj::ProductShape(crate::ast::obj::ProductShape::Cart(cart.clone())).readable_string())),
            ("proof_of_requirement_facts", JsonValue::Array(factors_nonempty.iter().map(|proof| project_function_space_nonempty(proof, rt)).collect())),
        ]),
        FunctionSpaceNonemptyProof::ConstantFunction { signature: space, return_nonempty } => object_for(rt, vec![
            ("type", string("constant_function_exists")), ("source_signature", signature(space)),
            ("source", project_function_space_nonempty(return_nonempty, rt)),
        ]),
    }
}

pub(super) fn project_call_domains_alpha_match(proof: &FunctionCallDomainsAlphaMatchProof, rt: &Runtime) -> JsonValue {
    JsonValue::Array(proof.layers.iter().map(|layer| {
        let mut fields = vec![
            ("type", string("domain_alpha_equivalent")),
            ("source_signature", signature(&layer.selected)),
            ("target_signature", signature(&layer.alternative)),
        ];
        if let Some(carriers) = &layer.return_carriers {
            fields.push(("left_path", project_known_equality_path(&carriers.selected_equal, rt)));
            fields.push(("right_path", project_known_equality_path(&carriers.alternative_equal, rt)));
        }
        object_for(rt, fields)
    }).collect())
}

pub(super) fn project_source(proof: &CompleteFunctionDomainProof, rt: &Runtime) -> JsonValue {
    let source = match &proof.source {
        CompleteFunctionDomainSourceProof::FiniteFunction(source) => project_finite_function_source(source, rt),
        CompleteFunctionDomainSourceProof::AnonymousFunction { function, subject_equal } => object_for(rt, vec![
            ("type", string("anonymous_function")),
            ("function", string(Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone())).readable_string())),
            ("subject_equal", project_known_equality_path(subject_equal, rt)),
        ]),
        CompleteFunctionDomainSourceProof::Membership { membership, subject_equal, carrier_equal } => object_for(rt, vec![
            ("type", string("exact_function_membership")),
            ("source_fact_id", string(membership.fact_id.to_string())),
            ("fact", string(crate::ast::fact::AtomicFact::InFact(membership.clone()).readable_string())),
            ("subject_equal", project_known_equality_path(subject_equal, rt)),
            ("carrier_equal", project_known_equality_path(carrier_equal, rt)),
        ]),
        CompleteFunctionDomainSourceProof::TemplateDefinition { instance, instance_wd, subject_equal } => object_for(rt, vec![
            ("type", string("checked_template_function_definition")),
            ("instance", string(Obj::InstantiatedTemplateObj(instance.clone()).readable_string())),
            ("well_defined", project_obj_wd_proof(instance_wd, rt)),
            ("subject_equal", project_known_equality_path(subject_equal, rt)),
        ]),
        CompleteFunctionDomainSourceProof::ApplicationReturn {
            application, subject_equal, signature_source, application_children, application_requirements, return_space, carrier_equal,
        } => object_for(rt, vec![
            ("type", string("checked_function_application_return")),
            ("application", string(Obj::FnObj(application.clone()).readable_string())),
            ("subject_equal", project_known_equality_path(subject_equal, rt)),
            ("signature_source", project_application_signature_source(signature_source, rt)),
            ("child_obj_well_defined", JsonValue::Array(application_children.iter().map(|p| project_obj_wd_proof(p, rt)).collect())),
            ("requirement_fact_verified", super::store::project_verify_facts(application_requirements, rt)),
            ("return_space", string(return_space.readable_string())),
            ("carrier_equal", project_known_equality_path(carrier_equal, rt)),
        ]),
    };
    object_for(rt, vec![("source_signature", signature(&proof.signature)), ("source", source)])
}

fn project_application_signature_source(
    source: &crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::*;
    match source {
        FiniteFunction(source) => project_finite_function_source(source, rt),
        InFunctionSet { fn_set, fact_id, function_equal } => object_for(rt, vec![
            ("type", string("exact_function_membership")), ("source_signature", signature(fn_set)),
            ("source_fact_id", string(fact_id.to_string())),
            ("function_equal", project_known_equality_path(function_equal, rt)),
        ]),
        AnonymousLiteral { fn_set } => object_for(rt, vec![
            ("type", string("anonymous_literal")), ("source_signature", signature(fn_set)),
        ]),
        TemplateDefinition { fn_set, function_equal } => object_for(rt, vec![
            ("type", string("template_definition")), ("source_signature", signature(fn_set)),
            ("function_equal", project_known_equality_path(function_equal, rt)),
        ]),
    }
}

pub(super) fn project_finite_function_source(
    source: &crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof,
    rt: &Runtime,
) -> JsonValue {
    object_for(rt, vec![
        ("type", string("finite_function")),
        ("source_signature", signature(&source.signature)),
        ("source", super::known_tuple::project_shape(&source.source, rt)),
    ])
}

pub(super) fn project_function_domain(proof: &FunctionDomainMatchProof, rt: &Runtime) -> JsonValue {
    let comparison = match &proof.comparison {
        FunctionDomainComparisonProof::AlphaEquivalent => object_for(rt, vec![("type", string("domain_alpha_equivalent"))]),
        FunctionDomainComparisonProof::MutualInclusion { forward, forward_proof, reverse, reverse_proof } => object_for(rt, vec![
            ("type", string("domain_mutual_inclusion")),
            ("forward", string(forward.readable_string())),
            ("forward_proof", project_verify_fact(forward_proof, rt)),
            ("reverse", string(reverse.readable_string())),
            ("reverse_proof", project_verify_fact(reverse_proof, rt)),
        ]),
    };
    object_for(rt, vec![
        ("function_wd", project_obj_wd_proof(&proof.function_wd, rt)),
        ("target_wd", project_obj_wd_proof(&proof.target_wd, rt)),
        ("source", project_source(&proof.source, rt)),
        ("target_signature", signature(&proof.target)),
        ("domain_comparison", comparison),
    ])
}

pub(super) fn project_function_domain_failure(failure: &FunctionDomainMatchFailure, rt: &Runtime) -> JsonValue {
    match failure {
        FunctionDomainMatchFailure::FunctionWd(result) => object_for(rt, vec![
            ("phase", string("function_well_defined")), ("result", project_verify_obj_wd(result, rt)),
        ]),
        FunctionDomainMatchFailure::TargetWd(result) => object_for(rt, vec![
            ("phase", string("target_well_defined")), ("result", project_verify_obj_wd(result, rt)),
        ]),
        FunctionDomainMatchFailure::NoCompleteDomain => object_for(rt, vec![("phase", string("complete_domain_unavailable"))]),
        FunctionDomainMatchFailure::Candidates(failures) => object_for(rt, vec![
            ("phase", string("complete_domain_mismatch")),
            ("candidates", JsonValue::Array(failures.iter().map(|candidate| object_for(rt, vec![
                ("source", project_source(&candidate.source, rt)),
                ("comparison", project_comparison_failure(&candidate.comparison, rt)),
            ])).collect())),
        ]),
    }
}

fn project_comparison_failure(failure: &FunctionDomainComparisonFailure, rt: &Runtime) -> JsonValue {
    match failure {
        FunctionDomainComparisonFailure::Arity { source, target } => object_for(rt, vec![
            ("phase", string("domain_arity")),
            ("source", JsonValue::Number(*source as f64)), ("target", JsonValue::Number(*target as f64)),
        ]),
        FunctionDomainComparisonFailure::Instantiate(message) => object_for(rt, vec![
            ("phase", string("instantiate")), ("message", string(message.clone())),
        ]),
        FunctionDomainComparisonFailure::Forward { fact, result } => object_for(rt, vec![
            ("phase", string("domain_forward_inclusion")), ("goal", string(fact.readable_string())),
            ("result", project_verify_fact(result, rt)),
        ]),
        FunctionDomainComparisonFailure::Reverse { forward, forward_proof, fact, result } => object_for(rt, vec![
            ("phase", string("domain_reverse_inclusion")),
            ("forward", string(forward.readable_string())), ("forward_proof", project_verify_fact(forward_proof, rt)),
            ("goal", string(fact.readable_string())), ("result", project_verify_fact(result, rt)),
        ]),
    }
}
