//! Generated exist-shaped builtin-rule detailed projection.
use super::store::project_verify_facts;
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchProofByBuiltinRule;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_exist_builtin_rule(rule: &ExistShapedFactSearchProofByBuiltinRule, runtime: &Runtime) -> JsonValue {
    match rule {
        ExistShapedFactSearchProofByBuiltinRule::BijectivePreimage(p) => object_for(runtime, vec![
            ("type", string("exist_builtin")),
            ("rule", string("BijectivePreimage")),
            ("certificate", super::searched::project_known_premise(&p.certificate, runtime)),
            ("target_membership", project_verify_fact(&p.target_membership, runtime)),
        ]),
        ExistShapedFactSearchProofByBuiltinRule::RealLineComparisonWitness(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("RealLineComparisonWitness"))];
            entries.push(("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|f| string(f.readable_string())).collect())));
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::EqualityWitnessFromMembership(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("EqualityWitnessFromMembership"))];
            entries.push(("membership_proof", project_verify_fact(&p.membership_proof, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::NonemptySetMemberWitness(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("NonemptySetMemberWitness"))];
            entries.push(("nonempty_proof", project_verify_fact(&p.nonempty_proof, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::RationalPositiveDenominator(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("RationalPositiveDenominator"))];
            entries.push(("rational_membership_proof", project_verify_fact(&p.rational_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::RationalIntegerRatio(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("RationalIntegerRatio"))];
            entries.push(("rational_membership_proof", project_verify_fact(&p.rational_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::IntegerMultipleFromZeroRemainder(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("IntegerMultipleFromZeroRemainder"))];
            entries.push(("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|f| string(f.readable_string())).collect())));
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::ArchimedeanReciprocal(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("ArchimedeanReciprocal"))];
            entries.push(("positive_bound_proof", project_verify_fact(&p.positive_bound_proof, runtime)));
            object_for(runtime, entries)
        },
        ExistShapedFactSearchProofByBuiltinRule::RealDensityMidpoint(p) => {
            let mut entries = vec![("type", string("exist_builtin")), ("rule", string("RealDensityMidpoint"))];
            entries.push(("requirement_facts", JsonValue::Array(p.requirement_facts.iter().map(|f| string(f.readable_string())).collect())));
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
    }
}
