//! Generated or-fact builtin-rule detailed projection.
use super::store::{project_store_and_infer, project_verify_facts};
use super::verify::project_verify_fact;
use super::wd::project_fact_wd_proof;
use crate::execute::execute_fact_stmt::OrFactSearchProofByBuiltinRule;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_or_builtin_rule(
    rule: &OrFactSearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    match rule {
        OrFactSearchProofByBuiltinRule::RealLineTrichotomyEqLessGreater(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("RealLineTrichotomyEqLessGreater")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::RealLineTrichotomyLessEqGreater(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("RealLineTrichotomyLessEqGreater")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::RealLineTrichotomyGreaterEqLess(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("RealLineTrichotomyGreaterEqLess")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::NaturalZeroOrAtLeastOne(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("NaturalZeroOrAtLeastOne")),
            ];
            entries.push(("n", string(p.n.readable_string())));
            entries.push(("n_in_n", project_verify_fact(&p.n_in_n, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::ComplementaryAtomic(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("ComplementaryAtomic")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::AbsSignSplit(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("AbsSignSplit")),
            ];
            entries.push(("arg", string(p.arg.readable_string())));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::ZeroProductSplit(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("ZeroProductSplit")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            entries.push((
                "product_zero",
                project_verify_fact(&p.product_zero, runtime),
            ));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::LessOrGreaterEqual(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("LessOrGreaterEqual")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::GreaterOrLessEqual(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("GreaterOrLessEqual")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::WeakOrderLeOrGe(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("WeakOrderLeOrGe")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("left_in_r", project_verify_fact(&p.left_in_r, runtime)));
            entries.push(("right_in_r", project_verify_fact(&p.right_in_r, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::EqualityPlusStrictCoversWeak(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("EqualityPlusStrictCoversWeak")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push(("weak_bound", project_verify_fact(&p.weak_bound, runtime)));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::CompleteResidues(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("CompleteResidues")),
            ];
            entries.push(("subject", string(p.subject.readable_string())));
            entries.push(("modulus", string(p.modulus.readable_string())));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("IntegerSuccessorTail")),
            ];
            entries.push(("subject", string(p.subject.readable_string())));
            entries.push(("base", string(p.base.readable_string())));
            entries.push((
                "subject_in_z",
                project_verify_fact(&p.subject_in_z, runtime),
            ));
            entries.push(("base_in_z", project_verify_fact(&p.base_in_z, runtime)));
            entries.push((
                "subject_ge_base",
                project_verify_fact(&p.subject_ge_base, runtime),
            ));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("SquareSumComponentNonzero")),
            ];
            entries.push(("left", string(p.left.readable_string())));
            entries.push(("right", string(p.right.readable_string())));
            entries.push((
                "square_sum_nonzero",
                project_verify_fact(&p.square_sum_nonzero, runtime),
            ));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::ClassicalImplication(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("ClassicalImplication")),
            ];
            entries.push((
                "assumed_from_branch_index",
                JsonValue::Number(p.assumed_from_branch_index as f64),
            ));
            entries.push((
                "conclusion_branch_index",
                JsonValue::Number(p.conclusion_branch_index as f64),
            ));
            entries.push((
                "assumed_premise",
                string(p.assumed_premise.readable_string()),
            ));
            entries.push((
                "assumed_well_defined",
                project_fact_wd_proof(&p.assumed_well_defined, runtime),
            ));
            entries.push((
                "assumed_store_and_infer",
                project_store_and_infer(&p.assumed_store_and_infer, runtime),
            ));
            entries.push((
                "conclusion_proof",
                project_verify_fact(&p.conclusion_proof, runtime),
            ));
            object_for(runtime, entries)
        }
        OrFactSearchProofByBuiltinRule::IntegerDiscreteSplit(p) => {
            let mut entries = vec![
                ("type", string("or_builtin")),
                ("rule", string("IntegerDiscreteSplit")),
            ];
            entries.push(("subject", string(p.subject.readable_string())));
            entries.push(("base", string(p.base.readable_string())));
            entries.push((
                "subject_in_z",
                project_verify_fact(&p.subject_in_z, runtime),
            ));
            entries.push(("base_in_z", project_verify_fact(&p.base_in_z, runtime)));
            object_for(runtime, entries)
        }
    }
}
