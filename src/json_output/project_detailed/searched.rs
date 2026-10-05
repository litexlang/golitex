//! Searched-proof route projection for Detailed output.

use super::known_special_property::project_known_special_property;
use super::equality_builtin_gen::project_equality_builtin_rule;
use super::exist_builtin_gen::project_exist_builtin_rule;
use super::or_builtin_gen::project_or_builtin_rule;
use super::builtin_atomic_gen::project_atomic_builtin_rule;
use super::store::{project_verify_facts};
use super::strategy_gen::project_atomic_builtin_strategy;
use super::verify::project_verify_fact;
use super::wd::project_equal_wd_proof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::{TheyAreTheSameProof, SameFreeParamShapeProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{KnownEqualityPathProof};
use crate::ast::fact::Fact;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition, AtomicExceptEqualityFactSearchedProof,
    BuiltinPropDefinitionProof, SearchProofByKnownStrategy, UserDefinedPropDefinitionProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualFactSearchedProof, EqualFactSearchedProofByEquivalenceClass,
    EqualFactSearchedProofByKnownForallViaSymmetry, EqualFactSearchedProofByMatchingOneArgByOne,
    EqualitySearchProofByBuiltinRewrite, EqualitySearchProofByBuiltinStrategy,
    EqualitySearchProofByObjectDefinition, SearchProofByKnownForallFact,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchProofByKnownAtomicFact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_or_fact::{
    OrFactSearchProofBySelectedBranch, OrFactSearchedProof,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_known_premise(
    proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(runtime, vec![
        ("fact", string(proof.fact.readable_string())),
        ("searched_proof", project_atomic_except_searched(&proof.searched_proof, runtime)),
    ])
}

pub(super) fn project_atomic_except_searched(
    searched: &AtomicExceptEqualityFactSearchedProof,
    runtime: &Runtime,
) -> JsonValue {
    match searched {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(p) => super::structural_membership::project_structural_membership(p, runtime),
        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(p) => super::closed_calculation::project_atomic_calculation(p, runtime),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(r) => {
            project_atomic_builtin_rule(r, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
            project_known_atomic(p, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(p) => {
            project_known_special_property(p, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(s) => {
            project_atomic_builtin_strategy(s, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByDefinition(d) => {
            project_by_definition(d, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(s) => {
            project_known_strategy(s, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) => {
            project_known_forall(p, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(p) => {
            super::atomic_builtin_rewrite::project_atomic_builtin_rewrite(p, runtime)
        }
        AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(_) => {
            object_for(runtime, vec![("type", string("by_known_rewrite"))])
        }
    }
}

pub(super) fn project_equal_searched(
    searched: &EqualFactSearchedProof,
    runtime: &Runtime,
) -> JsonValue {
    match searched {
        EqualFactSearchedProof::ByClosedCalculation(p) => super::closed_calculation::project_equal_calculation(p, runtime),
        EqualFactSearchedProof::ByTheyAreTheSame(p) => project_they_are_the_same(p, runtime),
        EqualFactSearchedProof::ByKnownSpecialProperty(p) =>
            super::known_tuple::project_equal_known_tuple(p, runtime),
        EqualFactSearchedProof::ByBuiltinRule(r) => project_equality_builtin_rule(r, runtime),
        EqualFactSearchedProof::ByKnownForallFact(p) => project_known_forall(p, runtime),
        EqualFactSearchedProof::ByEquivalenceClass(p) => project_equivalence_class(p, runtime),
        EqualFactSearchedProof::ByObjectDefinition(p) => project_object_definition(p, runtime),
        EqualFactSearchedProof::ByBuiltinStrategy(p) => {
            project_equality_builtin_strategy(p, runtime)
        }
        EqualFactSearchedProof::ByMatchingOneArgByOne(p) => {
            project_matching_one_arg(p, runtime)
        }
        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(p) => {
            project_known_forall_via_symmetry(p, runtime)
        }
        EqualFactSearchedProof::ByBuiltinRewrite(p) => project_equality_builtin_rewrite(p, runtime),
    }
}

fn project_they_are_the_same(proof: &TheyAreTheSameProof, runtime: &Runtime) -> JsonValue {
    let mut fields = vec![("type", string("by_they_are_the_same"))];
    match proof {
        TheyAreTheSameProof::SameIr(_) => fields.push(("kind", string("same_ir"))),
        TheyAreTheSameProof::SameFreeParamShape(shape) => {
            fields.push(("kind", string("same_free_param_shape")));
            let name = match shape {
                SameFreeParamShapeProof::FnSet(_) => "fn_set",
                SameFreeParamShapeProof::AnonymousFn(_) => "anonymous_fn",
                SameFreeParamShapeProof::SetBuilder(_) => "set_builder",
                SameFreeParamShapeProof::Compound(_) => "compound_obj",
            };
            fields.push(("shape", string(name)));
        }
    }
    object_for(runtime, fields)
}

fn project_equivalence_class(
    proof: &EqualFactSearchedProofByEquivalenceClass,
    runtime: &Runtime,
) -> JsonValue {
    let mut fields = vec![("type", string("by_equivalence_class"))];
    match proof {
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path) => {
            fields.push(("kind", string("known_path")));
            fields.push(("path", project_known_equality_path(path, runtime)));
        }
        EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(p) => {
            fields.push(("kind", string("alpha_endpoints")));
            fields.push(("cite_fact_id", string(p.cited.fact_id.to_string())));
            fields.push(("cite", string(crate::ast::fact::AtomicFact::EqualFact(p.cited.clone()).readable_string())));
            fields.push(("reversed", JsonValue::Bool(p.reversed)));
            fields.push(("left_identity", project_they_are_the_same(&p.left_identity, runtime)));
            fields.push(("right_identity", project_they_are_the_same(&p.right_identity, runtime)));
        }
        EqualFactSearchedProofByEquivalenceClass::AlphaPaths(p) => {
            fields.push(("kind", string("alpha_paths")));
            fields.push(("left_path", project_known_equality_path(&p.left_path, runtime)));
            fields.push(("left", string(p.left.readable_string())));
            fields.push(("right", string(p.right.readable_string())));
            fields.push(("identity", project_they_are_the_same(&p.identity, runtime)));
            fields.push(("right_path", project_known_equality_path(&p.right_path, runtime)));
        }
        EqualFactSearchedProofByEquivalenceClass::ViaPeers(p) => {
            let searched = project_equal_searched(&p.bridge.searched_proof, runtime);
            fields.push(("kind", string("via_peers")));
            fields.push(("left_path", project_known_equality_path(&p.left_path, runtime)));
            fields.push(("bridge", object_for(runtime, vec![
                ("fact", string(crate::ast::fact::AtomicFact::EqualFact(p.bridge.fact.clone()).readable_string())),
                ("well_defined", project_equal_wd_proof(&p.bridge.well_defined_proof, runtime)),
                ("searched_proof", searched),
            ])));
            fields.push(("right_path", project_known_equality_path(&p.right_path, runtime)));
        }
    }
    object_for(runtime, fields)
}

pub(super) fn project_known_equality_path(proof: &KnownEqualityPathProof, runtime: &Runtime) -> JsonValue {
    JsonValue::Array(proof.path.iter().map(|(from, to, fact_id)| {
        let mut entries = vec![
            ("from", string(from.readable_string())),
            ("to", string(to.readable_string())),
            ("cite_fact_id", string(fact_id.to_string())),
        ];
        if let Some(fact) = runtime.fact_by_id_in_stack(*fact_id) {
            entries.push(("cite", string(fact.readable_string())));
        }
        object_for(runtime, entries)
    }).collect())
}

fn project_object_definition(
    proof: &EqualitySearchProofByObjectDefinition,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition,
        by_identifier::EqualitySearchProofByIdentifierObjectDefinition,
        by_template::EqualitySearchProofByTemplateObjectDefinition,
    };
    match proof {
        EqualitySearchProofByObjectDefinition::ByIdentifier(inner) => match inner {
            EqualitySearchProofByIdentifierObjectDefinition::HaveObjEqual(p) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                ("kind", string("identifier_have_obj_equal")),
                ("expanded_rhs", string(p.expanded_rhs.readable_string())),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ]),
            EqualitySearchProofByIdentifierObjectDefinition::LetObj(p) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                ("kind", string("identifier_let_obj")),
                ("expanded_rhs", string(p.expanded_rhs.readable_string())),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ]),
        },
        EqualitySearchProofByObjectDefinition::ByFnApplication(inner) => match inner {
            EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(p) =>
                super::function_body::project_parent_checked_beta(p, runtime),
            EqualitySearchProofByFnApplicationObjectDefinition::BothFunctionBodies(p) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                ("kind", string("fn_application_both_function_bodies")),
                ("left_normalization", super::function_body::project_function_body_normalization(&p.left_normalization, runtime)),
                ("right_normalization", super::function_body::project_function_body_normalization(&p.right_normalization, runtime)),
                ("residual_equal", project_verify_fact(&p.residual_equal, runtime)),
            ]),
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(p) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                ("kind", string("fn_application_have_fn_equal")),
                ("normalization", super::function_body::project_function_body_normalization(&p.normalization, runtime)),
                ("expanded_body", string(p.normalization.expanded_body.readable_string())),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ]),
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqualCaseByCase(p) => {
                object_for(runtime, vec![
                    ("type", string("by_object_definition")),
                    ("kind", string("fn_application_have_fn_equal_case_by_case")),
                    (
                        "matched_case_index",
                        JsonValue::Number(p.matched_case_index as f64),
                    ),
                    ("expanded_body", string(p.expanded_body.readable_string())),
                    (
                        "residual_equal",
                        project_verify_fact(&p.residual_equal, runtime),
                    ),
                ])
            }
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnByInduc(p) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                ("kind", string("fn_application_have_fn_by_induc")),
                ("expanded_body", string(p.expanded_body.readable_string())),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ]),
        },
        EqualitySearchProofByObjectDefinition::ByTemplate(inner) => match inner {
            EqualitySearchProofByTemplateObjectDefinition::HaveObjEqual(p) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                ("kind", string("template_have_obj_equal")),
                ("expanded_rhs", string(p.expanded_rhs.readable_string())),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ]),
            EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualApplication(p) => object_for(runtime, vec![
                    ("type", string("by_object_definition")),
                    ("kind", string("template_have_fn_equal_application")),
                    ("normalization", super::function_body::project_function_body_normalization(&p.normalization, runtime)),
                    ("expanded_body", string(p.normalization.expanded_body.readable_string())),
                    (
                        "residual_equal",
                        project_verify_fact(&p.residual_equal, runtime),
                    ),
                ],
            ),
            EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualCaseByCaseApplication(
                p,
            ) => object_for(runtime, vec![
                ("type", string("by_object_definition")),
                (
                    "kind",
                    string("template_have_fn_equal_case_by_case_application"),
                ),
                (
                    "matched_case_index",
                    JsonValue::Number(p.matched_case_index as f64),
                ),
                ("expanded_body", string(p.expanded_body.readable_string())),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ]),
            EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(p) => {
                object_for(runtime, vec![
                    ("type", string("by_object_definition")),
                    ("kind", string("template_have_fn_by_induc_application")),
                    ("expanded_body", string(p.expanded_body.readable_string())),
                    (
                        "residual_equal",
                        project_verify_fact(&p.residual_equal, runtime),
                    ),
                ])
            }
        },
    }
}

fn project_equality_builtin_strategy(
    proof: &EqualitySearchProofByBuiltinStrategy,
    runtime: &Runtime,
) -> JsonValue {
    let (name, requirements, proofs) = match proof {
        EqualitySearchProofByBuiltinStrategy::CosZeroIntegerOffset(p) => (
            "CosZeroIntegerOffset", &p.requirement_facts, &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::TupleComponentEquality(p) => (
            "TupleComponentEquality", &p.requirement_facts, &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(p) => (
            "ArithmeticCongruence", &p.requirement_facts, &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::ExtremumEquality(p) => (
            "ExtremumEquality",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::FiniteSetProductPointwiseEquality(p) => (
            "FiniteSetProductPointwiseEquality",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::ModCongruence(p) => (
            "ModCongruence",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(p) => (
            "RationalWithNonzeroPremises",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        EqualitySearchProofByBuiltinStrategy::ComplexWithNonzeroPremises(p) => (
            "ComplexWithNonzeroPremises", &p.requirement_facts, &p.proof_of_requirement_facts,
        ),
    };
    object_for(runtime, vec![
        ("type", string("builtin_strategy")),
        ("strategy", string(name)),
        (
            "requirement_facts",
            JsonValue::Array(
                requirements
                    .iter()
                    .map(|f: &Fact| string(f.readable_string()))
                    .collect(),
            ),
        ),
        (
            "proof_of_requirement_facts",
            project_verify_facts(proofs, runtime),
        ),
    ])
}

fn project_matching_one_arg(
    proof: &EqualFactSearchedProofByMatchingOneArgByOne,
    runtime: &Runtime,
) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("by_matching_one_arg_by_one")),
        (
            "corresponding_arg_equal_proofs",
            project_verify_facts(&proof.corresponding_arg_equal_proofs, runtime),
        ),
    ])
}

fn project_known_forall_via_symmetry(
    proof: &EqualFactSearchedProofByKnownForallViaSymmetry,
    runtime: &Runtime,
) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("by_known_forall_via_symmetry")),
        (
            "reversed_equal",
            string(
                crate::ast::fact::AtomicFact::EqualFact(proof.reversed_equal.clone())
                    .readable_string(),
            ),
        ),
        (
            "known_forall",
            project_known_forall(&proof.known_forall, runtime),
        ),
    ])
}

fn project_equality_builtin_rewrite(
    proof: &EqualitySearchProofByBuiltinRewrite,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(p) => {
            let cites: Vec<JsonValue> = p
                .cited_equal_fact_ids
                .iter()
                .map(|id| {
                    let mut entries = vec![("fact_id", string(id.to_string()))];
                    if let Some(fact) = runtime.fact_by_id_in_stack(*id) {
                        entries.push(("fact", string(fact.readable_string())));
                    }
                    object_for(runtime, entries)
                })
                .collect();
            object_for(runtime, vec![
                ("type", string("by_builtin_rewrite")),
                ("rule", string("ClosedNumericEqualSubstitution")),
                ("rewritten_left", string(p.rewritten_left.readable_string())),
                (
                    "rewritten_right",
                    string(p.rewritten_right.readable_string()),
                ),
                ("cited_equal_fact_ids", JsonValue::Array(cites)),
                (
                    "residual_equal",
                    project_verify_fact(&p.residual_equal, runtime),
                ),
            ])
        }
    }
}

pub(super) fn project_known_atomic(
    proof: &AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
    runtime: &Runtime,
) -> JsonValue {
    let mut entries = vec![
        ("type", string("by_known_atomic")),
        ("cite_fact_id", string(proof.cite_fact_id.to_string())),
    ];
    if let Some(fact) = runtime.fact_by_id_in_stack(proof.cite_fact_id) {
        entries.push(("cite", string(fact.readable_string())));
    }
    // Each known argument is transported to the goal argument by its own
    // equality proof. Keep these children visible, including peer bridges.
    entries.push((
        "why_parameters_of_known_fact_are_equal_to_givens",
        JsonValue::Array(proof.why_parameters_of_known_fact_are_equal_to_givens
            .iter().map(|p| project_equal_searched(p, runtime)).collect()),
    ));
    object_for(runtime, entries)
}

fn project_known_forall(proof: &SearchProofByKnownForallFact, runtime: &Runtime) -> JsonValue {
    let mut entries = vec![
        ("type", string("by_known_forall")),
        ("cite_fact_id", string(proof.cite.fact_id.to_string())),
    ];
    if let Some(fact) = runtime.fact_by_id_in_stack(proof.cite.fact_id) {
        entries.push(("cite", string(fact.readable_string())));
    }
    entries.push((
        "forall_parameters_match_what_args",
        JsonValue::Array(
            proof
                .forall_parameters_match_what_args
                .iter()
                .map(|o: &Obj| string(o.readable_string()))
                .collect(),
        ),
    ));
    entries.push((
        "proof_of_dom_facts",
        project_verify_facts(
            &proof.instantiation_requirements.proof_of_dom_facts,
            runtime,
        ),
    ));
    object_for(runtime, entries)
}

fn project_known_strategy(proof: &SearchProofByKnownStrategy, runtime: &Runtime) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("by_known_strategy")),
        ("strategy_name", string(proof.strategy_name.clone())),
        ("then_index", JsonValue::Number(proof.then_index as f64)),
        (
            "proof_of_dom_facts",
            project_verify_facts(
                &proof.instantiation_requirements.proof_of_dom_facts,
                runtime,
            ),
        ),
    ])
}

fn project_by_definition(
    proof: &AtomicExceptEqualityFactSearchProofByDefinition,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(p) => {
            project_user_prop_def(p, runtime)
        }
        AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(p) => {
            project_builtin_prop_def(p, runtime)
        }
    }
}

fn project_user_prop_def(proof: &UserDefinedPropDefinitionProof, runtime: &Runtime) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("by_definition")),
        ("kind", string("user_defined_prop")),
        (
            "requirement_facts",
            JsonValue::Array(
                proof
                    .requirement_facts
                    .iter()
                    .map(|f: &Fact| string(f.readable_string()))
                    .collect(),
            ),
        ),
        (
            "proof_of_requirement_facts",
            project_verify_facts(&proof.proof_of_requirement_facts, runtime),
        ),
    ])
}

fn project_builtin_prop_def(proof: &BuiltinPropDefinitionProof, runtime: &Runtime) -> JsonValue {
    let (kind, requirements, proofs) = match proof {
        BuiltinPropDefinitionProof::Subset(p) => (
            "subset",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Superset(p) => (
            "superset",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::ProperSubset(p) => (
            "proper_subset",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::ProperSuperset(p) => (
            "proper_superset",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Injective(p) => (
            "injective",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Surjective(p) => (
            "surjective",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Bijective(p) => (
            "bijective",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::IsChoiceFunctionFor(p) => (
            "is_choice_function_for",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Prime(p) => (
            "prime",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Coprime(p) => (
            "coprime",
            &p.requirement_facts,
            &p.proof_of_requirement_facts,
        ),
        BuiltinPropDefinitionProof::Dvd(p) => {
            ("dvd", &p.requirement_facts, &p.proof_of_requirement_facts)
        }
    };
    object_for(runtime, vec![
        ("type", string("by_definition")),
        ("kind", string(kind)),
        (
            "requirement_facts",
            JsonValue::Array(
                requirements
                    .iter()
                    .map(|f: &Fact| string(f.readable_string()))
                    .collect(),
            ),
        ),
        (
            "proof_of_requirement_facts",
            project_verify_facts(proofs, runtime),
        ),
    ])
}

pub(super) fn project_or_searched(searched: &OrFactSearchedProof, runtime: &Runtime) -> JsonValue {
    match searched {
        OrFactSearchedProof::ByBuiltinRule(r) => project_or_builtin_rule(r, runtime),
        OrFactSearchedProof::BySelectedBranch(b) => project_or_selected_branch(b, runtime),
        OrFactSearchedProof::ByKnownOrFact(p) => {
            let mut entries = vec![
                ("type", string("by_known_or")),
                ("cite_fact_id", string(p.cite_fact_id.to_string())),
            ];
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        }
        OrFactSearchedProof::ByKnownForallFact(p) => project_known_forall(p, runtime),
    }
}

fn project_or_selected_branch(
    proof: &OrFactSearchProofBySelectedBranch,
    runtime: &Runtime,
) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("by_selected_branch")),
        (
            "selected_index",
            JsonValue::Number(proof.selected_index as f64),
        ),
        (
            "selected_branch",
            project_verify_fact(&proof.selected_branch, runtime),
        ),
            ])
}

pub(super) fn project_exist_searched(
    searched: &ExistShapedFactSearchedProof,
    runtime: &Runtime,
) -> JsonValue {
    match searched {
        ExistShapedFactSearchedProof::ByBuiltinRule(r) => project_exist_builtin_rule(r, runtime),
        ExistShapedFactSearchedProof::ByKnownExistShapedFact(p) => {
            let mut entries = vec![
                ("type", string("by_known_exist")),
                ("cite_fact_id", string(p.cite_fact_id.to_string())),
            ];
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        }
        ExistShapedFactSearchedProof::ByKnownForallFact(p) => project_known_forall(p, runtime),
    }
}
