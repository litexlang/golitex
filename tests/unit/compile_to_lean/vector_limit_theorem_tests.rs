use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const DEFINITION: &str = r#"# Invoke the vector-limit introduction theorem with its exact domain and output dimensions.
thm checked_vector_limit_builtin_definition:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), L cart_n(R, 3):
        forall radius R+:
            exist x cart_n(R, 2) st {0 < euclidean_norm(fn(k closed_range(1, 2)) R{x(k) - p(k)}, 2), euclidean_norm(fn(k closed_range(1, 2)) R{x(k) - p(k)}, 2) < radius}
        forall epsilon R+:
            exist delta R+ st {{x cart_n(R, 2): 0 < euclidean_norm(fn(k closed_range(1, 2)) R{x(k) - p(k)}, 2), euclidean_norm(fn(k closed_range(1, 2)) R{x(k) - p(k)}, 2) < delta} $subset {y cart_n(R, 2): euclidean_norm(fn(k closed_range(1, 3)) R{f(y)(k) - L(k)}, 3) < epsilon}}
        =>:
            $has_vector_limit_at(f, p, 2, 3, L)
    release thm vector_limit_at_from_definition(f, p, 2, 3, L)
"#;
const ELIMINATION: &str = r#"# A vector limit supplies epsilon control in the declared three-dimensional output space.
thm checked_vector_limit_builtin_epsilon_control:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), L cart_n(R, 3), epsilon R+:
        $has_vector_limit_at(f, p, 2, 3, L)
        =>:
            exist delta R+ st {{x cart_n(R, 2): 0 < euclidean_norm(fn(k closed_range(1, 2)) R{x(k) - p(k)}, 2), euclidean_norm(fn(k closed_range(1, 2)) R{x(k) - p(k)}, 2) < delta} $subset {y cart_n(R, 2): euclidean_norm(fn(k closed_range(1, 3)) R{f(y)(k) - L(k)}, 3) < epsilon}}
    release thm vector_limit_at_to_definition(f, p, 2, 3, L)
"#;
const UNIQUE: &str = r#"# Limits of a map from the real plane to three-dimensional real vectors are unique.
thm checked_vector_limit_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), L, K cart_n(R, 3):
        $has_vector_limit_at(f, p, 2, 3, L)
        $has_vector_limit_at(f, p, 2, 3, K)
        =>:
            L = K
    release thm vector_limit_at_unique(f, p, 2, 3, L, K)
"#;
const EXISTS: &str = r#"# A vector limit provides an existential witness in the exact output dimension.
thm checked_vector_limit_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), L cart_n(R, 3):
        $has_vector_limit_at(f, p, 2, 3, L)
        =>:
            exist value cart_n(R, 3) st {$has_vector_limit_at(f, p, 2, 3, value)}
    release thm vector_limit_at_exists(f, p, 2, 3, L)
"#;
const SELECTED: &str = r#"# The vector selector retains an original witness and both declared dimensions.
thm checked_vector_limit_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2):
        exist value cart_n(R, 3) st {$has_vector_limit_at(f, p, 2, 3, value)}
        =>:
            $has_vector_limit_at(f, p, 2, 3, lim_vector_at(f, p, 2, 3))
    release thm vector_limit_at_selected(f, p, 2, 3)
"#;

#[test]
fn vector_limit_theorem_retains_all_original_stages_and_both_output_formations() {
    for change in [
        "proof",
        "proof_order",
        "store",
        "store_order",
        "wd",
        "types",
    ] {
        let (mut run, compiler) = super::execute(ELIMINATION);
        let p = invocation(&mut run);
        match change {
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(0, 5),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 5),
            "wd" => {
                p.conclusions_wd.pop();
            }
            _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
        }
        compiler.compile_run(&run, change).expect_err(
            "every original prerequisite, store and both output WD stages are required",
        );
    }
}

#[test]
fn vector_limit_theorem_requires_original_domain_capture_and_input_output_carriers() {
    for change in ["missing", "identity", "domain", "input", "output"] {
        let (mut run, compiler) = super::execute(UNIQUE);
        let p = invocation(&mut run);
        if change == "missing" {
            p.dom_stores[5].infer = None;
        } else {
            let other = p.builtin.as_ref().unwrap().requirements[6].fact_id();
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut p.dom_stores[5].infer
            else {
                panic!()
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_mut_slice()
            else {
                panic!()
            };
            match change {
                "identity" => capture.source_fact_id = other,
                "domain" => capture.function_domain = None,
                "input" => {
                    capture
                        .function_domain
                        .as_mut()
                        .unwrap()
                        .signature
                        .set_bound_parameters
                        .groups[0]
                        .param_type = Box::new(Obj::StandardSet(StandardSet::R))
                }
                _ => {
                    capture.function_domain.as_mut().unwrap().signature.ret_set =
                        Box::new(Obj::StandardSet(StandardSet::R))
                }
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("the exact candidate capture and both vector dimensions are authoritative");
    }
}

#[test]
fn vector_limit_theorem_retains_exact_source_clauses_and_value_formation() {
    for change in ["accumulation", "epsilon", "positive", "value_wd"] {
        let (mut run, compiler) = super::execute(DEFINITION);
        let p = invocation(&mut run);
        if change == "value_wd" {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!()
            };
            capture.requirements.pop();
        } else {
            let index = if change == "epsilon" { 6 } else { 5 };
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[index] else {
                panic!()
            };
            if change == "positive" {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            } else {
                f.then_facts.clear();
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "the value carrier and exact positive-radius/epsilon clauses cannot be weakened",
        );
    }
}

#[test]
fn vector_limit_theorem_keeps_original_existence_carrier_and_selected_dimensions() {
    let (mut run, compiler) = super::execute(EXISTS);
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "wrong_exist_carrier")
        .expect_err("a vector witness cannot be replaced by a real scalar witness");
    let (mut run, compiler) = super::execute(SELECTED);
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
        &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    let MultivariableAnalysisRelation::VectorLimit(r) = &mut f.relation else {
        panic!()
    };
    let Obj::LimitOperator(LimitOperator::MultivariableVector(selector)) = &mut r.value else {
        panic!()
    };
    std::mem::swap(
        &mut selector.input_dimension,
        &mut selector.output_dimension,
    );
    compiler
        .compile_run(&run, "swapped_selected_dimensions")
        .expect_err("input and output dimensions retain distinct mathematical roles");
}

#[test]
fn vector_limit_theorem_rejects_future_conclusion_as_an_original_premise() {
    let (mut run, compiler) = super::execute(UNIQUE);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("the equality conclusion is invisible to original prerequisites");
}
