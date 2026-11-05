use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const ADD: &str = r#"# The add operation preserves the limits of two real sequences.
thm checked_sequence_limit_add:
    ? forall a, b seq(R), L, K R:
        $has_seq_limit(a, L)
        $has_seq_limit(b, K)
        =>:
            $has_seq_limit(fn(n N+) R{a(n) + b(n)}, L + K)
    release thm seq_limit_add(a, b, L, K)
"#;
const SUB: &str = r#"# The subtract operation preserves the limits of two real sequences.
thm checked_sequence_limit_subtract:
    ? forall a, b seq(R), L, K R:
        $has_seq_limit(a, L)
        $has_seq_limit(b, K)
        =>:
            $has_seq_limit(fn(n N+) R{a(n) - b(n)}, L - K)
    release thm seq_limit_subtract(a, b, L, K)
"#;
const MUL: &str = r#"# The multiply operation preserves the limits of two real sequences.
thm checked_sequence_limit_multiply:
    ? forall a, b seq(R), L, K R:
        $has_seq_limit(a, L)
        $has_seq_limit(b, K)
        =>:
            $has_seq_limit(fn(n N+) R{a(n) * b(n)}, L * K)
    release thm seq_limit_multiply(a, b, L, K)
"#;
const DIV: &str = r#"# A quotient limit retains nonzero denominator terms and a nonzero denominator limit.
thm checked_sequence_limit_divide:
    ? forall a, b seq(R), L, K R:
        $has_seq_limit(a, L)
        $has_seq_limit(b, K)
        K != 0
        forall n N+:
            b(n) != 0
        =>:
            $has_seq_limit(fn(n N+) R{a(n) / b(n)}, L / K)
    release thm seq_limit_divide(a, b, L, K)
"#;
#[test]
fn sequence_binary_map_preserves_each_original_stage_store_and_wd() {
    for source in [ADD, SUB, MUL, DIV] {
        for change in [
            "args",
            "proof",
            "proof_order",
            "store",
            "store_order",
            "wd",
            "nested_wd",
            "types",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                "proof" => p.dom_proofs.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store" => p.dom_stores.clear(),
                "store_order" => p.dom_stores.swap(0, 1),
                "wd" => p.conclusions_wd.clear(),
                "nested_wd" => {
                    let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                    else {
                        panic!()
                    };
                    wd.as_detailed_mut()
                        .unwrap()
                        .well_defined_of_each_parameter
                        .clear();
                }
                _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
            }
            compiler.compile_run(&run,change).expect_err("both original sequence/candidate pipelines and division premises must remain ordered");
        }
    }
}
#[test]
fn sequence_binary_map_keeps_exact_operands_binder_domain_output_and_body() {
    for source in [ADD, SUB, MUL, DIV] {
        for change in [
            "body",
            "limit",
            "domain",
            "output",
            "guard",
            "binder",
            "capture",
            "candidate",
            "second_sequence",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "candidate" {
                let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) = &mut p.requirements[3]
                else {
                    panic!()
                };
                f.value = super::number_object("0");
            } else if change == "second_sequence" {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[1] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            } else {
                let guard = p.requirements[0].clone();
                let a = p.arguments[0].clone();
                let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(goal)) =
                    &mut p.conclusions[0]
                else {
                    panic!()
                };
                if change == "limit" {
                    goal.value = super::number_object("0");
                } else {
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut goal.sequence
                    else {
                        panic!()
                    };
                    match change {
                        "body" => f.equal_to = Box::new(super::number_object("0")),
                        "domain" => {
                            f.body.set_bound_parameters.groups[0].param_type =
                                Box::new(Obj::StandardSet(StandardSet::N))
                        }
                        "output" => f.body.ret_set = Box::new(Obj::StandardSet(StandardSet::RPos)),
                        "guard" => {
                            let Fact::AtomicFact(guard) = guard else {
                                panic!()
                            };
                            f.body.dom_facts.push(QuantifierFreeFact::AtomicFact(guard));
                        }
                        "binder" => f.body.set_bound_parameters.groups[0].params.clear(),
                        "capture" => {
                            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = a else {
                                panic!()
                            };
                            f.body.set_bound_parameters.groups[0].params[0].id = id;
                        }
                        _ => panic!(),
                    }
                }
            }
            compiler.compile_run(&run,change).expect_err("binary combination cannot certify another function, carrier, free input or candidate");
        }
    }
}
#[test]
fn sequence_divide_requires_both_original_nonzero_contracts_and_unguarded_positive_term_forall() {
    for change in [
        "limit_nonzero",
        "missing_terms",
        "term_domain",
        "term_guard",
        "term_clause",
        "term_call",
        "term_zero",
    ] {
        let (mut run, compiler) = super::execute(DIV);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if change == "limit_nonzero" {
            p.requirements[4] = p.requirements[0].clone();
        } else if change == "missing_terms" {
            p.requirements.pop();
        } else {
            let guard = p.requirements[0].clone();
            let Fact::ForallFact(f) = &mut p.requirements[5] else {
                panic!()
            };
            match change {
                "term_domain" => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::N))
                }
                "term_guard" => f.dom_facts.push(guard),
                "term_clause" => f.then_facts.clear(),
                "term_call" | "term_zero" => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(eq)) =
                        &mut f.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == "term_call" {
                        eq.left = super::number_object("1");
                    } else {
                        eq.right = super::number_object("1");
                    }
                }
                _ => panic!(),
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("a nonzero limiting denominator alone does not certify all quotient terms");
    }
}
#[test]
fn sequence_binary_map_cannot_use_future_output_in_original_input_domains() {
    for source in [ADD, SUB, MUL, DIV] {
        let (mut run, compiler) = super::execute(source);
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
            .expect_err("future mapped limit is not input-domain evidence");
    }
}
