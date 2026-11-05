use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;

const SOURCES: [&str; 5] = [
    r#"# Eventually equal real sequences have the same limit.
thm checked_sequence_limit_eventually_equal:
    ? forall a,b seq(R),L R,cutoff N+:
        $has_seq_limit(a,L)
        forall k N+:
            k>=cutoff
            =>:
                a(k)=b(k)
        =>:
            $has_seq_limit(b,L)
    release thm seq_limit_eventually_equal(a,b,L,cutoff)
"#,
    r#"# A natural index shift, including zero, preserves a real sequence limit.
thm checked_sequence_limit_shift:
    ? forall a seq(R),L R,amount N:
        $has_seq_limit(a,L)
        =>:
            $has_seq_limit(fn(k N+) R {a(k+amount)},L)
    release thm seq_limit_shift(a,L,amount)
"#,
    r#"# An eventual order between two convergent real sequences orders their limits.
thm checked_sequence_limit_compare:
    ? forall a,b seq(R),L,M R,cutoff N+:
        $has_seq_limit(a,L)
        $has_seq_limit(b,M)
        forall k N+:
            k>=cutoff
            =>:
                a(k)<=b(k)
        =>:
            L<=M
    release thm seq_limit_compare(a,b,L,M,cutoff)
"#,
    r#"# A real sequence eventually between two sequences with one limit shares that limit.
thm checked_sequence_limit_squeeze:
    ? forall a,b,c seq(R),L R,cutoff N+:
        $has_seq_limit(a,L)
        $has_seq_limit(c,L)
        forall k N+:
            k>=cutoff
            =>:
                a(k)<=b(k)
                b(k)<=c(k)
        =>:
            $has_seq_limit(b,L)
    release thm seq_limit_squeeze(a,b,c,L,cutoff)
"#,
    r#"# A convergent real sequence has a real limit witness.
thm checked_sequence_limit_from_convergent:
    ? forall a seq(R):
        $is_seq_convergent(a)
        =>:
            exist L R st {$has_seq_limit(a,L)}
    release thm sequence_limit_from_convergent(a)
"#,
];
#[test]
fn sequence_tail_order_requires_original_ordered_stages_and_selected_schema() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "arguments",
            "conclusions",
            "derivation",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store_order" => p.dom_stores.swap(0, 1),
                "arguments" => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                "conclusions" => p.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(c.compile_run(&run, "bad_stages").is_err(), "{change}");
        }
    }
}
#[test]
fn sequence_tail_order_rejects_changed_guard_cutoff_and_tail_subjects() {
    for index in [0, 2, 3] {
        for change in ["guard", "index", "cutoff", "clause", "orientation"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let b = p.builtin.as_mut().unwrap();
            let i = b.requirements.len() - 1;
            let Fact::ForallFact(tail) = &mut b.requirements[i] else {
                panic!()
            };
            match change {
                "guard" => tail.dom_facts.clear(),
                "index" => {
                    tail.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::N))
                }
                "cutoff" => {
                    let Fact::AtomicFact(AtomicFact::GreaterEqualFact(g)) = &mut tail.dom_facts[0]
                    else {
                        panic!()
                    };
                    g.right = super::number_object("0");
                }
                "clause" => {
                    tail.then_facts.pop();
                }
                _ => match &mut tail.then_facts[0] {
                    ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) => {
                        std::mem::swap(&mut e.left, &mut e.right)
                    }
                    ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(e)) => {
                        std::mem::swap(&mut e.left, &mut e.right)
                    }
                    _ => panic!(),
                },
            }
            assert!(c.compile_run(&run, "bad_tail").is_err(), "{index} {change}");
        }
    }
}
#[test]
fn sequence_shift_retains_exact_positive_index_signature_and_natural_offset() {
    for change in [
        "carrier",
        "index",
        "value",
        "offset",
        "function",
        "operation",
    ] {
        let (mut run, c) = super::execute(SOURCES[1]);
        let p = invocation(&mut run);
        let b = p.builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(g)) = &mut b.conclusions[0] else {
            panic!()
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut g.sequence else {
            panic!()
        };
        match change {
            "carrier" => f.body.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            "index" => {
                f.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            "value" => g.value = super::number_object("0"),
            _ => {
                let Obj::FnObj(call) = f.equal_to.as_mut() else {
                    panic!()
                };
                if change == "function" {
                    call.head = Box::new(FnObjHead::from_obj(super::number_object("0")));
                } else {
                    let index = &mut call.body[0][0];
                    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = index.as_ref()
                    else {
                        panic!()
                    };
                    let new = if change == "offset" {
                        crate::rational_expression::helper::add_objs(
                            (*sum.left).clone(),
                            super::number_object("1"),
                        )
                    } else {
                        crate::rational_expression::helper::sub_objs(
                            (*sum.left).clone(),
                            (*sum.right).clone(),
                        )
                    };
                    *index = Box::new(new);
                }
            }
        }
        assert!(c.compile_run(&run, "bad_shift").is_err(), "{change}");
    }
}
#[test]
fn sequence_tail_candidate_context_consumes_original_fresh_membership_evidence() {
    for change in ["sequence_domain", "value_real"] {
        let (mut run, c) = super::execute(SOURCES[2]);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
            panic!()
        };
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut body.assumed_dom_facts[1].well_defined
        else {
            panic!()
        };
        let PredicateDomainProof::SequenceLimit(f) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("original fresh candidate formation")
        };
        if change == "sequence_domain" {
            f.sequence_source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            f.value_real.element = super::number_object("0");
        }
        assert!(c.compile_run(&run, "bad_candidate").is_err(), "{change}");
    }
}
#[test]
fn sequence_tail_cached_context_requires_visible_exact_citation() {
    let source = r#"# A real sequence eventually between two sequences with one limit shares that limit.
thm checked_sequence_limit_squeeze_aliased:
    ? forall a,b seq(R),L R,cutoff N+:
        $has_seq_limit(a,L)
        $has_seq_limit(a,L)
        forall k N+:
            k>=cutoff
            =>:
                a(k)<=b(k)
                b(k)<=a(k)
        =>:
            $has_seq_limit(b,L)
    release thm seq_limit_squeeze(a,b,a,L,cutoff)
"#;
    for change in ["future", "missing", "equality"] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let proof = super::atomic_proof_mut(&mut p.dom_proofs[3]);
        let PredicateDomainProof::ByKnownFact(cite) = &mut proof
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_domain
        else {
            panic!("actual cached limit WD")
        };
        match change {
            "future" => cite.cite_fact_id = future,
            "missing" => cite.cite_fact_id = FactId::new(u64::MAX),
            _ => {
                cite.why_parameters_of_known_fact_are_equal_to_givens.pop();
            }
        }
        assert!(c.compile_run(&run, "bad_cached").is_err(), "{change}");
    }
}

const MIXED: [&str; 2] = [
    r#"# Selected strict/nonnegative sum certificate, including the weak zero endpoint.
thm checked_mixed_positive_sum_left:
    ? forall x R,y R:
        0<x
        0<=y
        =>:
            0<x+y
    0<x+y
"#,
    r#"# Selected strict/nonnegative sum certificate, including the weak zero endpoint.
thm checked_mixed_positive_sum_right:
    ? forall x R,y R:
        0<x
        0<=y
        =>:
            0<y+x
    0<y+x
"#,
];
fn mixed(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(b) = &mut p.body else {
        panic!()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut b.proof_steps[0] else {
        panic!()
    };
    super::atomic_proof_mut(&mut p.verify_result)
}
#[test]
fn mixed_positive_sum_replays_both_original_selected_operand_orders() {
    for (i, source) in MIXED.into_iter().enumerate() {
        let (mut run, c) = super::execute(source);
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule as Rule;
        assert!(matches!(
            (&mixed(&mut run).searched_proof, i),
            (
                AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                        Rule::SumLeftStrictRightNonnegative(_)
                    )
                ),
                0
            ) | (
                AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                        Rule::SumLeftNonnegativeRightStrict(_)
                    )
                ),
                1
            )
        ));
        let out = c.compile_run(&run, "mixed_sum").unwrap();
        assert!(out.contains(if i == 0 {
            "Litex.addPositiveLeft"
        } else {
            "Litex.addPositiveRight"
        }));
    }
}
#[test]
fn mixed_positive_sum_rejects_swapped_or_changed_original_child_proofs() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule as Rule;
    for source in MIXED {
        for swap in [true, false] {
            let (mut run, c) = super::execute(source);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(rule),
            ) = &mut mixed(&mut run).searched_proof
            else {
                panic!()
            };
            let (a, b) = match rule {
                Rule::SumLeftStrictRightNonnegative(p) => {
                    (&mut p.left_positive_proof, &mut p.right_nonnegative_proof)
                }
                Rule::SumLeftNonnegativeRightStrict(p) => {
                    (&mut p.left_nonnegative_proof, &mut p.right_positive_proof)
                }
                _ => panic!(),
            };
            if swap {
                std::mem::swap(a, b);
            } else {
                let child = super::atomic_proof_mut(a);
                match &mut child.fact {
                    AtomicFact::LessFact(f) => f.right = super::number_object("0"),
                    AtomicFact::LessEqualFact(f) => f.right = super::number_object("0"),
                    _ => panic!(),
                }
            }
            assert!(c.compile_run(&run, "bad_mixed").is_err());
        }
    }
}
