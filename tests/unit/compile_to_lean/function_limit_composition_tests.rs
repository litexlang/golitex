use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::prelude::*;

const CONTINUOUS: &str = r#"# Private probe of the original local mapping composition contract.
thm checked_function_limit_continuous_compose:
    ? forall f,g,h fn(x R) R,x0,y0 R:
        $has_limit_at(f,x0,y0)
        $is_real_accumulation_at(R,x0)
        $is_continuous_at(g,y0)
        exist radius R+ st {{x R:0<abs(x-x0) and abs(x-x0)<radius} $subset {x R:x $in R,f(x) $in R,h(x)=g(f(x))}}
        =>:
            $has_limit_at(h,x0,g(y0))
    release thm fn_limit_at_continuous_compose(f,g,h,x0,y0)
"#;
const PUNCTURED: &str = r#"# Private probe of the original local mapping composition contract.
thm checked_function_limit_punctured_compose:
    ? forall f,g,h fn(x R) R,x0,y0,L R:
        $has_limit_at(f,x0,y0)
        $is_real_accumulation_at(R,x0)
        $has_limit_at(g,y0,L)
        exist radius R+ st {{x R:0<abs(x-x0) and abs(x-x0)<radius} $subset {x R:x $in R,f(x) $in R,f(x)!=y0,h(x)=g(f(x))}}
        =>:
            $has_limit_at(h,x0,L)
    release thm fn_limit_at_punctured_compose(f,g,h,x0,y0,L)
"#;
fn mapping(run: &mut RunLitexCodeResult) -> &mut SubsetFact {
    let b = invocation(run).builtin.as_mut().unwrap();
    let Fact::ExistFact(exists) = &mut b.requirements[12] else {
        panic!("source existential")
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(mapping)) = &mut exists.facts[0]
    else {
        panic!("source mapping")
    };
    mapping
}
fn allowed(run: &mut RunLitexCodeResult) -> &mut SetBuilder {
    let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &mut mapping(run).right else {
        panic!("allowed inputs")
    };
    builder
}
#[test]
fn limit_composition_replays_two_original_thirteen_stage_native_schemas() {
    for (source, id, law) in [
        (
            CONTINUOUS,
            BuiltinTheoremId::FnLimitAtContinuousCompose,
            "Continuous",
        ),
        (
            PUNCTURED,
            BuiltinTheoremId::FnLimitAtPuncturedCompose,
            "Punctured",
        ),
    ] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert_eq!(p.dom_proofs.len(), 13);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        let out = c.compile_run(&run, "local_limit_composition").unwrap();
        assert!(out.contains(&format!("Litex.finiteFunctionLimit{law}Compose")));
        assert_eq!(out, c.compile_run(&run, "local_limit_composition").unwrap());
    }
}
#[test]
fn limit_composition_requires_every_ordered_proof_store_and_conclusion_formation() {
    for source in [CONTINUOUS, PUNCTURED] {
        for change in 0..8 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => {
                    p.dom_stores.pop();
                }
                2 => p.dom_proofs.swap(9, 11),
                3 => p.dom_stores.swap(9, 11),
                4 => p.conclusions_wd.clear(),
                5 => p.theorem_derivation = TheoremDerivationProof::UserTheorem,
                6 => p
                    .builtin
                    .as_mut()
                    .unwrap()
                    .arguments
                    .pop()
                    .map(|_| ())
                    .unwrap(),
                _ => p.builtin.as_mut().unwrap().requirements.swap(9, 11),
            }
            assert!(
                c.compile_run(&run, "broken_composition_stage").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn limit_composition_retains_all_three_complete_real_function_contexts() {
    for source in [CONTINUOUS, PUNCTURED] {
        for index in 0..9 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(f)) => f.element = super::number_object("0"),
                Fact::AtomicFact(AtomicFact::SubsetFact(f)) => {
                    f.right = Obj::StandardSet(StandardSet::C)
                }
                _ => panic!("original context"),
            }
            assert!(
                c.compile_run(&run, "bad_complete_function_context")
                    .is_err(),
                "{index}"
            );
        }
    }
}
#[test]
fn limit_composition_retains_independent_output_accumulation_domain_point_and_side() {
    for source in [CONTINUOUS, PUNCTURED] {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let Fact::AtomicFact(AtomicFact::RealAccumulationFact(f)) =
                &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[10]
            else {
                panic!()
            };
            match change {
                0 => f.domain = Obj::StandardSet(StandardSet::Q),
                1 => f.point = super::number_object("9"),
                _ => f.side = RealApproachSide::Left,
            }
            assert!(
                c.compile_run(&run, "bad_output_accumulation").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn limit_composition_retains_inner_and_outer_limit_subjects_and_centres() {
    for source in [CONTINUOUS, PUNCTURED] {
        for (index, change) in [(9, 0), (9, 1), (9, 2), (11, 0), (11, 1), (11, 2)] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) => match change {
                    0 => f.function = super::number_object("7"),
                    1 => f.approach = LimitApproach::FromLeft(super::number_object("7").into()),
                    _ => f.value = super::number_object("7"),
                },
                Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) => match change {
                    0 => f.function = super::number_object("7"),
                    1 => f.point = super::number_object("7"),
                    _ => f.side = RealApproachSide::Right,
                },
                _ => panic!("outer condition"),
            }
            assert!(
                c.compile_run(&run, "bad_inner_outer_condition").is_err(),
                "{index}/{change}"
            );
        }
    }
}
#[test]
fn limit_composition_retains_positive_local_radius_and_exact_punctured_neighborhood() {
    for source in [CONTINUOUS, PUNCTURED] {
        for change in 0..5 {
            let (mut run, c) = super::execute(source);
            if change == 0 {
                let Fact::ExistFact(f) =
                    &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[12]
                else {
                    panic!()
                };
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            } else if change == 1 {
                let Fact::ExistFact(f) =
                    &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[12]
                else {
                    panic!()
                };
                f.facts.push(f.facts[0].clone());
            } else {
                let Obj::SetFormer(SetFormer::SetBuilder(f)) = &mut mapping(&mut run).left else {
                    panic!()
                };
                match change {
                    2 => f.param_set = Obj::StandardSet(StandardSet::Q).into(),
                    3 => f.facts.clear(),
                    _ => f.facts.push(f.facts[0].clone()),
                }
            }
            assert!(
                c.compile_run(&run, "bad_local_radius_neighborhood")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn limit_composition_retains_local_memberships_order_and_composition_equation() {
    for source in [CONTINUOUS, PUNCTURED] {
        for change in 0..7 {
            let (mut run, c) = super::execute(source);
            let a = allowed(&mut run);
            match change {
                0 => a.param_set = Obj::StandardSet(StandardSet::Q).into(),
                1 => a.facts.swap(0, 1),
                2 => {
                    a.facts.pop();
                }
                3 => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::InFact(f)) = &mut a.facts[0]
                    else {
                        panic!()
                    };
                    f.element = super::number_object("8");
                }
                4 => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::InFact(f)) = &mut a.facts[1]
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::Q);
                }
                _ => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(f)) =
                        a.facts.last_mut().unwrap()
                    else {
                        panic!()
                    };
                    if change == 5 {
                        f.left = super::number_object("8")
                    } else {
                        f.right = super::number_object("8")
                    };
                }
            }
            assert!(
                c.compile_run(&run, "bad_local_mapping").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn punctured_composition_requires_the_exact_eventual_exclusion() {
    for change in 0..4 {
        let (mut run, c) = super::execute(PUNCTURED);
        let a = allowed(&mut run);
        match change {
            0 => {
                a.facts.remove(2);
            }
            1 => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut a.facts[2]
                else {
                    panic!()
                };
                f.left = super::number_object("0");
            }
            2 => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut a.facts[2]
                else {
                    panic!()
                };
                f.right = super::number_object("1");
            }
            _ => a.facts.swap(1, 2),
        }
        assert!(
            c.compile_run(&run, "bad_punctured_exclusion").is_err(),
            "{change}"
        );
    }
}
#[test]
fn limit_composition_rejects_radius_neighborhood_and_mapping_binder_capture() {
    for source in [CONTINUOUS, PUNCTURED] {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &b.arguments[0] else {
                panic!()
            };
            let id = *id;
            let Fact::ExistFact(f) = &mut b.requirements[12] else {
                panic!()
            };
            if change == 0 {
                f.typed_parameters.groups[0].params[0].id = id;
            } else {
                let radius = f.typed_parameters.groups[0].params[0].id;
                let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(m)) = &mut f.facts[0]
                else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::SetBuilder(a)) = &mut m.right else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::SetBuilder(n)) = &mut m.left else {
                    panic!()
                };
                match change {
                    1 => a.param_binding.id = id,
                    2 => n.param_binding.id = radius,
                    _ => a.param_binding.id = n.param_binding.id,
                }
            }
            assert!(
                c.compile_run(&run, "captured_local_mapping").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn limit_composition_rejects_future_citations_for_inner_outer_and_mapping_proofs() {
    for source in [CONTINUOUS, PUNCTURED] {
        for index in [9, 11, 12] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let goal = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
            if index == 12 {
                let VerifyFactResult::ExistShapedFact(r) = &mut p.dom_proofs[index] else {
                    panic!("mapping exists")
                };
                let VerifyExistShapedFactResult::PlainExistFact(
                    VerifyPlainExistFactResult::Success(r),
                ) = r.as_mut()
                else {
                    panic!("mapping success")
                };
                let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) =
                    &mut r.searched_proof
                else {
                    panic!("original mapping citation")
                };
                cite.cite_fact_id = goal;
            } else {
                let child = super::atomic_proof_mut(&mut p.dom_proofs[index]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut child.searched_proof
                else {
                    panic!("original preceding citation")
                };
                cite.cite_fact_id = goal;
            }
            assert!(
                c.compile_run(&run, "future_composition_premise").is_err(),
                "{index}"
            );
        }
    }
}
#[test]
fn limit_composition_retains_exact_output_function_point_and_value() {
    for source in [CONTINUOUS, PUNCTURED] {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
                &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
            else {
                panic!()
            };
            match change {
                0 => f.function = super::number_object("3"),
                1 => f.approach = LimitApproach::AtPoint(super::number_object("3").into()),
                _ => f.value = super::number_object("3"),
            }
            assert!(
                c.compile_run(&run, "changed_composition_conclusion")
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn limit_composition_preserves_actual_explicit_goal_call_owners() {
    use crate::execute::execute_by_stmt::{ExecByStmtResult, ExecByThmStmtResult};
    for source in [
        r#"# Private probe of the original local mapping composition contract.
thm checked_function_limit_continuous_compose_call:
    ? forall f,g,h fn(x R) R,x0,y0 R:
        $has_limit_at(f,x0,y0)
        $is_real_accumulation_at(R,x0)
        $is_continuous_at(g,y0)
        exist radius R+ st {{x R:0<abs(x-x0) and abs(x-x0)<radius} $subset {x R:x $in R,f(x) $in R,h(x)=g(f(x))}}
        =>:
            $has_limit_at(h,x0,g(y0))
    by thm fn_limit_at_continuous_compose(f,g,h,x0,y0) => $has_limit_at(h,x0,g(y0))
"#,
        r#"# Private probe of the original local mapping composition contract.
thm checked_function_limit_punctured_compose_call:
    ? forall f,g,h fn(x R) R,x0,y0,L R:
        $has_limit_at(f,x0,y0)
        $is_real_accumulation_at(R,x0)
        $has_limit_at(g,y0,L)
        exist radius R+ st {{x R:0<abs(x-x0) and abs(x-x0)<radius} $subset {x R:x $in R,f(x) $in R,f(x)!=y0,h(x)=g(f(x))}}
        =>:
            $has_limit_at(h,x0,L)
    by thm fn_limit_at_punctured_compose(f,g,h,x0,y0,L) => $has_limit_at(h,x0,L)
"#,
    ] {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(p),
            )) = &mut run.statement_results[0]
            else {
                panic!()
            };
            let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
                panic!()
            };
            let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
                &mut body.proof_steps[0]
            else {
                panic!("actual explicit-goal Call")
            };
            assert!(matches!(
                p.theorem_derivation,
                TheoremDerivationProof::NativeSchema
            ));
            if change == 0 {
                p.dom_proofs.pop();
            } else if change == 1 {
                p.conclusions_wd.clear();
            } else if change == 2 {
                p.returned_conclusions.clear();
            }
            if change == 3 {
                c.compile_run(&run, "actual_composition_call").unwrap();
            } else {
                assert!(
                    c.compile_run(&run, "bad_composition_call").is_err(),
                    "{change}"
                );
            }
        }
    }
}
