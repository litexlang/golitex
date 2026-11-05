use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
const FROM: &str = r#"# A checked first-partial function supplies the ordered second partial.
thm second_partial_builtin_from_function:
    ? forall f,g fn(x cart_n(R,2)) R,p cart_n(R,2),d R:
        forall q cart_n(R,2):
            $has_partial_derivative_at(f,q,2,1,g(q))
        $has_partial_derivative_at(g,p,2,2,d)
        =>:
            $has_second_partial_derivative_at(f,p,2,1,2,d)
    release thm second_partial_at_from_function(f,g,p,2,1,2,d)
"#;
const TO: &str = r#"# A supplied first-partial function has the derivative selected by the second partial.
thm second_partial_builtin_to_function:
    ? forall f,g fn(x cart_n(R,2)) R,p cart_n(R,2),d R:
        $has_second_partial_derivative_at(f,p,2,1,2,d)
        forall q cart_n(R,2):
            $has_partial_derivative_at(f,q,2,1,g(q))
        =>:
            $has_partial_derivative_at(g,p,2,2,d)
    release thm second_partial_at_to_function(f,g,p,2,1,2,d)
"#;
#[test]
fn second_partial_function_schemas_replay_both_original_complete_contexts() {
    for (source, id, law) in [
        (
            FROM,
            BuiltinTheoremId::SecondPartialAtFromFunction,
            "secondPartialOfFirstPartialFunction",
        ),
        (
            TO,
            BuiltinTheoremId::SecondPartialAtToFunction,
            "firstPartialFunctionOfSecondPartial",
        ),
    ] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), 16);
        assert_eq!(p.dom_stores.len(), 16);
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "second_function").unwrap();
        assert!(out.contains(&format!("Litex.{law}")));
        assert!(out.contains("_second_same_domain"));
        assert_eq!(out, c.compile_run(&run, "second_function").unwrap());
    }
}
#[test]
fn second_partial_function_schemas_require_all_sixteen_pipeline_stages() {
    for source in [FROM, TO] {
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
                2 => p.dom_proofs.swap(0, 7),
                3 => p.dom_stores.swap(0, 7),
                4 => p.conclusions_wd.clear(),
                5 => p.theorem_derivation = TheoremDerivationProof::UserTheorem,
                6 => p.builtin.as_mut().unwrap().arguments.clear(),
                _ => p.builtin.as_mut().unwrap().requirements.swap(14, 15),
            }
            assert!(
                c.compile_run(&run, "changed_second_function_stage")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_function_schemas_preserve_the_first_partial_function_clause() {
    for (source, fold) in [(FROM, true), (TO, false)] {
        for change in 0..5 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = if fold { 14 } else { 15 };
            let Fact::ForallFact(p) = &mut b.requirements[index] else {
                panic!();
            };
            if change == 0 {
                p.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            } else {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::MultivariableAnalysisFact(q)) =
                    &mut p.then_facts[0]
                else {
                    panic!();
                };
                let MultivariableAnalysisRelation::PartialDerivativeAt(q) = &mut q.relation else {
                    panic!();
                };
                match change {
                    1 => q.function = super::number_object("9"),
                    2 => q.coordinate = super::number_object("9"),
                    3 => q.value = super::number_object("9"),
                    _ => q.point = super::number_object("9"),
                }
            }
            assert!(
                c.compile_run(&run, "changed_global_first_partial").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_function_schemas_keep_ordered_axes_point_and_candidate_value() {
    for (source, fold) in [(FROM, true), (TO, false)] {
        for change in 0..6 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let candidate = if fold {
                &mut b.conclusions[0]
            } else {
                &mut b.requirements[14]
            };
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = candidate else {
                panic!();
            };
            let mut args = p
                .relation
                .argument_refs()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            args[change] = super::number_object("9");
            p.relation = p.relation.with_arguments(&args);
            assert!(
                c.compile_run(&run, "changed_second_function_candidate")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_function_schemas_keep_the_last_partial_of_the_supplied_function() {
    for (source, fold) in [(FROM, true), (TO, false)] {
        for change in 0..5 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let candidate = if fold {
                &mut b.requirements[15]
            } else {
                &mut b.conclusions[0]
            };
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = candidate else {
                panic!();
            };
            let mut args = p
                .relation
                .argument_refs()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            args[change] = super::number_object("9");
            p.relation = p.relation.with_arguments(&args);
            assert!(
                c.compile_run(&run, "changed_supplied_first_function")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_function_schemas_preserve_each_original_domain_capture() {
    for (source, index) in [(FROM, 15), (TO, 14)] {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut p.dom_stores[index].infer
            else {
                panic!();
            };
            let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0];
            match change {
                0 => capture.function_domain = None,
                1 => capture.derived.clear(),
                2 => capture.source_fact_id = capture.derived[0].primary_fact_id(),
                _ => {
                    capture.function_domain.as_mut().unwrap().signature.ret_set =
                        Box::new(Obj::StandardSet(StandardSet::C))
                }
            }
            assert!(
                c.compile_run(&run, "changed_second_function_domain")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn second_partial_function_schemas_reject_unproved_first_or_second_partial() {
    let first_clause =
        "        forall q cart_n(R,2):\n            $has_partial_derivative_at(f,q,2,1,g(q))\n";
    let last_partial = "        $has_partial_derivative_at(g,p,2,2,d)\n";
    for source in [
        FROM.replace(first_clause, ""),
        FROM.replace(last_partial, ""),
        TO.replace(first_clause, ""),
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "unproved_first_function")
            .is_err());
    }
}
