use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{EqualFactSearchedProof,EqualitySearchProofByBuiltinRule,VerifyEqualityResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof,VerifyForallFactResult};
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::execute::{ExecFactStmtResult,ExecStmtResult};
use crate::launch_command::{LaunchCommand,OutputLanguage};
use crate::runtime::Runtime;
fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
fn input(square: bool) -> &'static str {
    if square {
        "forall x R:\n    cos(x)!=0\n    =>:\n        1+tan(x)^2=1/cos(x)^2\n"
    } else {
        "forall x R:\n    sin(x)!=0\n    cos(x)!=0\n    =>:\n        tan(x)*cot(x)=1\n"
    }
}
#[test]
fn actual_two_typed_leaves_keep_ten_guarded_language_outputs() {
    for language in OutputLanguage::ALL {
        for square in [false, true] {
            let mut rt = runtime(language);
            let run = rt.run_litex_code(input(square)).unwrap();
            assert!(run.success && run.session_error.is_none());
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &run.statement_results[0]
            else {
                panic!("forall success");
            };
            let VerifyFactResult::ForallFact(f) = &stmt.verify_result else {
                panic!("forall");
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) =
                f.as_ref()
            else {
                panic!("local forall");
            };
            let VerifyFactResult::Equality(e) = &f.proved_then_facts[0].verify_result else {
                panic!("equality");
            };
            let VerifyEqualityResult::Success(e) = e.as_ref() else {
                panic!("equality success");
            };
            let EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::TrigComplexIdentity(p),
            ) = &e.searched_proof
            else {
                panic!("owned fixed law");
            };
            let (angle, id) = match p {
                TrigComplexIdentityProof::TanCotProduct(p) => {
                    (p.angle.readable_string(), "TanCotProduct")
                }
                TrigComplexIdentityProof::TanSquareReciprocalCosine(p) => {
                    (p.angle.readable_string(), "TanSquareReciprocalCosine")
                }
                _ => panic!("quotient law"),
            };
            assert_eq!(angle, "x");
            assert_eq!(
                id,
                if square {
                    "TanSquareReciprocalCosine"
                } else {
                    "TanCotProduct"
                }
            );
            let text = p.rule_name_and_message(language);
            assert!(!text.rule_name.is_empty() && text.message.contains("cos(x)"));
            let detailed =
                crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
                    .stringify();
            assert!(detailed.contains(id));
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        }
    }
}
#[test]
fn equality_product_sum_and_square_spellings_preserve_the_mathematics() {
    for source in [
        "forall x R:\n    sin(x)!=0\n    cos(x)!=0\n    =>:\n        1=cot(x)*tan(x)\n",
        "forall x R:\n    cos(x)!=0\n    =>:\n        1/(cos(x)*cos(x))=tan(x)*tan(x)+1\n",
        "forall x R:\n    cos(x)!=0\n    =>:\n        tan(x)^2+1.0=1.0/cos(x)^2\n",
    ] {
        assert!(
            runtime(OutputLanguage::English)
                .run_litex_code(source)
                .unwrap()
                .success
        );
    }
}
#[test]
fn omitted_guards_poles_wrong_signs_and_different_angles_still_reject() {
    for source in [
        "forall x R:\n    tan(x)*cot(x)=1\n",
        "forall x R:\n    cos(x)!=0\n    =>:\n        tan(x)*cot(x)=1\n",
        "forall x R:\n    1+tan(x)^2=1/cos(x)^2\n",
        "tan(pi/2)*cot(pi/2)=1\n",
        "forall x R:\n    sin(x)!=0\n    cos(x)!=0\n    =>:\n        tan(x)*cot(x)=-1\n",
        "forall x R:\n    cos(x)!=0\n    =>:\n        1+tan(x)^2=-1/cos(x)^2\n",
        "forall x,y R:\n    cos(x)!=0\n    sin(y)!=0\n    =>:\n        tan(x)*cot(y)=1\n",
        "forall x,y R:\n    cos(x)!=0\n    cos(y)!=0\n    =>:\n        1+tan(x)^2=1/cos(y)^2\n",
        "forall x C:\n    cos(x)!=0\n    =>:\n        1+tan(x)^2=1/cos(x)^2\n",
    ] {
        let run = runtime(OutputLanguage::English)
            .run_litex_code(source)
            .unwrap();
        assert!(run.session_error.is_none());
        assert!(!run.success, "{source}");
    }
}
#[test]
fn failed_target_does_not_publish_and_verified_forall_reuses_actual_source() {
    for square in [false, true] {
        let mut rt = runtime(OutputLanguage::English);
        let good = input(square);
        let bad = good.replace("=1/", "=-1/").replace("=1\n", "=-1\n");
        assert!(!rt.run_litex_code(&bad).unwrap().success);
        assert!(rt.run_litex_code(good).unwrap().success);
        let run = rt.run_litex_code(good).unwrap();
        assert!(run.success);
        let detail =
            crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
        assert!(detail.contains("by_known_forall_fact"));
        assert!(!rt.run_litex_code(&bad).unwrap().success);
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}
#[test]
fn both_persistent_law_tracers_verify_without_trust() {
    for source in [include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/tan_cot_product.lit"),include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/tan_square_reciprocal_cosine.lit")] {
        assert!(!source.contains("trust"));assert!(runtime(OutputLanguage::English).run_litex_code(source).unwrap().success);
    }
}
