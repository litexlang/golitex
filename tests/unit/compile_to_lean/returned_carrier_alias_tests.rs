use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;
const NESTED: &str = r#"# Index a sequence of real sequences through two carrier aliases.
have AliasRowSpace set = seq(R)
have AliasRowsSpace set = seq(AliasRowSpace)
forall provider fn(t R) AliasRowsSpace, t R, row, col N+:
    provider(t)(row)(col) $in R
"#;
const GUARDED: &str = r#"# Call a returned function through its alias, retaining both layers of guards.
have AliasGuardedSpace set = fn(k N+: k <= 2) R
forall provider fn(t R: t != 0) AliasGuardedSpace, t R:
    t != 0
    =>:
        provider(t)(2) $in R
"#;
const MATRIX: &str = r#"# Read a matrix entry through the alias of a function's return set.
have AliasMatrixSpace set = matrix(R, 2, 2)
forall provider fn(t R) AliasMatrixSpace, t R:
    provider(t)(1, 2) $in R
"#;

fn nested_call(run: &mut RunLitexCodeResult) -> &mut FnObjObjWellDefinedProof {
    let all = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = atom
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0]
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original returned-call WD")
    };
    call
}

#[test]
fn returned_carrier_aliases_reject_missing_reordered_and_changed_evidence() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(NESTED);
        compiler.compile_run(&run, "before_mutation").unwrap();
        let call = nested_call(&mut run);
        assert_eq!(call.requirement_fact_verified.len(), 5);
        assert!(matches!(
            call.requirement_fact_verified[1],
            VerifyFactResult::Equality(_)
        ));
        assert!(matches!(
            call.requirement_fact_verified[3],
            VerifyFactResult::Equality(_)
        ));
        match mutation {
            0 => {
                call.requirement_fact_verified.remove(1);
            }
            1 => call.requirement_fact_verified.swap(1, 2),
            2 => call.requirement_fact_verified.swap(1, 3),
            3 | 4 => {
                let equal = super::equality_proof_mut(&mut call.requirement_fact_verified[1]);
                if mutation == 3 {
                    equal.fact.left = Obj::StandardSet(StandardSet::R);
                } else {
                    equal.fact.right = Obj::StandardSet(StandardSet::R);
                }
            }
            5 => {
                call.child_obj_well_defined.pop();
            }
            6 => {
                call.requirement_fact_verified.pop();
            }
            7 => call.child_obj_well_defined.swap(1, 2),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_returned_alias")
            .expect_err(
                "carrier equalities and call evidence retain their exact subjects and order",
            );
    }
}

#[test]
fn returned_carrier_aliases_keep_the_inner_guard_and_index_bounds() {
    for source in [
        GUARDED.replace("provider(t)(2)", "provider(t)(3)"),
        MATRIX.replace("provider(t)(1, 2)", "provider(t)(1, 3)"),
    ] {
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_returned_alias")
            .expect_err("source WD fails");
    }
}
