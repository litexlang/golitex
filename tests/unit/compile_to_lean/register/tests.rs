use crate::compile_to_lean::compile_register_stmt_result::registration_proof;
use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_register_stmt::*;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../../lean/examples/registered_equality/statement.lit");

#[test]
fn registrations_export_the_original_checked_laws() {
    let (run, compiler) = super::execute(SOURCE);
    let output = compiler.compile_run(&run, "registered").unwrap();
    for statement in &run.statement_results[1..4] {
        let ExecStmtResult::Register(registration) = statement else {
            panic!("registration")
        };
        let law = source_subject(registration_proof(registration).unwrap()).unwrap();
        assert!(output.contains(&format!("theorem h_{}", law.fact_id().value())));
    }
    assert_eq!(output, compiler.compile_run(&run, "registered").unwrap());
}

#[test]
fn registration_rejects_changed_property_and_law_shape() {
    for change_shape in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let ExecStmtResult::Register(ExecRegisterStmtResult::ReflexiveProp(
            ExecRegisterReflexivePropStmtResult::Success(p),
        )) = &mut run.statement_results[1]
        else {
            panic!("reflexive")
        };
        if change_shape {
            let VerifyFactResult::ForallFact(p) = &mut p.forall_proof else {
                panic!("forall")
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!("local")
            };
            p.fact.typed_parameters.groups.clear();
        } else {
            p.prop = AtomicName::Plain {
                name: "different_predicate".into(),
            };
        }
        let error = compiler.compile_run(&run, "registered").unwrap_err();
        assert!(error.route.starts_with("Register/"), "{error:?}");
    }
}

// Exercise the verifier's registered-rewrite entrypoint directly. Ordinary
// source execution can choose definition unfolding before reaching this route.
fn select_recorded_rewrite(source: &str) -> (RunLitexCodeResult, super::LitexToLeanCompiler) {
    let (mut run, mut compiler) = super::execute(source);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!("fact")
    };
    let VerifyFactResult::AtomicExceptEquality(p) = &mut p.verify_result else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
        panic!("success")
    };
    let rewrite = compiler
        .runtime
        .search_atomic_except_equality_fact_proof_by_known_rewrite(
            &p.fact,
            VerifyState::top_level(),
        )
        .unwrap()
        .expect("recorded registered rewrite");
    p.searched_proof = AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(rewrite);
    (run, compiler)
}

#[test]
fn registered_rewrite_replays_actual_reflexivity_and_symmetry_evidence() {
    for (index, target) in [
        "$lean_eqrel(2, 2)",
        "let reg_one = 1\n$lean_eqrel(reg_one, 1)",
    ]
    .iter()
    .enumerate()
    {
        let (run, compiler) = select_recorded_rewrite(&format!("{SOURCE}\n{target}\n"));
        let output = compiler.compile_run(&run, "registered").unwrap();
        assert!(output.contains("(Litex.isSet"));
        if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
            std::fs::write(
                std::path::Path::new(&directory).join(format!("registered_rewrite_{index}.lean")),
                output,
            )
            .unwrap();
        }
    }
}

#[test]
fn registered_rewrite_rejects_missing_producer_and_corrupt_permutation() {
    let source = format!("{SOURCE}\nlet reg_one = 1\n$lean_eqrel(reg_one, 1)\n");
    for corrupt in [false, true] {
        let (mut run, compiler) = select_recorded_rewrite(&source);
        if corrupt {
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
                run.statement_results.last_mut().unwrap()
            else {
                panic!("fact")
            };
            let VerifyFactResult::AtomicExceptEquality(p) = &mut p.verify_result else {
                panic!("atomic")
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
                panic!("success")
            };
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_rewrite::AtomicExceptEqualityFactSearchProofByKnownRewrite as Rule;
            let AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(Rule::Symmetry(p)) =
                &mut p.searched_proof
            else {
                panic!("symmetry")
            };
            p.argument_permutation = vec![0, 1];
        } else {
            let registration = run.statement_results.remove(2);
            run.statement_results.push(registration);
        }
        assert!(compiler.compile_run(&run, "registered").is_err());
    }
}
