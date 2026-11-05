use crate::compile_to_lean::compile_register_stmt_result::registration_proof;
use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_register_stmt::*;
use crate::prelude::*;

const SOURCE: &str = r#"# Equality is reflexive, symmetric and transitive on arbitrary Litex objects.
prop lean_eqrel(x, y set):
    x = y

register reflexive:
    ? forall reg_x set:
        $lean_eqrel(reg_x, reg_x)

register symmetric:
    ? forall reg_x, reg_y set:
        $lean_eqrel(reg_x, reg_y)
        =>:
            $lean_eqrel(reg_y, reg_x)

register transitive:
    ? forall reg_x, reg_y, reg_z set:
        $lean_eqrel(reg_x, reg_y)
        $lean_eqrel(reg_y, reg_z)
        =>:
            $lean_eqrel(reg_x, reg_z)

$lean_eqrel(1, 1)

forall reg_a, reg_b, reg_c set:
    $lean_eqrel(reg_a, reg_b)
    $lean_eqrel(reg_b, reg_c)
    =>:
        $lean_eqrel(reg_a, reg_c)

thm locally_registered_equality:
    ? forall reg_t set:
        $lean_eqrel(reg_t, reg_t)
    register reflexive:
        ? forall local_reg_t set:
            $lean_eqrel(local_reg_t, local_reg_t)
"#;

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

fn transitivity_source() -> String {
    let source = r#"# A user-defined real order reuses its proved, registered transitivity law.
# Before: register transitive supported chain storage, but ordinary goals had
# no KnownRewrite/Transitivity route. Order-specific shortcuts could mask this.
prop below(x, y set):
    x $in R
    y $in R
    x <= y

claim:
    ? forall x, y, z set:
        $below(x, y)
        $below(y, z)
        =>:
            $below(x, z)
    x <= y <= z
    by def $below(x, z)

register transitive:
    ? forall x, y, z set:
        $below(x, y)
        $below(y, z)
        =>:
            $below(x, z)

# Now: the registered rewrite can select below(a,b), check below(b,c), then
# apply the checked law. Ordinary verification may first cite the ambient forall;
# focused kernel/compiler tests select and replay the actual rewrite entrypoint.
forall a, b, c R:
    $below(a, b)
    $below(b, c)
    =>:
        $below(a, c)

# Boundary: residual verification cannot use another registered rewrite.
# Evidence: target/release/litex -lang en -strict -f examples/proof_nodes/atomic/by_known_rewrite/transitivity.lit
# Implementation: search_transitive_relation.rs and known rewrite dispatcher.
"#;
    let prefix = source.split("# Now:").next().unwrap();
    format!("{prefix}\nhave rel_a R=1\nhave rel_b R=2\nhave rel_c R=3\nby def $below(rel_a,rel_b)\nby def $below(rel_b,rel_c)\n$below(rel_a,rel_c)\n")
}

#[test]
fn one_step_registered_transitivity_replays_the_checked_registration_and_two_premises() {
    let (run, compiler) = select_recorded_rewrite(&transitivity_source());
    let output = compiler
        .compile_run(&run, "registered_transitivity")
        .unwrap();
    assert!(output.contains("Litex.leTrans"));
    assert!(!output.contains("sorry"));
    if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
        std::fs::write(
            std::path::Path::new(&directory).join("registered_transitivity.lean"),
            output,
        )
        .unwrap();
    }
}

#[test]
fn one_step_registered_transitivity_rejects_late_registration_and_wrong_known_edge() {
    for change in 0..3 {
        let (mut run, compiler) = select_recorded_rewrite(&transitivity_source());
        if change == 0 {
            let registration = run.statement_results.remove(2);
            run.statement_results.push(registration);
        } else {
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
                run.statement_results.last_mut().unwrap()
            else {
                panic!()
            };
            let proof = super::atomic_proof_mut(&mut p.verify_result);
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByKnownRewrite as Rule;
            let AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(Rule::Transitivity(p)) =
                &mut proof.searched_proof
            else {
                panic!("registered transitivity")
            };
            if change == 1 {
                p.application.known_left_fact_id = FactId::new(u64::MAX);
            } else {
                p.cite_prop = AtomicName::plain("another_relation".into());
            }
        }
        assert!(compiler
            .compile_run(&run, "bad_registered_transitivity")
            .is_err());
    }
}
