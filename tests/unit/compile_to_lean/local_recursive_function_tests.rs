use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult};
use crate::prelude::*;

const SOURCE: &str = r#"# A local recursive constant sequence witnesses two prescribed initial values.
thm repeated_seed:
    ? forall a R:
        exist f fn(n N) R st {f(0) = a, f(1) = a}
    have fn sequence(n N) R by induc n from 0:
        case n = 0: a
        case n > 0: sequence(n - 1)
    sequence(0) = a
    sequence(1) = sequence(0) = a
    witness exist f fn(n N) R st {f(0) = a, f(1) = a} from sequence
"#;

fn recursive(run: &mut RunLitexCodeResult) -> &mut ExecHaveFnByInducStmtSuccessResult {
    let theorem = super::named_theorem_mut(&mut run.statement_results[0]);
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!()
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(proof),
    )) = &mut body.proof_steps[0]
    else {
        panic!()
    };
    proof
}

#[test]
fn local_recursive_declaration_and_equations_obey_source_prefix() {
    let (mut run, compiler) = super::execute(SOURCE);
    let proof = recursive(&mut run);
    let id = proof.statement.name.id;
    let facts = proof.store_and_infer_result.stored_fact_ids.clone();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &run.statement_results[0]
    else {
        panic!()
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    // The theorem has one parameter, followed by its first local declaration.
    let before = SourcePosition::new(Some(&outside), SourceOwner::Named(theorem), 1);
    let after = SourcePosition {
        before: 2,
        ..before
    };
    assert!(before.visible_recursive_function(&id).is_err());
    assert!(after.visible_recursive_function(&id).is_ok());
    for fact in &facts {
        assert!(before.visible_fact(*fact, &compiler.runtime).is_err());
        assert!(after.visible_fact(*fact, &compiler.runtime).is_ok());
    }
    // An inner cursor cannot move its enclosing statement past the active ceiling.
    let blocked = SourcePosition::new(Some(&before), after.owner, after.before);
    assert!(blocked.visible_recursive_function(&id).is_err());
    let closed = SourcePosition {
        before: 1,
        ..outside
    };
    assert!(closed.visible_recursive_function(&id).is_err());
    for fact in facts {
        assert!(closed.visible_fact(fact, &compiler.runtime).is_err());
    }
}

#[test]
fn local_recursive_result_cannot_change_its_captured_statement() {
    let (mut run, compiler) = super::execute(SOURCE);
    recursive(&mut run).statement.measure = Obj::StandardSet(StandardSet::R);
    assert_eq!(
        compiler.compile_run(&run, "bad_source").unwrap_err().route,
        "Theorem/ProofStepCapture"
    );
}

#[test]
fn local_recursive_result_requires_exact_stored_equations() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SOURCE);
        let proof = recursive(&mut run);
        match mutation {
            0 => proof
                .store_and_infer_result
                .case_defining_fact_ids
                .reverse(),
            1 => proof.store_and_infer_result.stored_fact_ids.clear(),
            2 => proof.case_checks.cases.swap(0, 1),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_evidence")
            .expect_err("changed evidence");
    }
}
