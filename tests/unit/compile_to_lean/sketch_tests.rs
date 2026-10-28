use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_proof_block_stmt::{
    ExecProofBlockStmtResult, ExecSketchStmtResult, ExecSketchStmtSuccess,
};
use crate::prelude::*;

const ARITHMETIC: &str =
    include_str!("../../../lean/examples/local_arithmetic_sketch/statement.lit");

fn sketch(statement: &ExecStmtResult) -> &ExecSketchStmtSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
        ExecSketchStmtResult::Success(p),
    )) = statement
    else {
        panic!("successful sketch")
    };
    p
}

fn sketch_mut(statement: &mut ExecStmtResult) -> &mut ExecSketchStmtSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
        ExecSketchStmtResult::Success(p),
    )) = statement
    else {
        panic!("successful sketch")
    };
    p
}

#[test]
fn sketch_checks_local_calculation_without_exporting_it() {
    let (run, compiler) = super::execute(ARITHMETIC);
    let lean = compiler
        .compile_run(&run, "local_arithmetic_sketch")
        .unwrap();
    assert!(lean.contains("private theorem _sketch_1"));
    assert!(lean.contains("Litex.add"));
    assert!(lean.contains("exact True.intro"));
    assert!(lean.len() < 30_000);
    assert_eq!(
        lean,
        compiler
            .compile_run(&run, "local_arithmetic_sketch")
            .unwrap()
    );
}

#[test]
fn sketch_does_not_recover_missing_or_future_producers_from_its_env() {
    for reorder in [false, true] {
        let (mut run, compiler) = super::execute(ARITHMETIC);
        let p = sketch_mut(&mut run.statement_results[0]);
        if reorder {
            p.proof_steps.swap(0, 1);
        } else {
            p.proof_steps.remove(0);
        }
        assert!(compiler
            .compile_run(&run, "sketch_missing_producer")
            .is_err());
    }
}

#[test]
fn sketch_fact_citations_are_prefix_local_and_do_not_escape() {
    let (run, compiler) = super::execute(ARITHMETIC);
    let p = sketch(&run.statement_results[0]);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(alias)),
    )) = &p.proof_steps[0]
    else {
        panic!()
    };
    let fact = alias.stored_fact_ids[0];
    let outer = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let before = SourcePosition::new(Some(&outer), SourceOwner::Sketch(p), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(compiler.cited_fact_reference(fact, &before).is_err());
    assert!(compiler.cited_fact_reference(fact, &after).is_ok());
    let closed = SourcePosition { before: 1, ..outer };
    assert!(compiler.cited_fact_reference(fact, &closed).is_err());
}

#[test]
fn sketch_rejects_unsupported_children_instead_of_skipping_them() {
    let (run, compiler) =
        super::execute("sketch:\n    have fn identity(x R) R = x\n    identity(2) = 2\n");
    let error = compiler
        .compile_run(&run, "unsupported_sketch_child")
        .unwrap_err();
    assert!(
        error.to_string().contains("Function/LocalDeclaration"),
        "{error}"
    );
}

#[test]
fn sketch_rejects_failed_child_even_inside_a_success_wrapper() {
    let (mut run, compiler) = super::execute(ARITHMETIC);
    let command = parse_launch_command(&["-strict".into(), "-e".into(), "1 = 2".into()]).unwrap();
    let mut other =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let mut failed = other.run_litex_code("1 = 2").unwrap();
    assert!(!failed.success);
    sketch_mut(&mut run.statement_results[0])
        .proof_steps
        .push(failed.statement_results.remove(0));
    assert!(compiler.compile_run(&run, "failed_sketch_child").is_err());
}

#[test]
fn sketches_replay_nested_blocks_outer_parameters_and_tuple_wd() {
    for source in [
        include_str!("../../../lean/examples/nested_arithmetic_sketch/statement.lit"),
        include_str!("../../../lean/examples/sketch_in_named_theorem/statement.lit"),
        include_str!("../../../lean/examples/local_tuple_sketch/statement.lit"),
        include_str!("../../../lean/examples/local_finite_set_sketch/statement.lit"),
        "have a R\nsketch:\n    a + 0 = a\na = a\n",
        "sketch:\n    have b R = 2\n    b + 1 = 3\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(run.success, "source must verify: {source}");
        let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(runtime);
        let lean = compiler.compile_run(&run, "nested_sketch").unwrap();
        assert_eq!(lean, compiler.compile_run(&run, "nested_sketch").unwrap());
        assert!(!lean.contains("sorry"));
        assert!(lean.len() < 80_000);
    }
}

#[test]
fn a_nested_sketch_keeps_its_original_source_steps() {
    let source = include_str!("../../../lean/examples/sketch_in_named_theorem/statement.lit");
    let (mut run, compiler) = super::execute(source);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!()
    };
    sketch_mut(&mut body.proof_steps[0]).proof_steps.clear();
    assert!(compiler.compile_run(&run, "missing_sketch_step").is_err());
}

#[test]
fn nested_sketch_fact_is_hidden_from_parent_and_sibling() {
    let (run, compiler) = super::execute(
        "sketch:\n    sketch:\n        let hidden = 2\n    sketch:\n        1 = 1\n",
    );
    let parent = sketch(&run.statement_results[0]);
    let child = sketch(&parent.proof_steps[0]);
    let sibling = sketch(&parent.proof_steps[1]);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(alias)),
    )) = &child.proof_steps[0]
    else {
        panic!()
    };
    let id = alias.stored_fact_ids[0];
    let run_position = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let outer = SourcePosition::new(Some(&run_position), SourceOwner::Sketch(parent), 1);
    let inside = SourcePosition::new(Some(&outer), SourceOwner::Sketch(child), 1);
    let beside = SourcePosition::new(Some(&outer), SourceOwner::Sketch(sibling), 0);
    assert!(compiler.cited_fact_reference(id, &inside).is_ok());
    assert!(compiler.cited_fact_reference(id, &outer).is_err());
    assert!(compiler.cited_fact_reference(id, &beside).is_err());
}

#[test]
fn sketch_cached_wd_requires_its_visible_original_producer() {
    let (run, compiler) = super::execute(
        "sketch:\n    let fraction = 1 / 2\n    let copy = 1 / 2\n    fraction = copy\n",
    );
    let p = sketch(&run.statement_results[0]);
    let alias = super::let_definition(&p.proof_steps[1]);
    let VerifyObjWellDefinedResult::Success(wd) = &alias.value_well_defined else {
        panic!("repeated fraction cites original WD")
    };
    assert!(matches!(
        wd.as_detailed().unwrap(),
        DetailedObjWellDefinedProof::ByKnown { .. }
    ));
    let run_position = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let before = SourcePosition::new(Some(&run_position), SourceOwner::Sketch(p), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(compiler.compile_wd(wd, &before).is_err());
    assert!(compiler.compile_wd(wd, &after).is_ok());
    assert!(compiler
        .compile_wd(
            wd,
            &SourcePosition {
                before: 1,
                ..run_position
            }
        )
        .is_err());
}
