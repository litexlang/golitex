use crate::prelude::*;

const SOURCE: &str = include_str!(
    "../../../../examples/proof_nodes/equal/by_builtin_strategy/matrix_structural_equality.lit"
);

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

#[test]
fn native_matrix_structural_thirteen_independent_goals() {
    let mut count = 0;
    for source in SOURCE.split("\n\n").filter(|s| s.starts_with("forall")) {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(
            run.success,
            "{source}\n{}",
            crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify()
        );
        let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(json.contains("MatrixStructuralEquality"), "{source}");
        assert!(json.contains("MatrixEntryReduction"), "{source}");
        count += 1;
    }
    assert_eq!(count, 13);
}

#[test]
fn native_matrix_structural_false_controls_and_failed_scope_retention() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have retained N = 2").unwrap().success);
    for source in [
        "forall m,n N,z C,A matrix(C,m,n):\n    conjugate_transpose(matrix_scale(z,A,m,n),m,n)=matrix_scale(z,conjugate_transpose(A,m,n),n,m)",
        "forall m,n N,A,B matrix(C,m,n):\n    matrix_sub(A,B,m,n)=matrix_sub(B,A,m,n)",
        "forall m,n N,A matrix(C,m,n):\n    transpose(A,m,n)=A",
        "forall m,n N,A matrix(C,m,n):\n    matrix_scale(2,A,m,n)=A",
    ] {
        let run=rt.run_litex_code(source).unwrap();
        assert!(!run.success,"{source}");
        assert!(run.session_error.is_none(),"{source}");
        assert!(rt.run_litex_code("retained+0=2").unwrap().success);
    }
}

#[test]
fn native_matrix_structural_reverse_nested_and_empty_dimensions() {
    for source in [
        "forall m,n N,A matrix(C,m,n):\n    A=transpose(transpose(A,m,n),n,m)",
        "forall m,n N,A matrix(C,m,n):\n    matrix_scale(2,matrix_add(A,A,m,n),m,n)=matrix_scale(4,A,m,n)",
        "forall n N,A matrix(C,0,n):\n    transpose(transpose(A,0,n),n,0)=A",
        "forall m N,A matrix(C,m,0):\n    matrix_add(A,zero_matrix(m,0),m,0)=A",
    ] {
        let run=runtime().run_litex_code(source).unwrap();
        assert!(run.success,"{source}");
    }
}

fn fact(rt: &mut Runtime, source: &str) -> Fact {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(fact) = statements.remove(0) else {
        panic!("fact")
    };
    fact
}

#[test]
fn native_matrix_structural_preserves_search_permissions_and_parent_scope() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have A matrix(C,1,1) = zero_matrix(1,1)")
            .unwrap()
            .success
    );
    let goal = fact(&mut rt, "matrix_add(A,A,1,1)=matrix_scale(2,A,1,1)");
    let sizes = |rt: &Runtime| {
        rt.execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect::<Vec<_>>()
    };
    let before = sizes(&rt);
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
        VerifyStateLevel::BuiltinRule,
    ] {
        assert!(
            rt.verify_fact(&goal, VerifyState::new(level))
                .unwrap()
                .is_failed(),
            "{level:?}"
        );
        assert_eq!(sizes(&rt), before);
    }
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Strategy))
        .unwrap()
        .is_failed());
    assert_eq!(sizes(&rt), before);
}

#[test]
fn native_matrix_structural_entry_expansion_respects_size_and_depth_limits() {
    let mut rt = runtime();
    let Fact::AtomicFact(AtomicFact::EqualFact(goal)) = fact(&mut rt, "0=0") else {
        panic!()
    };
    let state = VerifyState::new(VerifyStateLevel::BuiltinRule);
    let mut remaining = 0;
    assert!(rt
        .normalize_matrix_entry(&goal.left, state, 0, &mut remaining)
        .unwrap()
        .is_none());
    let mut remaining = 1;
    assert!(rt
        .normalize_matrix_entry(&goal.left, state, 0, &mut remaining)
        .unwrap()
        .is_some());
    assert_eq!(remaining, 0);
    let mut remaining = 256;
    assert!(rt
        .normalize_matrix_entry(&goal.left, state, 32, &mut remaining)
        .unwrap()
        .is_none());
}

#[test]
fn native_matrix_structural_reading_retains_checked_entry_evidence() {
    let result = crate::reading::build_reading(
        &crate::reading::ReadingInput::Source(
            "forall m,n N,A matrix(C,m,n):\n    transpose(transpose(A,m,n),n,m)=A".into(),
        ),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let json = result.document.stringify();
    for evidence in [
        "MatrixStructuralEquality",
        "MatrixEntryReduction",
        "MatrixEntryNormalizationProof",
        "MatrixEntryNormalizationStep",
        "FunctionDomainMatchProof",
    ] {
        assert!(json.contains(evidence), "{evidence}");
    }
}
