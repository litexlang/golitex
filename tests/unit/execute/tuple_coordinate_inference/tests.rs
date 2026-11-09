use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferEqualFactResult, InferResult};

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
fn round2_mismatched_tuple_lengths_do_not_publish_a_truncated_prefix() {
    let mut rt = runtime();
    let tuple = |values: &[i64]| {
        Obj::ProductShape(ProductShape::Tuple(Tuple {
            args: values
                .iter()
                .map(|value| {
                    Box::new(Obj::Literal(Literal::Number(Number::new(
                        value.to_string(),
                    ))))
                })
                .collect(),
        }))
    };
    for (left, right) in [
        (tuple(&[1, 2, 3]), tuple(&[4, 5])),
        (tuple(&[4, 5]), tuple(&[1, 2, 3])),
    ] {
        let source = EqualFact {
            fact_id: rt.global_ids.allocate_fact_id(),
            left,
            right,
            line_file: None,
        };
        assert!(rt
            .infer_equal_fact_tuple_coordinates(&source)
            .unwrap()
            .is_none());
        assert!(rt.top_exec_env().facts.facts_by_id.is_empty());
    }
}

fn exec(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1);
    rt.exec_stmt(&statements[0]).unwrap()
}

fn equalities(rt: &Runtime) -> Vec<String> {
    rt.execution_environments_stack
        .iter()
        .flat_map(|env| env.facts.facts_by_id.values())
        .filter_map(|fact| match fact {
            Fact::AtomicFact(AtomicFact::EqualFact(equal)) => {
                Some(Fact::from(equal.clone()).readable_string())
            }
            _ => None,
        })
        .collect()
}

#[test]
fn tuple_coordinate_inference_publishes_values_before_any_projection_query() {
    let mut rt = runtime();
    let result = exec(&mut rt, "have tilted cart_n(C,2) = (3/5,4/5)");
    assert!(!result.is_failed());
    let facts = equalities(&rt);
    assert!(
        facts.iter().any(|f| f == "tilted(1) = (3 / 5)"),
        "{facts:?}"
    );
    assert!(
        facts.iter().any(|f| f == "tilted(2) = (4 / 5)"),
        "{facts:?}"
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &result
    else {
        panic!("typed equality")
    };
    let seed = proof
        .store_and_infer_result
        .store_and_infer_results
        .last()
        .unwrap();
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &seed.infer else {
        panic!("equality inference")
    };
    let rule = rules
        .iter()
        .find_map(|r| match r {
            InferEqualFactResult::TupleCoordinates(r) => Some(r),
            _ => None,
        })
        .unwrap();
    assert_eq!(rule.source_fact_id, seed.primary_fact_id());
    assert_eq!(rule.coordinates.len(), 2);
    assert!(rule
        .coordinates
        .iter()
        .all(|c| c.primary_fact_id() != rule.source_fact_id));
    let detailed = crate::json_output::project_stmt_detailed(&result, &rt).stringify();
    assert!(detailed.contains("TupleCoordinates"));
    assert!(!exec(&mut rt, "tilted(1)^2 + tilted(2)^2 = 1").is_failed());
}

#[test]
fn tuple_coordinate_inference_handles_reverse_assumptions_and_let_values() {
    for source in [
        "let p=(3/5,4/5)\np(1)^2+p(2)^2=1",
        "forall p cart(C,C):\n    (3/5,4/5)=p\n    =>:\n        p(1)^2+p(2)^2=1",
        "have a,b C\nhave p cart(C,C)=(a,b)\np(1)=a\np(2)=b",
        "let p=(7,)\np(1)+1=8",
        "let p=tuple()\np $in cart()",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "{source}\n{}",
            crate::json_output::emit_run_detailed(&run, &rt, "tuple", None)
        );
    }
}

#[test]
fn tuple_coordinate_inference_is_one_layer_and_scope_local() {
    let mut rt = runtime();
    assert!(!exec(&mut rt, "let p=((1,2),3)").is_failed());
    let facts = equalities(&rt);
    assert!(facts.iter().any(|f| f == "p(1) = (1, 2)"), "{facts:?}");
    assert!(!facts.iter().any(|f| f.starts_with("p(1)(")), "{facts:?}");
    let before = facts.len();
    assert!(!exec(
        &mut rt,
        "forall q cart(C,C):\n    q=(3/5,4/5)\n    =>:\n        q(1)^2+q(2)^2=1"
    )
    .is_failed());
    assert_eq!(
        equalities(&rt).len(),
        before,
        "local coordinates must not leak"
    );
    assert!(exec(
        &mut rt,
        "claim:\n    ? 1=2\n    have doomed cart(C,C)=(3/5,4/5)"
    )
    .is_failed());
    assert_eq!(
        equalities(&rt).len(),
        before,
        "failed statement must roll back its coordinates"
    );
}

#[test]
fn tuple_coordinate_inference_keeps_false_and_invalid_coordinates_rejected() {
    let mut rt = runtime();
    assert!(!exec(&mut rt, "have p cart(C,C)=(3/5,4/5)").is_failed());
    for source in [
        "p(1)=4/5",
        "p(2)=3/5",
        "p(0)=0",
        "p(3)=0",
        "p(1)^2+p(2)^2=2",
    ] {
        assert!(exec(&mut rt, source).is_failed(), "{source}");
    }
    assert!(!exec(&mut rt, "p(1)^2+p(2)^2=1").is_failed());
}
