use crate::prelude::*;

fn checked(
    source: &str,
) -> (
    RunLitexCodeResult,
    crate::compile_to_lean::LitexToLeanCompiler,
) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none(), "{source}");
    (
        run,
        crate::compile_to_lean::LitexToLeanCompiler::new(runtime),
    )
}

#[test]
fn tuple_coordinate_inference_compiles_original_stores_and_later_citations() {
    for source in [
        "have p cart(C,C)=(3/5,4/5)\np(1)^2+p(2)^2=1",
        "let p=(3/5,4/5)\np(1)^2+p(2)^2=1",
        "have p set=(3/5,4/5)\np(1)^2+p(2)^2=1",
        "forall p cart(C,C):\n    (3/5,4/5)=p\n    =>:\n        p(1)^2+p(2)^2=1",
        "have a,b C\nhave p cart(C,C)=(a,b)\np(1)=a\np(2)=b",
        "let p=tuple()\np $in cart()",
        "let p=((1,2),3)\np(1)=(1,2)\np(1)(1)+p(1)(2)=3",
    ] {
        let (run, compiler) = checked(source);
        let generated = compiler
            .compile_run(&run, "TupleCoordinateInference")
            .unwrap_or_else(|error| panic!("{source}\n{error}"));
        assert!(!generated.contains("sorry"));
        if !source.contains("tuple()") {
            assert!(generated.contains("Litex.tuple_coordinate"));
        }
    }
}

#[test]
fn tuple_coordinate_inference_rejects_missing_or_reordered_capture() {
    for mutation in 0..4 {
        let (mut run, compiler) = checked("have p cart(C,C)=(3/5,4/5)");
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) = &mut run.statement_results[0]
        else {
            panic!("typed tuple")
        };
        let seed = proof
            .store_and_infer_result
            .store_and_infer_results
            .last_mut()
            .unwrap();
        let seed = std::rc::Rc::get_mut(seed).unwrap();
        let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
            crate::store_fact_and_infer::InferAtomicFactResult::EqualFact(rules),
        )) = &mut seed.infer
        else {
            panic!("equal rules")
        };
        let rule = rules
            .iter_mut()
            .find_map(|r| match r {
                crate::store_fact_and_infer::InferEqualFactResult::TupleCoordinates(r) => Some(r),
                _ => None,
            })
            .unwrap();
        match mutation {
            0 => {
                rule.coordinates.pop();
            }
            1 => rule.coordinates.swap(0, 1),
            2 => rule.source_fact_id = FactId::new(u64::MAX),
            3 => rule.reversed = !rule.reversed,
            _ => unreachable!(),
        }
        proof.store_and_infer_result.stored_fact_ids = proof
            .store_and_infer_result
            .store_and_infer_results
            .iter()
            .flat_map(|stored| stored.stored_fact_ids())
            .collect();
        let error = compiler
            .compile_run(&run, "InvalidTupleCapture")
            .unwrap_err();
        assert_eq!(
            error.route,
            [
                "TupleInference/Arity",
                "TupleInference/Subject",
                "TupleInference/Seed",
                "TupleInference/Constructor"
            ][mutation]
        );
    }
}

#[test]
fn tuple_uniform_membership_replays_arbitrary_valid_index() {
    for source in [
        include_str!("../../../lean/examples/tuple_uniform_variable_index/statement.lit"),
        include_str!("../../../lean/examples/tuple_uniform_function_body/statement.lit"),
    ] {
        let (run, compiler) = checked(source);
        let generated = compiler.compile_run(&run, "uniform_tuple").unwrap();
        assert!(generated.contains("Litex.FiniteFunction.indexSet_members"));
        assert_eq!(
            generated,
            compiler.compile_run(&run, "uniform_tuple").unwrap()
        );
    }
}
