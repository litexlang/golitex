use crate::prelude::*;

#[test]
fn builtin_closed_calculation_replays_and_checks_original_normal_forms() {
    for (index, source) in ["2 + 3 = 5\n", "1 / 3 = 2 / 6\n"].iter().enumerate() {
        for corrupt in [false, true] {
            let (mut run, mut compiler) = super::execute(source);
            let proof = super::equality_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
            );
            // Select the real builtin stage, even if the ordinary source run
            // found the equivalent direct calculation stage first.
            let mut selected = compiler
                .runtime
                .search_equal_fact_by_calculation(&proof.fact, VerifyState::top_level())
                .unwrap()
                .unwrap();
            match &mut selected {
                EqualitySearchProofByCalculation::ClosedDecimal { right_normal, .. }
                    if index == 0 =>
                {
                    if corrupt {
                        *right_normal = "6".into();
                    }
                }
                EqualitySearchProofByCalculation::ClosedRational { right_normal, .. }
                    if index == 1 =>
                {
                    if corrupt {
                        *right_normal = "(1 / 2)".into();
                    }
                }
                _ => panic!("the exact builtin calculation family"),
            }
            proof.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Calculation(selected),
            );
            let output = compiler.compile_run(&run, "closed_builtin");
            if corrupt {
                assert!(output.unwrap_err().route.starts_with("ClosedEquality/"));
            } else {
                let output = output.unwrap();
                if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
                    std::fs::write(
                        std::path::Path::new(&directory)
                            .join(format!("builtin_closed_{index}.lean")),
                        output,
                    )
                    .unwrap();
                }
            }
        }
    }
}
