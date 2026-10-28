use crate::prelude::*;

#[test]
fn complex_square_does_not_prove_negative_absolute_value() {
    let mut rt = runtime();
    let run = rt.run_litex_code("abs(i^2)=i^2").unwrap();
    assert!(!run.success);
    assert!(run.session_error.is_none());

    for source in ["i^2=-1", "0<=abs(i^2)"] {
        assert!(rt.run_litex_code(source).unwrap().success, "{source}");
    }
    for source in ["abs(i^2)=-1", "0<=-1"] {
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(run.session_error.is_none(), "{source}");
    }
}

#[test]
fn real_square_identity_retains_its_domain_proof() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have a R").unwrap().success);
    let run = rt.run_litex_code("abs(a^2)=a^2").unwrap();
    assert!(run.success);
    let detail =
        crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
    assert!(detail.contains("\"rule\": \"AbsSquare\""), "{detail}");
    assert!(detail.contains("\"base_real\""), "{detail}");
    assert!(detail.contains("a $in R"), "{detail}");
    assert!(detail.contains("cite_fact_id"), "{detail}");
}

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
