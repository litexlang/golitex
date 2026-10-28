use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

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
fn cart_n_reuses_finite_sequence_semantics_and_existing_outputs() {
    let mut rt = runtime();
    let source = include_str!("../../../examples/test_objs/cart_n.lit");
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "cart_n", None)
    );
    let normal = crate::json_output::emit_run_normal(&run, &rt, "cart_n", None);
    assert!(
        normal.contains("finite_seq("),
        "the existing node keeps its canonical output: {normal}"
    );
}

#[test]
fn cart_n_rejects_wrong_dimensions_indices_and_wide_domains_without_losing_context() {
    for target in [
        "let bad=cart_n(R,-1)",
        "let bad=cart_n(R,1/2)",
        "v(0)=0",
        "v $in cart_n(R,2)",
        "wide $in cart_n(R,3)",
        "release thm fn_set_member(wide,cart_n(R,3))",
        "let bad=cart_n(R)",
        "let bad=cart_n(R,2,3)",
    ] {
        let mut rt = runtime();
        assert!(
            rt.run_litex_code("have v cart_n(R,3)=(1,2,3)\nhave fn wide(k N+) R=k\n")
                .unwrap()
                .success
        );
        let run = rt.run_litex_code(target).unwrap();
        assert!(!run.success, "unexpected acceptance: {target}");
        assert!(
            run.session_error.is_none(),
            "ordinary rejection terminated the session: {target}"
        );
        assert!(
            rt.run_litex_code("v(2)=2\n").unwrap().success,
            "earlier context was lost: {target}"
        );
    }
}

#[test]
fn cart_n_is_reserved_as_a_builtin_constructor() {
    let mut rt = runtime();
    let run = rt.run_litex_code("let cart_n=0\n").unwrap();
    assert!(!run.success);
    assert!(
        format!("{:?}{:?}", run.input_error, run.session_error).contains("reserved builtin name")
    );
}
