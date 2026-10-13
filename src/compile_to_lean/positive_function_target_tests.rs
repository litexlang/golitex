use super::LitexToLeanCompiler;
use crate::prelude::*;

#[test]
fn first_positive_function_keeps_both_inputs_return_guard_and_alias_evidence() {
    let source = "have fn first_positive(x R+, y R+) R+ = x\n\
forall x R+, y R+:\n    first_positive(x, y) = x\n\
first_positive(1, 2) = 1\n\
have fn positive_guard(x R+, y R: y != 0) R+ = x\n\
forall x R+, y R:\n    y != 0\n    =>:\n        positive_guard(x, y) = x\n\
positive_guard(1, 2) = 1\n\
have fn positive_to_real(x R+) R = x\n\
forall x R+:\n    positive_to_real(x) = x\n\
let positive_domain = R+\n\
have fn alias_positive(x positive_domain) positive_domain = x\n\
alias_positive(1) = 1\n\
let reals = R\n\
have fn first_real(x R, y R) reals = x\n\
forall x R, y R:\n    first_real(x, y) = x\n";
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("original source run");
    assert!(result.success && result.session_error.is_none());
    let lean = LitexToLeanCompiler::new(runtime)
        .compile_run(&result, "positive_function_targets")
        .expect("the first function consumes its own completed return-set WD");
    assert!(lean.contains("Litex.formulaFn2Target"));
    assert!(lean.contains("Litex.call2Target"));
    assert!(lean.contains("Litex.positiveRealPredicate"));
    assert!(lean.contains("Litex.RPos"));
}
