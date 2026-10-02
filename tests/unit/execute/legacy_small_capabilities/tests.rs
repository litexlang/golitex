use crate::json_output::emit_run_detailed;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(source: &str, expected: bool) {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut runtime = Runtime::new(LaunchCommand::Eval {
                code: String::new(), session: false, strict: true,
                language: OutputLanguage::English,
            });
            let result = runtime.run_litex_code(&source).expect("run code");
            assert_eq!(result.success, expected, "{}\n{}", source,
                emit_run_detailed(&result, &runtime, "eval", None));
        }).unwrap().join().unwrap();
}

#[test]
fn legacy_small_prime_definition_projection() {
    check("forall p N:\n    $prime(p)\n    =>:\n        2 <= p", true);
    check("forall p N:\n    $prime(p)\n    =>:\n        3 <= p", false);
}

#[test]
fn legacy_small_coprime_definition_projection() {
    check("forall a, b N:\n    $coprime(a, b)\n    =>:\n        gcd(a, b) = 1", true);
    check("forall a, b N:\n    $coprime(a, b)\n    =>:\n        gcd(a, b) = 2", false);
}

#[test]
fn legacy_small_rounding_identities() {
    check("forall x R:\n    floor(-x) = -ceil(x)", true);
    check("forall x R, n Z:\n    floor(x + n) = floor(x) + n", true);
    check("forall x R:\n    floor(x + 0.5) = floor(x) + 0.5", false);
}

#[test]
fn legacy_small_extrema_absorption() {
    check("forall a, b R:\n    min(a, max(a, b)) = a", true);
    check("forall a, b R:\n    max(a, min(a, b)) = a", true);
}
