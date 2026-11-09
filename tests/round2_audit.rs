use litex::ast::obj::Obj;
use litex::ast::stmt::{CommandStmt, Stmt};
use litex::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal;
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;
use litex::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn object(rt: &mut Runtime, text: &str) -> Obj {
    let blocks = Tokenizer::new()
        .tokenize(&format!("eval {text}"), rt.current_file.clone())
        .unwrap();
    let Stmt::Command(CommandStmt::EvalStmt(stmt)) = rt.parse(&blocks).unwrap().remove(0) else {
        panic!("expected eval");
    };
    stmt.obj_to_eval
}

#[test]
fn multivariable_alpha_preserves_relation_kind_and_polarity() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn f(p finite_seq(R, 2)) R = p(1)^2 + p(2)^2")
            .unwrap()
            .success
    );
    for prefix in ["", "not "] {
        let a = object(
            &mut rt,
            &format!("{{p finite_seq(R,2): {prefix}$has_multi_limit_at(f,p,2,0)}}"),
        );
        let renamed = object(
            &mut rt,
            &format!("{{q finite_seq(R,2): {prefix}$has_multi_limit_at(f,q,2,0)}}"),
        );
        let b = object(
            &mut rt,
            &format!("{{q finite_seq(R,2): {prefix}$has_laplacian_at(f,q,2,0)}}"),
        );
        assert!(compound_objs_alpha_equal(&a, &renamed));
        assert!(!compound_objs_alpha_equal(&a, &b));
    }
    let result = rt.run_litex_code("{p finite_seq(R,2): $has_multi_limit_at(f,p,2,0)} = {q finite_seq(R,2): $has_laplacian_at(f,q,2,0)}").unwrap();
    assert!(
        !result.success,
        "different predicates must not establish set equality"
    );
    assert!(!rt.run_litex_code("0 = 4").unwrap().success);
    assert!(rt.run_litex_code("1 + 1 = 2").unwrap().success);
}

#[test]
fn multivariable_selector_alpha_covers_every_existing_constructor() {
    let mut rt = runtime();
    for call in [
        "lim_multi_at(p,p,2)",
        "lim_vector_at(p,p,2,3)",
        "partial_derivative(p,p,2,1)",
        "scalar_differential(p,p,2)",
        "differential(p,p,2,3)",
        "gradient_at(p,p,2)",
        "jacobian(p,p,2,3)",
        "hessian(p,p,2)",
        "divergence(p,p,2)",
        "curl(p,p)",
        "laplacian(p,p,2)",
    ] {
        let a = object(&mut rt, &format!("fn(p R) R {{{call}}}"));
        let b = object(
            &mut rt,
            &format!(
                "fn(q R) R {{{}}}",
                call.replace("(p", "(q").replace(",p", ",q")
            ),
        );
        assert!(compound_objs_alpha_equal(&a, &a), "reflexivity: {call}");
        assert!(compound_objs_alpha_equal(&a, &b), "bound rename: {call}");
    }
    let a = object(&mut rt, "fn(p R) R {gradient_at(p,p,2)}");
    let b = object(&mut rt, "fn(p R) R {laplacian(p,p,2)}");
    assert!(!compound_objs_alpha_equal(&a, &b));
}

#[test]
fn closed_range_has_two_arithmetic_endpoints() {
    let mut rt = runtime();
    let actual = object(&mut rt, "1 + 1 ... 2 * 3 - 1");
    let expected = object(&mut rt, "closed_range(1 + 1, 2 * 3 - 1)");
    assert_eq!(actual, expected);
    assert!(rt.run_litex_code("2 $in 1 + 1 ... 3").unwrap().success);
}

#[test]
fn continued_headers_and_blank_comments_preserve_body_indentation() {
    let mut rt = runtime();
    for code in [
        concat!(r"forall x R, \\", "\n    y R:\n    x + y = y + x"),
        "forall x R:\n\n# comment\n    x = x",
    ] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(
            run.success,
            "{code}\n{}",
            litex::json_output::emit_run_normal(&run, &rt, "round2", None)
        );
    }
    assert!(Tokenizer::new()
        .tokenize("forall x R:\n\nx=x", rt.current_file.clone())
        .is_err());
}

fn compile_checked(source: &str) -> String {
    let mut rt = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        litex::result_detail::OutputDetail::Detailed,
    );
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success,
        "{}",
        litex::json_output::emit_run_normal(&run, &rt, "round2", None)
    );
    litex::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "round2")
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
}

#[test]
fn sequence_carrier_aliases_expand_and_replay() {
    for source in [
        "have A set = finite_seq(R,2)\nhave f A\nf(1) $in R",
        "have A set = seq(R)\nhave f A\nf(1) $in R",
        "have A set = matrix(R,2,2)\nhave f A = zero_matrix(2,2)\nf(1,1) $in R",
        "have A set = power_set(R)\nhave x A\nx $subset R",
        "have a Z = 3\nforall x closed_range(a,3):\n    x $in Z",
    ] {
        compile_checked(source);
    }
}

#[test]
fn negative_exist_keeps_reciprocal_domain_guard() {
    compile_checked("forall a R:\n    not exist x R st {x != 0, 1 / x = 2}\n    a != 0\n    =>:\n        1 / a != 2");
}

#[test]
fn template_value_definitions_keep_callable_carrier() {
    let source =
        "template<T set>:\n    have identity fn(x T) T = fn(x T) T {x}\n\\identity<R>(1) $in R";
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success,
        "{}",
        litex::json_output::emit_run_normal(&run, &rt, "round2", None)
    );
    assert!(!rt.run_litex_code("\\identity<R>(1,2) = 1").unwrap().success);
    let mut rt = runtime();
    let source = include_str!("../examples/wd/template_value_callable.lit");
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success,
        "{}",
        litex::json_output::emit_run_normal(&run, &rt, "template", None)
    );
}

#[test]
fn extraction_avoids_library_shadowing_and_duplicate_sign_evaluation() {
    let source = "have math R = 2\nhave p R = pi\nalgo choose(int R) R by cases:\n    case int = int: sign(sign(int))";
    let python = litex::extract_executable_code::to_python_from_source(source).unwrap();
    assert!(python.contains("__litex_user_math = 2.0"), "{python}");
    assert!(python.contains("def choose(__litex_user_int):"), "{python}");
    assert!(
        python.contains("__litex_sign(__litex_sign(__litex_user_int))"),
        "{python}"
    );
    let run = std::process::Command::new("python3")
        .arg("-c")
        .arg(format!("{python}\nassert choose(-4) == -1\nassert p > 3\n"))
        .output()
        .unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let c = litex::extract_executable_code::to_c_from_source("algo choose(litex_sign R) R by cases:\n    case litex_sign = litex_sign: sign(sign(litex_sign))").unwrap();
    assert!(c.contains("choose(double litex_user_litex_sign)"), "{c}");
    assert!(
        c.contains("litex_sign(litex_sign(litex_user_litex_sign))"),
        "{c}"
    );
}

#[test]
fn latex_groups_powers_and_uses_distinct_dummy_names() {
    let latex = litex::compile_to_latex::to_latex_from_source(
        "have x R\nhave iota Z\n(-x)^2 = x^2\nrange(0,iota) = range(0,iota)",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(latex.contains(r"\left(-x\right)^{2}"), "{latex}");
    assert!(latex.contains(r"\iota < \mathit{iota}"), "{latex}");
}

#[test]
fn binder_carriers_do_not_capture_the_name_being_declared() {
    let mut rt = runtime();
    let builder = object(&mut rt, "{x R: x = x}");
    let equivalent = object(&mut rt, "{y R: y = y}");
    assert!(compound_objs_alpha_equal(&builder, &equivalent));
    assert!(
        !runtime()
            .run_litex_code("forall x {x}:\n    x = x")
            .unwrap()
            .success
    );
    assert!(
        !runtime()
            .run_litex_code("eval {x {x}: x = x}")
            .unwrap()
            .success
    );
}

#[test]
fn predicate_witness_private_names_do_not_conflict_with_local_proof_names() {
    compile_checked("prop P(x R):\n    exist hidden R st {hidden = x}\nwitness $P(1) from 1:\n    have hidden R = 2\n    hidden = 2\n$P(1)");
}

#[test]
fn selector_values_can_use_later_candidates_and_direct_equalities() {
    compile_checked("forall a seq(R):\n    $has_seq_limit(a,1+1)\n    =>:\n        lim(a) = 2");
    compile_checked("forall f fn(p finite_seq(R,2)) R, a,g,h finite_seq(R,2):\n    $has_gradient_at(f,a,2,g)\n    $has_gradient_at(f,a,2,h)\n    =>:\n        gradient_at(f,a,2) = h");
}

#[test]
fn exports_retain_obtained_facts_and_registered_properties() {
    use std::fs;
    let root = std::env::temp_dir().join(format!("litex-round2-modules-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("litex.config"),
        "[export]\nfirst = \"./first.lit\"\nsecond = \"./second.lit\"\n",
    )
    .unwrap();
    fs::write(root.join("first.lit"), "prop same(x,y set):\n    x = y\nregister symmetric:\n    ? forall x,y set:\n        $same(x,y)\n        =>:\n            $same(y,x)\nwitness exist x R st {x=2} from 2\nobtain chosen from exist x R st {x=2}\n1 $same 1\nprop is_one(v R):\n    v=1\nstrategy use_one:\n    ? forall v R:\n        v=1\n        =>:\n            $is_one(v)\n    by def $is_one(v)\n").unwrap();
    fs::write(root.join("second.lit"), "release obj def first::chosen\nfirst::chosen=2\nforall x,y set:\n    $first::same(x,y)\n    =>:\n        $first::same(y,x)\n$first::is_one(1)\n").unwrap();
    let result = litex::run_module::run_project(LaunchCommand::Repository {
        path: root.clone(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(
        result.run.success,
        "module errors: {:?}",
        result.run.session_error
    );
    let lean = std::process::Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-lang", "en", "-strict", "-lean", "-f"])
        .arg(root.join("second.lit"))
        .output()
        .unwrap();
    fs::remove_dir_all(&root).unwrap();
    assert!(
        lean.status.success(),
        "{}",
        String::from_utf8_lossy(&lean.stderr)
    );
}
