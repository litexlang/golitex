use litex::extract_executable_code::{
    to_c_from_repository, to_c_from_source, to_python_from_repository, to_python_from_source,
};
use litex::launch_command::OutputLanguage;
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Scratch(PathBuf);
impl Scratch {
    fn new(label: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "litex-output-round2-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn python(program: &str) {
    let output = Command::new("python3")
        .args(["-c", program])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn c_run(program: &str, main: &str) {
    let scratch = Scratch::new("c");
    scratch.write("program.c", &format!("{program}\n{main}"));
    let output = Command::new("clang")
        .args([
            "-std=c99",
            "-fsanitize=undefined,float-cast-overflow",
            "-fno-sanitize-recover=all",
        ])
        .arg(scratch.0.join("program.c"))
        .arg("-lm")
        .arg("-o")
        .arg(scratch.0.join("program"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{program}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(scratch.0.join("program")).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "requires Python 3"]
fn python_runtime_names_and_nested_sign_execute_once() {
    let source = "have math R=2\nhave p R=pi\nalgo base(x R) R by cases:\n    case x=x: x\nalgo nested(int R) R by cases:\n    case int=int: sign(sign(base(int)))\n";
    let generated = to_python_from_source(source).unwrap();
    python(&format!("{generated}\nassert __litex_user_math == 2\nassert p > 3\noriginal = base\ncalls = 0\ndef counted(x):\n    global calls\n    calls += 1\n    return original(x)\nbase = counted\nassert nested(-4) == -1\nassert calls == 1\n"));
    let deep = format!(
        "algo nested(x R) R by cases:\n    case x=x: {}x{}\n",
        "sign(".repeat(18),
        ")".repeat(18)
    );
    let generated = to_python_from_source(&deep).unwrap();
    assert!(
        generated.len() < 2000,
        "nested sign must have linear output size"
    );
    python(&format!("{generated}\nassert nested(-2) == -1\n"));
}

#[test]
#[ignore = "requires clang with UBSan"]
fn c_runtime_namespace_and_integer_helpers_have_no_undefined_behavior() {
    let source = "have rand R=7\nhave litex_user_rand R=8\nalgo nested(litex_sign R) R by cases:\n    case litex_sign=litex_sign: sign(sign(litex_sign))\nalgo extreme(x R) R by cases:\n    case x=x: lcm(-9223372036854775808,1)\nalgo large(x R) R by cases:\n    case x=x: lcm(4294967295,4294967296)\nalgo factorial_value(x R) R by cases:\n    case x=x: factorial(10)\n";
    let generated = to_c_from_source(source).unwrap();
    c_run(&generated, "int main(void) {\n    if (litex_user_rand != 7.0 || litex_user_litex_user_rand != 8.0) return 1;\n    if (nested(-4.0) != -1.0) return 2;\n    if (extreme(0.0) != 9223372036854775808.0) return 3;\n    if (large(0.0) != 18446744069414584320.0) return 4;\n    if (factorial_value(0.0) != 3628800.0) return 5;\n    if (!isinf(litex_factorial(171.0))) return 6;\n    return 0;\n}");
}

#[test]
#[ignore = "requires clang with UBSan"]
fn c_division_is_the_same_floating_operation_in_constants_and_functions() {
    let generated =
        to_c_from_source("have ratio R=-3/2\nalgo quotient(x R) R by cases:\n    case x=x: -3/2\n")
            .unwrap();
    c_run(
        &generated,
        "int main(void) { return ratio == -1.5 && quotient(0.0) == ratio ? 0 : 1; }",
    );
}

#[test]
#[ignore = "requires Python 3 and clang with UBSan"]
fn extraction_rejects_duplicate_names_across_exports_without_partial_output() {
    let scratch = Scratch::new("duplicates");
    scratch.write(
        "litex.config",
        "[export]\nfirst=\"./first.lit\"\nsecond=\"./second.lit\"\n",
    );
    scratch.write("first.lit", "have shared R=1\n");
    scratch.write("second.lit", "have shared R=2\n");
    for error in [
        to_c_from_repository(scratch.0.to_str().unwrap()).unwrap_err(),
        to_python_from_repository(scratch.0.to_str().unwrap()).unwrap_err(),
    ] {
        assert!(
            error
                .to_string()
                .contains("duplicate extracted name `shared`"),
            "{error}"
        );
    }
    scratch.write("second.lit", "have other R=2\n");
    let c = to_c_from_repository(scratch.0.to_str().unwrap()).unwrap();
    c_run(
        &c,
        "int main(void) { return shared == 1.0 && other == 2.0 ? 0 : 1; }",
    );
    let py = to_python_from_repository(scratch.0.to_str().unwrap()).unwrap();
    python(&format!("{py}\nassert shared == 1.0 and other == 2.0\n"));
}

#[test]
#[ignore = "requires XeLaTeX and its documented fonts"]
fn latex_nested_operators_remain_grouped_and_dummy_names_do_not_capture_ascii_names() {
    let source = "have A,B,matrixC matrix(R,2,2)\nhave x,xi,iota R\n(-x)^2=x^2\ntranspose(transpose(A,2,2),2,2)=A\nmatrix_inv(transpose(A,2,2),2)=A\nmatrix_mul(matrix_add(A,B,2,2),matrixC,2,2,2)=A\nrange(0,iota)=range(0,iota)\nintegral(fn(t R) R {t+xi},0,1)=1\n";
    let fragment =
        litex::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(fragment.contains(r"\left(-x\right)^{2}"), "{fragment}");
    assert!(
        fragment.contains(r"\left(A^{\mathsf{T}}\right)_{[2,2]}^{\mathsf{T}}"),
        "{fragment}"
    );
    assert!(
        fragment.contains(r"\left(A^{\mathsf{T}}\right)_{[2,2]}^{-1}"),
        "{fragment}"
    );
    assert!(
        fragment.contains(r"\left(A + B\right)_{[2,2]}\,\mathit{matrixC}"),
        "{fragment}"
    );
    assert!(fragment.contains(r"\iota < \mathit{iota}"), "{fragment}");
    assert!(fragment.contains(r"\mathit{xi}"), "{fragment}");
    assert!(!fragment.contains(r"^{\mathsf{T}}^{\mathsf{T}}"));
    let scratch = Scratch::new("latex");
    let document = litex::compile_to_latex::to_latex_document(&fragment, OutputLanguage::English);
    scratch.write("document.tex", &document);
    let output = Command::new("xelatex")
        .args(["-interaction=nonstopmode", "-halt-on-error", "document.tex"])
        .current_dir(&scratch.0)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(!String::from_utf8_lossy(&output.stdout).contains("Missing character:"));
}

#[test]
fn latex_selected_export_includes_each_preceding_file_once() {
    let scratch = Scratch::new("latex-project");
    scratch.write(
        "litex.config",
        "[export]\nfirst=\"./first.lit\"\nsecond=\"./second.lit\"\n",
    );
    scratch.write("first.lit", "have first_value R=1\n");
    scratch.write("second.lit", "have second_value R=first::first_value\n");
    let fragment = litex::compile_to_latex::to_latex_from_file(
        scratch.0.join("second.lit").to_str().unwrap(),
        OutputLanguage::English,
    )
    .unwrap();
    assert_eq!(
        fragment.matches(r"\section*{first}").count(),
        1,
        "{fragment}"
    );
    assert_eq!(
        fragment.matches(r"\section*{second}").count(),
        1,
        "{fragment}"
    );
}

#[test]
fn latex_mounts_distinct_transitive_packages_with_the_same_local_alias() {
    let scratch = Scratch::new("latex-transitive");
    scratch.write(
        "litex.config",
        "[import]\nA=\"./a\"\nB=\"./b\"\n[export]\nmain=\"./main.lit\"\n",
    );
    for package in ["a", "b"] {
        scratch.write(
            &format!("{package}/litex.config"),
            "[import]\nUtil=\"./dep\"\n[export]\napi=\"./api.lit\"\n",
        );
        scratch.write(
            &format!("{package}/api.lit"),
            "have number R=Util::values::number\n",
        );
        scratch.write(
            &format!("{package}/dep/litex.config"),
            "[export]\nvalues=\"./values.lit\"\n",
        );
        scratch.write(&format!("{package}/dep/values.lit"), "have number R=1\n");
    }
    scratch.write(
        "main.lit",
        "have left R=A::api::number\nhave right R=B::api::number\n",
    );
    let fragment = litex::compile_to_latex::to_latex_from_file(
        scratch.0.join("main.lit").to_str().unwrap(),
        OutputLanguage::English,
    )
    .unwrap();
    assert!(fragment.contains("A::api::number"), "{fragment}");
    assert!(fragment.contains("B::api::number"), "{fragment}");
}
