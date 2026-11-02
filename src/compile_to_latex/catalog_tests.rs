//! Per-type rendering contract, including nested method and object forms.
use super::*;
use crate::ast::{obj::*, stmt::*};
use crate::knowledge_base::{JsonObject, JsonValue};
use crate::launch_command::{LatexInput, LaunchCommand, OutputLanguage};
use crate::module_manager::{LitexConfig, LitexConfigExport, LitexConfigImport};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;
use std::{collections::BTreeSet, fs, path::PathBuf};

#[path = "catalog_kinds.rs"]
mod kinds;

fn string<'a>(row: &'a JsonValue, key: &str) -> &'a str {
    row.as_object().unwrap().get(key).unwrap().as_str().unwrap()
}
fn runtime(language: OutputLanguage) -> Runtime {
    let mut runtime = Runtime::new(LaunchCommand::CompileToLatex {
        input: LatexInput::Code(String::new()),
        language,
        document: false,
    });
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/compile_to_latex/catalog_namespace");
    let mut config = LitexConfig::new();
    config.exports.push(LitexConfigExport::new(
        "alpha".into(),
        root.join("alpha.lit"),
    ));
    config
        .imports
        .push(LitexConfigImport::new("dep".into(), root.join("dep")));
    runtime.global_module_manager.set_root_config(config);
    let mut imported = LitexConfig::new();
    imported.exports.push(LitexConfigExport::new(
        "beta".into(),
        root.join("dep/beta.lit"),
    ));
    runtime
        .global_module_manager
        .mount_module("dep".into(), root.join("dep"), imported)
        .unwrap();
    runtime
}
fn parse(runtime: &mut Runtime, source: &str) -> Vec<Stmt> {
    let blocks = Tokenizer::new()
        .tokenize(source, runtime.current_file.clone())
        .unwrap();
    runtime
        .parse(&blocks)
        .unwrap_or_else(|error| panic!("{source}\n{error}"))
}
const OBJECT_CONTEXT: &str = "have A, B, S, X, I, F set\nhave a, b, c, d, m, n, k, j, x, y, z, u, v, p, q, s, f, g, op set\nstruct Point<T set>:\n    value T\n    other T\ntemplate<T set>:\n    have carrier set = T\n";

#[test]
fn named_function_operands_are_natural_and_composite_functions_stay_grouped() {
    for (source, expected) in [
        ("integral(f,a,b)", r"\int_{a}^{b} f(\xi)"),
        ("derivative(f,a)", r"f^{\prime}"),
        ("gradient_at(f,a,n)", r"\nabla f"),
        ("lim(a)", r"\lim_{n\to\infty} a(n)"),
        ("sum(a,b,f)", r"\sum_{\iota=a}^{b} f(\iota)"),
        ("integral(compose(f,g),a,b)", r"\left(f \circ g\right)(\xi)"),
        (
            "derivative(compose(f,g),a)",
            r"\left(f \circ g\right)^{\prime}",
        ),
        (
            "derivative(exp(f),a)",
            r"\left(\mathrm{e}^{f}\right)^{\prime}",
        ),
    ] {
        let mut rt = object_runtime(OutputLanguage::Chinese);
        let ast = parse(&mut rt, &format!("let specimen = {source}"));
        let latex =
            to_latex_from_ast(&ast, &rt.global_module_manager, OutputLanguage::Chinese).unwrap();
        assert!(latex.contains(expected), "{source}: {latex}");
    }
}
fn object_runtime(language: OutputLanguage) -> Runtime {
    let mut rt = runtime(language);
    parse(&mut rt, OBJECT_CONTEXT);
    rt
}
fn object_from(statements: &[Stmt]) -> &Obj {
    let Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::LetObjStmt(value))) =
        &statements[0]
    else {
        panic!("expected object specimen")
    };
    &value.value
}
fn statements_in<'a>(value: &'a Stmt, output: &mut Vec<&'a Stmt>) {
    output.push(value);
    let mut body = |values: &'a [Stmt]| {
        for child in values {
            statements_in(child, output)
        }
    };
    match value {
        Stmt::By(value) => match value {
            ByStmt::ByCasesStmt(x) => {
                for proof in &x.proofs {
                    body(proof)
                }
            }
            ByStmt::ByContraStmt(x) => body(&x.proof),
            ByStmt::ByEnumerateFiniteSetStmt(x) => body(&x.proof),
            ByStmt::ByForStmt(x) => body(&x.proof),
            ByStmt::ByExtensionStmt(x) => body(&x.proof),
            ByStmt::ByFnExtensionStmt(x) => body(&x.proof),
            ByStmt::ByInducStmt(x) => {
                body(&x.proof);
                if let Some(p) = &x.base_proof {
                    body(p)
                };
                if let Some(p) = &x.step_proof {
                    body(p)
                }
            }
            ByStmt::ByStrongInducStmt(x) => {
                body(&x.proof);
                if let Some(p) = &x.base_proof {
                    body(p)
                };
                if let Some(p) = &x.step_proof {
                    body(p)
                }
            }
            ByStmt::ByDefStmt(_) | ByStmt::ByThmStmt(_) => {}
        },
        Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(x)) => body(&x.proof),
        Stmt::ProofBlock(ProofBlockStmt::SketchStmt(x)) => body(&x.proof),
        Stmt::Definition(DefinitionStmt::DefThmStmt(x)) => body(&x.prove_process),
        Stmt::Definition(DefinitionStmt::DefStrategyStmt(x)) => body(&x.prove_process),
        Stmt::ReleaseAndExpand(ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(x)) => body(&x.proof),
        Stmt::ReleaseAndExpand(ReleaseAndExpandStmt::ReleaseZornLemmaStmt(x)) => body(&x.proof),
        Stmt::Witness(WitnessStmt::WitnessExistFact(x)) => body(&x.proof),
        Stmt::Witness(WitnessStmt::WitnessAtomicFact(x)) => body(&x.proof),
        Stmt::Witness(WitnessStmt::WitnessNonemptySet(x)) => body(&x.proof),
        _ => {}
    }
}
fn helper_kind(value: &Obj) -> &'static str {
    match value {
        Obj::FnObj(value) => match value.head.as_ref() {
            FnObjHead::Identifier(_) => "FnObjHead.Identifier",
            FnObjHead::AnonymousFnLiteral(_) => "FnObjHead.AnonymousFnLiteral",
            FnObjHead::FieldAccess(_) => "FnObjHead.FieldAccess",
            FnObjHead::InstantiatedTemplateObj(_) => "FnObjHead.InstantiatedTemplateObj",
            FnObjHead::Object(_) => "FnObjHead.Object",
        },
        Obj::LimitOperator(LimitOperator::Function(value)) => match value.approach {
            LimitApproach::AtPoint(_) => "LimitApproach.AtPoint",
            LimitApproach::FromLeft(_) => "LimitApproach.FromLeft",
            LimitApproach::FromRight(_) => "LimitApproach.FromRight",
            LimitApproach::AtPositiveInfinity => "LimitApproach.AtPositiveInfinity",
            LimitApproach::AtNegativeInfinity => "LimitApproach.AtNegativeInfinity",
        },
        _ => panic!("not a helper specimen"),
    }
}
fn record(kind: &str, source: &str, latex: &str, pattern: &str, full_source: &str) -> JsonValue {
    let mut row = JsonObject::new();
    for (key, value) in [
        ("kind", kind),
        ("source", source),
        ("latex", latex),
        ("format", pattern),
    ] {
        row.insert(key.into(), JsonValue::String(value.into()));
    }
    let mut rt = runtime(OutputLanguage::Chinese);
    let ast = parse(&mut rt, full_source);
    let full_latex =
        to_latex_from_ast(&ast, &rt.global_module_manager, OutputLanguage::Chinese).unwrap();
    assert!(
        full_latex.contains(latex),
        "isolated fragment not found in full source: {kind}"
    );
    row.insert("full_source".into(), JsonValue::String(full_source.into()));
    row.insert("full_latex".into(), JsonValue::String(full_latex));
    JsonValue::Object(row)
}

#[test]
fn every_ast_type_has_a_designed_and_exercised_format() {
    let catalog = JsonValue::parse(
        &fs::read_to_string(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/compile_to_latex/format_catalog.json"),
        )
        .unwrap(),
    )
    .unwrap();
    let mut rendered = Vec::new();
    for (group, expected) in [
        ("objects", kinds::OBJ_KINDS),
        ("statements", kinds::STMT_KINDS),
    ] {
        let rows = catalog
            .as_object()
            .unwrap()
            .get(group)
            .unwrap()
            .as_array()
            .unwrap();
        let listed = rows
            .iter()
            .map(|row| string(row, "kind"))
            .collect::<BTreeSet<_>>();
        assert_eq!(
            listed,
            expected.iter().copied().collect::<BTreeSet<_>>(),
            "missing or duplicate {group} formats"
        );
        assert_eq!(rows.len(), listed.len(), "duplicate {group} entries");
        for row in rows {
            let kind = string(row, "kind");
            let mut rt = if group == "objects" {
                object_runtime(OutputLanguage::Chinese)
            } else {
                runtime(OutputLanguage::Chinese)
            };
            let full_source = if group == "objects" {
                OBJECT_CONTEXT.to_string() + string(row, "source")
            } else {
                fs::read_to_string(
                    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(string(row, "fixture")),
                )
                .unwrap()
            };
            let (source, ast) = if group == "objects" {
                let source = string(row, "source").to_string();
                let ast = parse(&mut rt, &source);
                assert_eq!(kinds::obj_kind(object_from(&ast)), kind, "{source}");
                (source, ast)
            } else {
                let source = fs::read_to_string(
                    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(string(row, "fixture")),
                )
                .unwrap();
                let ast = parse(&mut rt, &source);
                let mut nested = Vec::new();
                for value in &ast {
                    statements_in(value, &mut nested)
                }
                let target = nested
                    .into_iter()
                    .find(|value| kinds::stmt_kind(value) == kind)
                    .unwrap_or_else(|| panic!("fixture does not exercise {kind}"));
                (target.readable_string(), vec![target.clone()])
            };
            let latex = to_latex_from_ast(&ast, &rt.global_module_manager, OutputLanguage::Chinese)
                .unwrap();
            assert!(
                !latex.contains("$$") && !latex.contains("@a@") && !latex.contains("@b@"),
                "{kind}: {latex}"
            );
            rendered.push(record(
                kind,
                &source,
                &latex,
                string(row, "format"),
                &full_source,
            ));
        }
    }
    let helpers = catalog
        .as_object()
        .unwrap()
        .get("helpers")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(helpers.len(), 10);
    let mut helper_kinds = BTreeSet::new();
    for row in helpers {
        let mut rt = object_runtime(OutputLanguage::Chinese);
        let source = string(row, "source");
        let ast = parse(&mut rt, source);
        assert_eq!(helper_kind(object_from(&ast)), string(row, "kind"));
        assert!(helper_kinds.insert(string(row, "kind")), "duplicate helper");
        let latex =
            to_latex_from_ast(&ast, &rt.global_module_manager, OutputLanguage::Chinese).unwrap();
        rendered.push(record(
            string(row, "kind"),
            source,
            &latex,
            string(row, "format"),
            &(OBJECT_CONTEXT.to_string() + source),
        ));
    }
    let facts = catalog
        .as_object()
        .unwrap()
        .get("facts")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(facts.len(), 10);
    let mut fact_kinds = BTreeSet::new();
    for row in facts {
        let mut rt = runtime(OutputLanguage::Chinese);
        parse(&mut rt, "have a,b,c,d R");
        let source = string(row, "source");
        let ast = parse(&mut rt, source);
        let Stmt::Fact(value) = &ast[0] else {
            panic!("expected fact")
        };
        let kind = kinds::fact_kind(value);
        assert_eq!(kind, string(row, "kind"));
        assert!(fact_kinds.insert(kind));
        let latex =
            to_latex_from_ast(&ast, &rt.global_module_manager, OutputLanguage::Chinese).unwrap();
        rendered.push(record(
            kind,
            source,
            &latex,
            string(row, "format"),
            &("have a,b,c,d R\n".to_string() + source),
        ));
    }
    if let Ok(path) = std::env::var("LITEX_LATEX_CATALOG_OUTPUT") {
        fs::write(path, JsonValue::Array(rendered).stringify_pretty()).unwrap();
    }
}

#[test]
fn dimensions_preimage_scope_and_proof_paragraphs_are_not_lost() {
    let catalog = JsonValue::parse(
        &fs::read_to_string(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/compile_to_latex/format_catalog.json"),
        )
        .unwrap(),
    )
    .unwrap();
    for row in catalog
        .as_object()
        .unwrap()
        .get("objects")
        .unwrap()
        .as_array()
        .unwrap()
    {
        let mut rt = object_runtime(OutputLanguage::English);
        let sample = parse(&mut rt, string(row, "source"));
        let value = object_from(&sample);
        let operation = if let Obj::MatrixOperator(matrix) = value {
            Some((matrix.name(), matrix.operand_refs().len()))
        } else {
            value
                .multivariable_selector_name()
                .map(|name| (name, value.multivariable_selector_args().unwrap().len()))
        };
        let Some((name, arity)) = operation else {
            continue;
        };
        let numbers = (101..101 + arity)
            .map(|n| n.to_string())
            .collect::<Vec<_>>();
        let mut rt = runtime(OutputLanguage::English);
        let ast = parse(
            &mut rt,
            &format!("let specimen = {name}({})", numbers.join(",")),
        );
        let latex =
            to_latex_from_ast(&ast, &rt.global_module_manager, OutputLanguage::English).unwrap();
        for number in numbers {
            assert!(
                latex.contains(&number),
                "lost operand {number} in {name}: {latex}"
            )
        }
    }
    let fibre = to_latex_from_source(
        &(OBJECT_CONTEXT.to_string() + "let result = preimage(f,S)"),
        OutputLanguage::English,
    )
    .unwrap();
    let preimage = to_latex_from_source(
        &(OBJECT_CONTEXT.to_string() + "let result = preimage_set(f,S)"),
        OutputLanguage::English,
    )
    .unwrap();
    assert!(fibre.contains(r"\left\{S\right\}") && !preimage.contains(r"\left\{S\right\}"));
    let proof = to_latex_from_source(
        include_str!("../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit"),
        OutputLanguage::English,
    )
    .unwrap();
    assert!(proof.contains(r"\textbf{Proof by contradiction.}"));
    assert!(proof.contains("$n \\leq 1$;\n\\par\n$n = 1$;"), "{proof}");
    assert!(proof.contains(r"\begin{quote}") && proof.contains(r"\neg\left(n > 1\right)"));
}
