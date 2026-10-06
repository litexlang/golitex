use super::*;
use crate::knowledge_base::{store_definition_memory, JsonValue};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;
use std::fs;
use std::path::Path;

const IDENTITY: &str =
    "thm identity:\n    ? forall x R:\n        x = x\nby thm identity(2) => 2 = 2\n";

#[test]
fn identity_has_ten_localized_latex_renderings() {
    let titles = [
        "Theorem",
        "定理",
        "定理",
        "Théorème",
        "Теорема",
        "Teorema",
        "نظرية",
        "定理",
        "정리",
        "Định lý",
    ];
    for (lang, title) in OutputLanguage::ALL.into_iter().zip(titles) {
        let text = to_latex_from_source(IDENTITY, lang).unwrap();
        assert!(
            text.contains(&format!("\\textbf{{{title} identity.}}")),
            "{lang:?}: {text}"
        );
        assert!(text.contains(r"x\in \mathbb{R}"), "{text}");
        assert!(text.contains(r"\mathit{identity}\left(2\right)"), "{text}");
        assert!(text.contains(r"\(2 = 2\)"), "{text}");
        assert!(!text.contains("@a@") && !text.contains("#1#"));
        if lang != OutputLanguage::English {
            assert!(
                !text.contains("For every") && !text.contains("By Theorem"),
                "{text}"
            );
        }
        let doc = to_latex_document(&text, lang);
        assert!(doc.contains(r"\begin{document}"));
    }
}

#[test]
fn conversion_does_not_publish_definitions_facts_or_evaluation() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    let before = store_definition_memory(&rt.execution_environments_stack[0].definitions).unwrap();
    let text = to_latex("have a R = 7\n1 = 2\neval 1 + 1", &mut rt).unwrap();
    assert!(text.contains("1 = 2"));
    assert!(text.contains(r"Evaluate \(1 + 1\)."));
    assert!(!text.contains("1 + 1 = 2"));
    let env = &rt.execution_environments_stack[0];
    assert_eq!(before, store_definition_memory(&env.definitions).unwrap());
    assert!(env.facts.facts_by_id.is_empty());
    assert!(env.well_defined_objects.object_to_wd_id.is_empty());
    assert!(to_latex_from_source("1 = 1\nhave", OutputLanguage::English).is_err());
}

#[test]
fn math_grouping_quantifier_scope_and_kinds_are_preserved() {
    let text=to_latex_from_source("(1 + 2) * 3 = 9\n1 - (2 - 3) = 2\n(2^3)^4 = 4096\nforall S set, x S:\n    x $in S\nforall z R:\n    =>:\n        z = 0\n    <=>:\n        z^2 = 0\nexist! k N st {k = 0}\nnot forall t R:\n    t > 0",OutputLanguage::English).unwrap();
    assert!(text.contains(r"\left(1 + 2\right) \cdot 3"), "{text}");
    assert!(text.contains(r"1 - \left(2 - 3\right)"), "{text}");
    assert!(text.contains(r"\left(2^{3}\right)^{4}"), "{text}");
    assert!(text.contains(r"S:\text{set};\ x\in S"), "{text}");
    assert!(!text.contains(r"S\in \text{set}"));
    assert!(
        text.contains(
            r"\forall z\in \mathbb{R}:\ \left(\left(z = 0\right)\right)\Longleftrightarrow"
        ),
        "{text}"
    );
    assert!(text.contains(r"\exists!"));
    assert!(text.contains(r"\neg\left(\forall"));
}

#[test]
fn every_current_statement_fixture_renders_in_every_language() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/test_statements");
    let mut count = 0;
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|x| x != "lit") {
            continue;
        }
        let source = fs::read_to_string(&path).unwrap();
        count += 1;
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        });
        let blocks = Tokenizer::new()
            .tokenize(&source, rt.current_file.clone())
            .unwrap();
        let stmts = rt
            .parse(&blocks)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        for lang in OutputLanguage::ALL {
            let text = to_latex_from_ast(&stmts, &rt.global_module_manager, lang)
                .unwrap_or_else(|error| panic!("{} / {lang:?}: {error}", path.display()));
            assert!(!text.trim().is_empty(), "{}", path.display());
            assert!(!text.contains("@a@"), "{}", path.display());
        }
    }
    assert_eq!(
        count, 50,
        "update the statement inventory when the parser surface changes"
    );
}

#[test]
fn object_examples_render_without_source_text_fallback() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/test_objs");
    let mut count = 0;
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|x| x != "lit") {
            continue;
        }
        let source = fs::read_to_string(&path).unwrap();
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
            language: OutputLanguage::English,
        });
        let blocks = Tokenizer::new()
            .tokenize(&source, rt.current_file.clone())
            .unwrap();
        let stmts = rt
            .parse(&blocks)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        let text = to_latex_from_ast(&stmts, &rt.global_module_manager, OutputLanguage::English)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert!(!text.contains("#1#"), "{}", path.display());
        count += 1;
    }
    assert!(count >= 40, "object corpus unexpectedly shrank: {count}");
}

#[test]
fn artifact_errors_and_argument_boundaries_are_explicit() {
    for (args, success) in [
        (vec!["-latex", "-lang", "zh", "-e", "1 = 2"], true),
        (vec!["-latex", "-lang", "fr", "-e", "have"], false),
        (vec!["-latex", "-e", "1 = 1", "-strict"], false),
        (vec!["-latex", "-e", "1 = 1", "-session"], false),
        (vec!["-latex", "-latex", "-e", "1 = 1"], false),
        (vec!["-latex", "-f", "missing.lit"], false),
    ] {
        let (json, ok) =
            run_latex_args(&args.into_iter().map(str::to_string).collect::<Vec<_>>()).unwrap();
        assert_eq!(ok, success, "{json}");
        let value = JsonValue::parse(&json).unwrap();
        let map = value.as_object().unwrap();
        assert_eq!(map.get("success"), Some(&JsonValue::Bool(success)));
        assert_eq!(map.get("verified"), Some(&JsonValue::Bool(false)));
        if !success {
            assert_eq!(map.get("content"), Some(&JsonValue::Null));
        }
    }
    assert!(run_latex_args(&["-e".into(), "-latex".into()]).is_none());
    assert!(run_latex_args(&["-f".into(), "-latex".into()]).is_none());
}

#[test]
fn localized_trust_axioms_and_nested_proofs_are_retained() {
    for lang in OutputLanguage::ALL {
        let text=to_latex_from_source("trust:\n    1 = 2\naxiom background:\n    ? forall x R:\n        x = x\nclaim:\n    ? 1 = 1\n    sketch:\n        1 = 1",lang).unwrap();
        assert!(text.contains("trust"));
        assert!(text.contains(super::language::phrase(
            lang,
            super::language::Phrase::Axiom
        )));
        assert!(text.contains(super::language::phrase(
            lang,
            super::language::Phrase::Sketch
        )));
        assert!(text.contains(r"\begin{quote}"));
    }
}

#[test]
fn escape_text_does_not_inject_latex_commands() {
    assert_eq!(
        super::helper::escape_text("a_%#&${}\\^~"),
        r"a\_\%\#\&\$\{\}\textbackslash{}\textasciicircum{}\textasciitilde{}"
    );
    assert_eq!(super::helper::ident("foo_bar"), r"\mathit{foo\_bar}");
}

#[test]
fn template_control_words_are_separated_from_argument_names() {
    let source = "template<S set>:\n    have member set = S\nhave T set\n\\member<T> = T";
    let text = to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(text.contains(r"\langle T\rangle"), "{text}");
    assert!(!text.contains(r"\langleT"));
}

#[test]
fn builtin_relations_keep_readable_mathematical_chains() {
    let text = to_latex_from_source("1 < 2 <= 3\n1 = 2 = 3", OutputLanguage::English).unwrap();
    assert!(text.contains(r"1 < 2 \leq 3"), "{text}");
    assert!(text.contains("1 = 2 = 3"), "{text}");
    assert!(!text.contains(r"\land"));
}

#[test]
fn empty_forall_binders_do_not_create_empty_quantification() {
    let text = to_latex_from_source("forall:\n    1 = 1", OutputLanguage::Chinese).unwrap();
    assert!(text.contains("1 = 1"));
    assert!(!text.contains("对任意") && !text.contains(r"\forall"));
}
