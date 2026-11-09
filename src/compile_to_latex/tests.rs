use super::*;

#[test]
fn negative_atomic_relations_keep_the_entire_relation_inside_negation() {
    let latex =
        to_latex_from_source("have a,b R\nnot a < b\nnot a <= b", OutputLanguage::English).unwrap();
    assert!(latex.contains(r"\neg\left(a < b\right)"));
    assert!(latex.contains(r"\neg\left(a \leq b\right)"));
    assert!(!latex.contains(r"\neg a"));
}

#[test]
fn annotated_statements_keep_exact_latex_and_distinguish_identical_nested_facts() {
    let source = "claim:\n    ? 1 = 1\n    1 = 1\n1 = 1\n";
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: source.into(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let blocks = Tokenizer::new()
        .tokenize(source, runtime.current_file.clone())
        .unwrap();
    let ast = runtime.parse(&blocks).unwrap();
    for language in OutputLanguage::ALL {
        let mut index = 0;
        let mapped = to_latex_with_statement_ids(
            &ast,
            &runtime.global_module_manager,
            language,
            &mut |_| {
                let id = format!("node{index}");
                index += 1;
                Some(id)
            },
        )
        .unwrap();
        let ordinary = to_latex_from_ast(&ast, &runtime.global_module_manager, language).unwrap();
        assert_eq!(mapped.content, ordinary);
        assert_eq!(mapped.statements.len(), 3);
        let root = mapped
            .statements
            .iter()
            .find(|span| span.statement_id == "node0")
            .unwrap();
        let inner = mapped
            .statements
            .iter()
            .find(|span| span.statement_id == "node1")
            .unwrap();
        let repeated = mapped
            .statements
            .iter()
            .find(|span| span.statement_id == "node2")
            .unwrap();
        assert!(root.start_byte < inner.start_byte && inner.end_byte < root.end_byte);
        assert!(repeated.start_byte > root.end_byte);
        let proof_fact =
            super::language::sentence(language, super::language::Phrase::WeHave, "$1 = 1$", "", "");
        assert_eq!(&ordinary[inner.start_byte..inner.end_byte], proof_fact);
        assert_eq!(
            &ordinary[repeated.start_byte..repeated.end_byte],
            "$1 = 1$;"
        );
        assert!(
            inner.start_byte > ordinary.find("$1 = 1$;").unwrap(),
            "the claim goal is not the body statement"
        );
    }
}
use crate::knowledge_base::{store_definition_memory, JsonValue};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;
use std::fs;
use std::path::Path;

const IDENTITY: &str =
    "thm identity:\n    ? forall x R:\n        x = x\nby thm identity(2) => 2 = 2\n";

#[test]
fn display_formulas_preserve_guards_conjunctions_and_grouping_without_execution() {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    });
    let source = "forall x R:\n    x = 2\n    =>:\n        x + 1 = 3\nforall x R:\n    x = x\n    x^2 >= 0\n(1 + 2) * 3 = 9\nnot forall x R:\n    x = 0\n";
    let blocks = Tokenizer::new()
        .tokenize(source, runtime.current_file.clone())
        .unwrap();
    let statements = runtime.parse(&blocks).unwrap();
    let render = |index: usize| {
        let crate::ast::stmt::Stmt::Fact(value) = &statements[index] else {
            panic!("expected a fact");
        };
        super::math_display::fact_to_display_latex(
            value,
            &runtime.global_module_manager,
            OutputLanguage::English,
        )
        .unwrap()
    };
    let guarded = render(0);
    assert!(
        guarded.contains(r"\forall") && guarded.contains(r"x = 2 \Rightarrow x + 1 = 3"),
        "{guarded}"
    );
    let conjunction = render(1);
    assert!(
        conjunction.contains(r"\forall")
            && conjunction.contains(r"\land")
            && conjunction.contains(r"x^{2} \geq 0"),
        "{conjunction}"
    );
    let comparison = render(2);
    assert!(
        comparison.contains(r"\left(1 + 2\right) \cdot 3") && comparison.contains(r"\\&=\ 9"),
        "{comparison}"
    );
    let negated = render(3);
    assert!(negated.contains(r"\neg\left(\forall"), "{negated}");
    let environment = &runtime.execution_environments_stack[0];
    assert!(
        environment.facts.facts_by_id.is_empty()
            && environment.well_defined_objects.object_to_wd_id.is_empty()
    );
}

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
        assert!(text.contains(r"\mathit{identity}(2)"), "{text}");
        assert!(text.contains("$2 = 2$"), "{text}");
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
    assert!(text.contains("Evaluate $1 + 1$."));
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
        text.contains(r"\forall z\in \mathbb{R}:\ z = 0 \Longleftrightarrow"),
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
            assert!(
                !text.contains("$$"),
                "{} / {lang:?}: {text}",
                path.display()
            );
        }
    }
    assert_eq!(
        count, 52,
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
fn selected_command_errors_keep_latex_artifact_metadata() {
    for (args, success) in [
        (vec!["-latex", "-lang", "zh", "-e", "1 = 2"], true),
        (vec!["-latex", "-lang", "fr", "-e", "have"], false),
        (vec!["-latex", "-f", "missing.lit"], false),
    ] {
        let args = args.into_iter().map(str::to_string).collect::<Vec<_>>();
        let command = crate::launch_command::parse_launch_command(&args).unwrap();
        let json = match crate::run::run_command(command.clone()) {
            Ok(outcome) => {
                assert!(!outcome.process_failed());
                outcome.normal_json().unwrap().to_string()
            }
            Err(error) => crate::json_output::emit_command_error(&command, &error).unwrap(),
        };
        let value = JsonValue::parse(&json).unwrap();
        let map = value.as_object().unwrap();
        assert_eq!(
            map.get("artifact_result").unwrap().as_str().ok(),
            Some(if success { "success" } else { "failure" })
        );
        assert_eq!(map.get("verified"), Some(&JsonValue::Bool(false)));
        if !success {
            assert_eq!(map.get("content"), Some(&JsonValue::Null));
        }
    }
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
        assert!(!text.contains(r"\begin{quote}"));
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

#[test]
fn single_conclusions_and_calls_omit_redundant_parentheses() {
    let text = to_latex_from_source(
        "have fn distance_from_zero(x R) R = |x|\nforall x R:\n    distance_from_zero(x) = |x| >= 0\nprop a():\n    0 = 0\nexist! k N st {k = 0}\nnot $a()",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(
        text.contains(r"we have $\mathit{distance\_from\_zero}(x) = \left|x\right| \geq 0$"),
        "{text}"
    );
    assert!(!text.contains(r"we have $\left("), "{text}");
    assert!(!text.contains(r"we have \("), "{text}");
    assert!(text.contains(r"a \Longleftrightarrow"), "{text}");
    assert!(!text.contains("For every $$"), "{text}");
    assert!(text.contains(r"\exists! k\in \mathbb{N}:\ k = 0"), "{text}");
    assert!(text.contains(r"\neg a"), "{text}");
    assert!(!text.contains(r"a\left("), "{text}");
}

#[test]
fn proofs_keep_inline_case_labels_and_one_continuous_proof_paragraph() {
    let source =
        include_str!("../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit");
    for language in OutputLanguage::ALL {
        let text = to_latex_from_source(source, language).unwrap();
        let case = super::language::phrase(language, super::language::Phrase::Case);
        let proof = super::language::phrase(language, super::language::Phrase::Proof);
        assert!(!text.contains(r"\begin{description}"), "{text}");
        for index in [1, 2] {
            assert!(
                text.contains(&format!(r"\textbf{{{case} {index}.}}")),
                "{text}"
            );
        }
        assert_eq!(
            text.matches(&format!(r"\textbf{{{proof}.}}")).count(),
            1,
            "{text}"
        );
        assert!(!text.contains(r"\begin{quote}"), "{text}");
        assert!(text.contains(r"\neg\left(n > 1\right)"), "{text}");
        let then = super::language::sentence(
            language,
            super::language::Phrase::Then,
            r"$n \leq 1$",
            "",
            "",
        );
        let also =
            super::language::sentence(language, super::language::Phrase::Also, "$n = 1$", "", "");
        assert!(text.contains(&format!("{then}\n {also}")), "{text}");
        let start = text.find(&format!(r"\textbf{{{proof}.}}")).unwrap();
        let end = text.find(r"\square").unwrap();
        let body = &text[start..end];
        for forbidden in [r"\par", r"\item", r"\[", r"\hfill"] {
            assert!(!body.contains(forbidden), "{language:?}: {body}");
        }
        assert_eq!(text.matches(r"\square").count(), 1, "{text}");
        assert!(text.contains(r"n\in \mathbb{N}_{>0}"), "{text}");
    }
}

#[test]
fn proof_prose_connects_assumptions_steps_and_structural_conclusions() {
    let source =
        include_str!("../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit");
    let chinese = to_latex_from_source(source, OutputLanguage::Chinese).unwrap();
    for prose in [
        r"可得 $n \geq 1$。",
        r"假设 $n = 1$， 则 $n = 1 \lor n > 1$。",
        r"假设 $n \ne 1$。",
        r"则 $n \leq 1$。",
        r"又有 $n = 1$。",
        r"这与 $n \ne 1$ 矛盾，因此 $n > 1$。",
        r"综上，$n = 1 \lor n > 1$。",
    ] {
        assert!(chinese.contains(prose), "missing {prose}: {chinese}");
    }
    let english = to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(english.contains(r"Suppose $n = 1$. Then $n = 1 \lor n > 1$."));
    assert!(english.contains(r"This contradicts $n \ne 1$, so $n > 1$."));
    assert!(english.contains(r"In all cases, $n = 1 \lor n > 1$."));
    // Prose transitions belong to proof steps, never to a top-level assertion.
    assert_eq!(
        to_latex_from_source("1 = 1", OutputLanguage::Chinese).unwrap(),
        "$1 = 1$;\n"
    );
    for language in OutputLanguage::ALL {
        let text = to_latex_from_source(source, language).unwrap();
        assert!(!text.contains("@a@") && !text.contains("@b@"));
        let closing = super::language::sentence(
            language,
            super::language::Phrase::CasesConclusion,
            r"$n = 1 \lor n > 1$",
            "",
            "",
        );
        assert!(text.contains(&closing), "{text}");
    }
}

#[test]
fn mixed_calculation_rows_preserve_each_original_adjacent_comparison() {
    let text = to_latex_from_source("1 < 4 > 3 < 5 <= 6", OutputLanguage::English).unwrap();
    for row in ["1 &< 4", "4 &> 3", "3 &< 5", r"5 &\leq 6"] {
        assert!(text.contains(row), "{text}");
    }
    assert!(!text.contains("1 &> 3"), "{text}");
    let equality =
        to_latex_from_source("1 + 1 = 2 = 4 / 2 = 6 / 3", OutputLanguage::English).unwrap();
    assert!(equality.contains(r"\begin{aligned}"), "{equality}");
    assert!(
        equality.contains(r"1 + 1 &= 2")
            && equality.contains(r"&= \frac{4}{2}")
            && equality.contains(r"&= \frac{6}{3}"),
        "{equality}"
    );
}

#[test]
fn multiclause_statements_and_definitions_retain_every_clause_and_domain() {
    let source = "prop in_unit_interval(x R):\n    x >= 0\n    x <= 1\nforall x R:\n    x >= 0\n    x <= 1\n    =>:\n        x^2 >= 0\n        x^2 <= 1\nexist x R st {x >= 0, x <= 1}";
    let text = to_latex_from_source(source, OutputLanguage::English).unwrap();
    for clause in [
        r"\forall x\in \mathbb{R}",
        r"\exists x\in \mathbb{R}",
        r"x \geq 0",
        r"x \leq 1",
        r"x^{2} \geq 0",
        r"x^{2} \leq 1",
        r"\Longleftrightarrow",
        r"\Longrightarrow",
        r"\land",
    ] {
        assert!(text.contains(clause), "{text}");
    }
    assert!(
        text.contains(r"\begin{gathered}") && text.contains(r"\begin{aligned}"),
        "{text}"
    );
}

#[test]
fn induction_phases_have_inline_labels_without_forced_breaks() {
    let source =
        include_str!("../../examples/stmt_nodes/by/induction_domain_and_proof_actions.lit");
    let text = to_latex_from_source(source, OutputLanguage::English).unwrap();
    assert!(
        text.contains(r"\textbf{Base case.}") && text.contains(r"\textbf{Induction step.}"),
        "{text}"
    );
    assert!(!text.contains(r"\begin{quote}"), "{text}");
    let start = text.find(r"We aim to show $\mathit{same}(m)$").unwrap();
    let remainder = &text[start..];
    let proof = &remainder[..remainder.find(r"\par").unwrap()];
    assert!(
        !proof.contains(r"\item") && !proof.contains(r"\["),
        "{proof}"
    );
    assert!(proof.contains(r"\textbf{Base case.}") && proof.contains(r"\textbf{Induction step.}"));
}

#[test]
fn nested_proof_definitions_calculations_and_quantifiers_stay_inline() {
    // Parse-only typography control; these facts are not a verification claim.
    let source = "sketch:\n    let a = 1\n    1 < 4 > 3 < 5 <= 6\n    forall x R:\n        x >= 0\n        x <= 1\n        =>:\n            x^2 >= 0\n            x^2 <= 1\n    claim:\n        ? 1 = 1\n        1 = 1\n";
    let text = to_latex_from_source(source, OutputLanguage::English).unwrap();
    for forbidden in [r"\par", r"\begin{quote}", r"\begin{description}", r"\["] {
        assert!(!text.contains(forbidden), "{text}");
    }
    for retained in [
        r"a = 1",
        "1 < 4 > 3 < 5 ",
        r"\leq 6",
        r"\forall x\in \mathbb{R}",
        r"x \geq 0",
        r"x \leq 1",
        r"x^{2} \geq 0",
        r"x^{2} \leq 1",
        r"\Rightarrow",
        r"\land",
        r"\textbf{Claim.}",
        r"\square",
    ] {
        assert!(text.contains(retained), "missing {retained}: {text}");
    }
}

#[test]
fn bodyless_theorems_do_not_acquire_a_fabricated_proof_or_end_marker() {
    let text = to_latex_from_source(
        "thm reflexivity:\n    ? forall x R:\n        x = x",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(
        !text.contains(r"\textbf{Proof.}") && !text.contains(r"\square"),
        "{text}"
    );
}

#[test]
fn superscript_bases_are_parenthesized_before_another_superscript() {
    let latex = to_latex_from_source(
        "exp(1)^2=exp(1)^2\nhave X set = matrix(seq(R),2,2)",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(
        latex.contains(r"\left(\mathrm{e}^{1}\right)^{2}"),
        "{latex}"
    );
    assert!(!latex.contains(r"\mathrm{e}^{1}^{2}"), "{latex}");
    assert!(latex.contains(r"\right)^{2\times 2}"), "{latex}");
}

#[test]
fn direct_import_aliases_take_precedence_over_dependency_aliases() {
    let root = std::env::temp_dir().join(format!(
        "litex-latex-alias-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    for dir in ["", "a", "b"] {
        std::fs::create_dir_all(root.join(dir)).unwrap();
    }
    for (path, body) in [
        (
            "litex.config",
            "[import]\nA=\"./a\"\nRootB=\"./b\"\n[export]\nmain=\"./main.lit\"\n",
        ),
        ("main.lit", "RootB::main::v = RootB::main::v\n"),
        (
            "a/litex.config",
            "[import]\nInternalB=\"../b\"\n[export]\nmain=\"./main.lit\"\n",
        ),
        ("a/main.lit", "have a R = 0\n"),
        ("b/litex.config", "[export]\nmain=\"./main.lit\"\n"),
        ("b/main.lit", "have v R = 0\n"),
    ] {
        std::fs::write(root.join(path), body).unwrap();
    }
    let result = to_latex_from_repository(root.to_str().unwrap(), OutputLanguage::English);
    std::fs::remove_dir_all(&root).unwrap();
    let text = result.unwrap();
    assert!(text.contains("RootB"), "{text}");
    assert!(!text.contains("InternalB"), "{text}");
}
