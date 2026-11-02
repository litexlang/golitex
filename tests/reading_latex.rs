//! Native compiler/reading/CLI contract for the mathematical reading view.
use litex::knowledge_base::JsonValue;
use litex::launch_command::{parse_launch_command, LaunchCommand, OutputLanguage};
use litex::reading::{
    build_reading, build_reading_with_layout, parse_reading_command, ReadingAction, ReadingInput,
    ReadingLayout,
};
use std::collections::BTreeSet;
use std::process::Command;

const PROOF: &str =
    include_str!("../examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit");

#[test]
fn layout_flag_is_independent_of_reading_action_and_respects_operands() {
    let args = |values: &[&str]| {
        values
            .iter()
            .map(|value| (*value).into())
            .collect::<Vec<String>>()
    };
    for action in [vec![], vec!["-json"], vec!["-export", "out"]] {
        let mut values = vec!["-reading", "-latex", "-strict", "-e", "1=1"];
        values.extend(action);
        let command = parse_reading_command(&args(&values)).unwrap().unwrap();
        assert_eq!(command.layout, ReadingLayout::Latex);
        assert!(command.strict);
    }
    let source = parse_reading_command(&args(&["-reading", "-json", "-e", "-latex"]))
        .unwrap()
        .unwrap();
    assert_eq!(source.layout, ReadingLayout::Source);
    assert_eq!(source.input, ReadingInput::Source("-latex".into()));
    assert_eq!(source.action, ReadingAction::Json);
    assert!(parse_reading_command(&args(&["-reading", "-latex", "--latex"])).is_err());
    assert!(parse_reading_command(&args(&["-reading", "-latex", "-document"])).is_err());
    assert!(parse_reading_command(&args(&["-reading", "-latex", "-json"])).is_err());
    let standalone = parse_launch_command(&args(&["-latex", "-e", "1=2"])).unwrap();
    assert!(matches!(standalone, LaunchCommand::CompileToLatex { .. }));
}

#[test]
fn presentation_preserves_every_native_proof_record_and_all_localized_compiler_bytes() {
    for language in OutputLanguage::ALL {
        let input = ReadingInput::Source(PROOF.into());
        let plain = build_reading(&input, true, language);
        let math = build_reading_with_layout(&input, true, language, ReadingLayout::Latex);
        assert!(plain.success && math.success);
        assert_eq!(
            math.document.field("reading_layout").as_str().unwrap(),
            "latex"
        );
        for key in [
            "statements",
            "facts",
            "inferences",
            "well_definedness",
            "evidence_nodes",
            "scopes",
            "symbols",
            "occurrences",
            "trust_summary",
            "execution_policy",
            "run_result",
            "diagnostics",
        ] {
            assert_eq!(
                plain.document.field(key),
                math.document.field(key),
                "changed {key} in {language:?}"
            );
        }
        let source = &math.document.field("sources").as_array().unwrap()[0];
        let blocks = source.field("latex_blocks").as_array().unwrap();
        let combined = blocks
            .iter()
            .map(|block| block.field("content").as_str().unwrap())
            .collect::<String>();
        let expected = litex::compile_to_latex::to_latex_from_source(PROOF, language).unwrap();
        assert_eq!(combined, expected);
        let statements = math.document.field("statements").as_array().unwrap();
        let mut ids = BTreeSet::new();
        for block in blocks {
            let latex = block.field("content").as_str().unwrap();
            for span in block.field("statements").as_array().unwrap() {
                let id = span.field("statement_id").as_str().unwrap();
                assert!(ids.insert(id));
                let original = statements
                    .iter()
                    .find(|record| record.field("id").as_str().unwrap() == id)
                    .unwrap();
                assert_eq!(original.field("source_id"), source.field("id"));
                let a = span.field("start_byte").as_u64().unwrap() as usize;
                let b = span.field("end_byte").as_u64().unwrap() as usize;
                assert!(a < b && latex.is_char_boundary(a) && latex.is_char_boundary(b));
            }
        }
        assert_eq!(ids.len(), statements.len());
    }
}

#[test]
fn repeated_formulas_keep_distinct_source_boundaries_and_failure_is_not_certification() {
    let duplicate = "claim:\n    ? 1=1\n    1=1\n1=1\n";
    let built = build_reading_with_layout(
        &ReadingInput::Source(duplicate.into()),
        true,
        OutputLanguage::English,
        ReadingLayout::Latex,
    );
    assert!(built.success);
    let blocks = built.document.field("sources").as_array().unwrap()[0]
        .field("latex_blocks")
        .as_array()
        .unwrap();
    assert_eq!(blocks.len(), 2);
    let spans = blocks[0].field("statements").as_array().unwrap();
    assert_eq!(spans.len(), 2);
    let child = &spans[1];
    let text = blocks[0].field("content").as_str().unwrap();
    let start = child.field("start_byte").as_u64().unwrap() as usize;
    let end = child.field("end_byte").as_u64().unwrap() as usize;
    assert_eq!(&text[start..end], "$1 = 1$;");
    assert!(
        start > text.find("$1 = 1$;").unwrap(),
        "a proof-body statement must not bind to the identical claim goal"
    );
    let failed = build_reading_with_layout(
        &ReadingInput::Source("1=1\n1=2\nhave\n3=3\n".into()),
        true,
        OutputLanguage::English,
        ReadingLayout::Latex,
    );
    assert!(!failed.success);
    let statements = failed.document.field("statements").as_array().unwrap();
    assert!(statements
        .iter()
        .any(|statement| statement.field("status").as_str().unwrap() == "rejected"));
    let source = &failed.document.field("sources").as_array().unwrap()[0];
    assert!(source.field("content").as_str().unwrap().contains("3=3"));
    let compiled = source
        .field("latex_blocks")
        .as_array()
        .unwrap()
        .iter()
        .map(|b| b.field("content").as_str().unwrap())
        .collect::<String>();
    assert!(!compiled.contains("3 = 3"));
}

#[test]
fn actual_cli_json_and_static_export_carry_the_shared_mathematical_reader() {
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args([
            "-reading", "-latex", "-json", "-strict", "-lang", "zh", "-e", PROOF,
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let reading = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-latex", "-lang", "zh", "-e", PROOF])
        .output()
        .unwrap();
    assert!(output.status.success());
    let artifact = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
    let compiled = reading.field("sources").as_array().unwrap()[0]
        .field("latex_blocks")
        .as_array()
        .unwrap()
        .iter()
        .map(|b| b.field("content").as_str().unwrap())
        .collect::<String>();
    assert_eq!(compiled, artifact.field("content").as_str().unwrap());
    assert_eq!(artifact.field("verified"), &JsonValue::Bool(false));
    let directory =
        std::env::temp_dir().join(format!("litex-reading-latex-export-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_litex"))
        .args(["-reading", "-latex", "-strict", "-export"])
        .arg(&directory)
        .args(["-e", PROOF])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(std::fs::read_to_string(directory.join("standalone.html"))
        .unwrap()
        .contains("reading_layout"));
    assert!(std::fs::read_to_string(directory.join("reader.js"))
        .unwrap()
        .contains("function compiledLatex"));
    let manifest = JsonValue::parse(
        &std::fs::read_to_string(directory.join("reading.manifest.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(manifest.field("reading_layout").as_str().unwrap(), "latex");
    let source = &manifest.field("sources").as_array().unwrap()[0];
    assert!(
        source.as_object().unwrap().get("latex_blocks").is_none(),
        "native layout is loaded with its source chunk"
    );
    let chunk = JsonValue::parse(
        &std::fs::read_to_string(directory.join(source.field("chunk_url").as_str().unwrap()))
            .unwrap(),
    )
    .unwrap();
    assert!(!chunk.field("sources").as_array().unwrap()[0]
        .field("latex_blocks")
        .as_array()
        .unwrap()
        .is_empty());
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn all_current_statement_fixtures_keep_complete_native_render_correspondence() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = std::fs::read_dir(root.join("examples/test_statements"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|s| s == "lit"))
        .collect::<Vec<_>>();
    files.sort();
    assert_eq!(files.len(), 52);
    let mut covered = BTreeSet::new();
    for file in files {
        let source = std::fs::read_to_string(&file).unwrap();
        let result = build_reading_with_layout(
            &ReadingInput::Source(source.clone()),
            false,
            OutputLanguage::English,
            ReadingLayout::Latex,
        );
        assert!(
            !result
                .document
                .field("diagnostics")
                .as_array()
                .unwrap()
                .iter()
                .any(
                    |diagnostic| diagnostic.field("kind").as_str().unwrap() == "latex_presentation"
                ),
            "{}: {}",
            file.display(),
            result.document.field("diagnostics").stringify()
        );
        let statements = result.document.field("statements").as_array().unwrap();
        let blocks = result.document.field("sources").as_array().unwrap()[0]
            .as_object()
            .unwrap()
            .get("latex_blocks")
            .unwrap()
            .as_array()
            .unwrap();
        let ids = blocks
            .iter()
            .flat_map(|block| block.field("statements").as_array().unwrap())
            .map(|span| span.field("statement_id").as_str().unwrap())
            .collect::<BTreeSet<_>>();
        for statement in statements {
            if statement.field("id") == statement.field("source_statement_id") {
                assert!(
                    ids.contains(statement.field("id").as_str().unwrap()),
                    "{}: unmapped {}",
                    file.display(),
                    statement.stringify()
                );
                covered.insert(
                    statement
                        .field("statement_kind")
                        .as_str()
                        .unwrap()
                        .to_string(),
                );
            }
        }
        if result.success {
            let combined = blocks
                .iter()
                .map(|block| block.field("content").as_str().unwrap())
                .collect::<String>();
            assert_eq!(
                combined,
                litex::compile_to_latex::to_latex_from_source(&source, OutputLanguage::English)
                    .unwrap(),
                "{}",
                file.display()
            );
        }
    }
    assert_eq!(
        covered.len(),
        52,
        "missing observed statement kinds: {covered:?}"
    );
}

#[test]
fn project_and_registered_file_prefixes_preserve_qualified_names_and_source_order() {
    let binary = env!("CARGO_BIN_EXE_litex");
    for (mode, path, count) in [
        ("-r", "tests/fixtures/reading_latex_project", 2),
        ("-f", "tests/fixtures/reading_latex_project/alpha.lit", 1),
        ("-f", "tests/fixtures/reading_latex_project/beta.lit", 2),
    ] {
        let output = Command::new(binary)
            .args(["-reading", "-latex", "-json", "-strict", mode, path])
            .output()
            .unwrap();
        let baseline = Command::new(binary)
            .args(["-reading", "-json", "-strict", mode, path])
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            baseline.status.code(),
            "presentation changed the native verdict for {path}"
        );
        let reading = JsonValue::parse(std::str::from_utf8(&output.stdout).unwrap()).unwrap();
        let sources = reading.field("sources").as_array().unwrap();
        assert_eq!(sources.len(), count);
        assert!(sources[0]
            .field("path")
            .as_str()
            .unwrap()
            .ends_with("alpha.lit"));
        if count == 2 {
            let compiled = sources[1].field("latex_blocks").as_array().unwrap()[0]
                .field("content")
                .as_str()
                .unwrap();
            assert!(compiled.contains("alpha::twice"), "{compiled}");
        }
    }
}

trait Fields {
    fn field(&self, key: &str) -> &JsonValue;
}
impl Fields for JsonValue {
    fn field(&self, key: &str) -> &JsonValue {
        self.as_object()
            .unwrap()
            .get(key)
            .unwrap_or_else(|| panic!("missing {key}"))
    }
}
