//! Foundation interfaces keep the same predicate identity as their definitions.
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn exported_zorn_interfaces_use_resolved_predicate_names() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let project = std::env::temp_dir().join(format!(
        "litex-qualified-zorn-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir_all(&project).unwrap();
    fs::write(
        project.join("litex.config"),
        "[export]\nfirst=\"./first.lit\"\nsecond=\"./second.lit\"\n",
    )
    .unwrap();
    let source = include_str!("../examples/test_statements/release_zorn_lemma_stmt.lit");
    fs::write(project.join("first.lit"), source).unwrap();
    fs::write(project.join("second.lit"), source).unwrap();
    let result = build_reading(
        &ReadingInput::Project(project.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(
        result.success,
        "both chapters must retain their own relation, bound and maximality definitions: {:?}",
        result.document
    );
    fs::remove_dir_all(project).unwrap();
}

#[test]
fn unresolved_and_unary_zorn_relations_remain_rejected() {
    for source in [
        include_str!("../examples/test_statements/negative/release_zorn_lemma_stmt/undefined-zorn-interfaces.lit"),
        include_str!("../examples/test_statements/negative/release_zorn_lemma_stmt/unary-order-interface.lit"),
    ] {
        let result = build_reading(&ReadingInput::Source(source.to_owned()), true, OutputLanguage::English);
        assert!(!result.success, "resolving names must not relax the Zorn relation interface");
    }
}
