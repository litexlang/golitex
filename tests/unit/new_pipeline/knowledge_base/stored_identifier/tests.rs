use crate::new_pipeline::ast::line_file::SourceLine;
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::knowledge_base::{
    load_stored_identifier, store_stored_identifier, write_stored_identifier,
};
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::CodeSource;
use std::path::{Path, PathBuf};
use std::rc::Rc;

const FIXTURE: &str = include_str!(
    "../../../../../examples/new_pipeline/knowledge_base/stored_identifier/let_a.stored_identifier.json"
);

fn sample() -> StoredIdentifierDefinition {
    StoredIdentifierDefinition::LetObj((
        "a".to_string(),
        Rc::new(LetObjStmt {
            name: BoundName::new(IdentifierId::new(3), "a".to_string()),
            value: Obj::Literal(Literal::Number(Number {
                normalized_value: "1".to_string(),
            })),
            line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
        }),
    ))
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "examples/new_pipeline/knowledge_base/stored_identifier/let_a.stored_identifier.json",
    )
}

#[test]
fn store_load_round_trip() {
    let entry = sample();
    let text = store_stored_identifier(&entry).expect("store");
    assert_eq!(entry, load_stored_identifier(&text).expect("load"));
}

#[test]
fn load_example_golden() {
    assert_eq!(sample(), load_stored_identifier(FIXTURE).expect("load"));
}

#[test]
fn store_matches_golden() {
    let text = store_stored_identifier(&sample()).expect("store");
    assert_eq!(
        text.trim_end_matches(['\n', '\r']),
        FIXTURE.trim_end_matches(['\n', '\r'])
    );
}

#[test]
fn dump_fixture() {
    if std::env::var_os("LITEX_DUMP_KB_FIXTURES").is_none() {
        return;
    }
    write_stored_identifier(&fixture_path(), &sample()).expect("write");
}
