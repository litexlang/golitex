use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::{Obj, StandardSet};
use crate::ast::stmt::{DefStructStmt, StructFieldDef};
use crate::knowledge_base::{load_def_struct, store_def_struct, write_def_struct};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::CodeSource;
use std::path::{Path, PathBuf};

const FIXTURE: &str = include_str!(
    "../../../../../examples/knowledge_base/def_struct/point.def_struct.json"
);

fn sample() -> DefStructStmt {
    DefStructStmt {
        name: "Point".to_string(),
        param_def_with_dom: None,
        fields: vec![
            StructFieldDef {
                binding: BoundName::new(IdentifierId::new(31), "x".to_string()),
                field_type: Obj::StandardSet(StandardSet::R),
            },
            StructFieldDef {
                binding: BoundName::new(IdentifierId::new(32), "y".to_string()),
                field_type: Obj::StandardSet(StandardSet::R),
            },
        ],
        equivalent_facts: Vec::new(),
        line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
    }
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/knowledge_base/def_struct/point.def_struct.json")
}

#[test]
fn store_load_round_trip() {
    let stmt = sample();
    let text = store_def_struct(&stmt).expect("store");
    assert_eq!(stmt, load_def_struct(&text).expect("load"));
}

#[test]
fn load_example_golden() {
    assert_eq!(sample(), load_def_struct(FIXTURE).expect("load"));
}

#[test]
fn store_matches_golden() {
    let text = store_def_struct(&sample()).expect("store");
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
    write_def_struct(&fixture_path(), &sample()).expect("write");
}
