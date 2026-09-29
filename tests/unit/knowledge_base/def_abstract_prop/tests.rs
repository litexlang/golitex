use crate::ast::line_file::SourceLine;
use crate::ast::stmt::DefAbstractPropStmt;
use crate::knowledge_base::{
    load_def_abstract_prop, store_def_abstract_prop, write_def_abstract_prop,
};
use crate::runtime::CodeSource;
use std::fs;
use std::path::{Path, PathBuf};

const FIXTURE: &str = include_str!(
    "../../../../examples/knowledge_base/def_abstract_prop/marked.def_abstract_prop.json"
);

fn sample() -> DefAbstractPropStmt {
    DefAbstractPropStmt {
        name: "marked".to_string(),
        params: vec!["x".to_string()],
        line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
    }
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "examples/knowledge_base/def_abstract_prop/marked.def_abstract_prop.json",
    )
}

#[test]
fn store_load_round_trip() {
    let stmt = sample();
    let text = store_def_abstract_prop(&stmt).expect("store");
    assert_eq!(stmt, load_def_abstract_prop(&text).expect("load"));
}

#[test]
fn load_example_golden() {
    assert_eq!(sample(), load_def_abstract_prop(FIXTURE).expect("load"));
}

#[test]
fn store_matches_golden() {
    let text = store_def_abstract_prop(&sample()).expect("store");
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
    let path = fixture_path();
    write_def_abstract_prop(&path, &sample()).expect("write");
    eprintln!("wrote {}", path.display());
}
