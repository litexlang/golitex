use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{Literal, Number, Obj};
use crate::ast::stmt::DefThmStmt;
use crate::knowledge_base::{load_def_thm, store_def_thm, write_def_thm};
use crate::runtime::runtime_ids::FactId;
use crate::runtime::CodeSource;
use std::path::{Path, PathBuf};

const FIXTURE: &str = include_str!(
    "../../../../../examples/knowledge_base/def_thm/one_is_one.def_thm.json"
);

fn sample() -> DefThmStmt {
    DefThmStmt {
        name: "one_is_one".to_string(),
        fact: Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: FactId::new(10),
            left: Obj::Literal(Literal::Number(Number {
                normalized_value: "1".to_string(),
            })),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: "1".to_string(),
            })),
            line_file: None,
        })),
        prove_process: Vec::new(),
        line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
    }
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/knowledge_base/def_thm/one_is_one.def_thm.json")
}

#[test]
fn store_load_round_trip() {
    let stmt = sample();
    let text = store_def_thm(&stmt).expect("store");
    assert_eq!(stmt, load_def_thm(&text).expect("load"));
}

#[test]
fn load_example_golden() {
    assert_eq!(sample(), load_def_thm(FIXTURE).expect("load"));
}

#[test]
fn store_matches_golden() {
    let text = store_def_thm(&sample()).expect("store");
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
    write_def_thm(&fixture_path(), &sample()).expect("write");
}
