use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::{
    AnonymousFn, FnSet, IdentifierObj, Literal, Number, Obj, StandardSet,
};
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::ast::stmt::{HaveFnEqualStmt, LetObjStmt};
use crate::exec_env::StoredIdentifierDefinition;
use crate::knowledge_base::{
    load_stored_identifier, store_stored_identifier, write_stored_identifier,
};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::CodeSource;
use std::path::{Path, PathBuf};
use std::rc::Rc;

const LET_A_FIXTURE: &str = include_str!(
    "../../../../../examples/knowledge_base/stored_identifier/let_a.stored_identifier.json"
);
const HAVE_FN_ID_FIXTURE: &str = include_str!(
    "../../../../../examples/knowledge_base/stored_identifier/have_fn_id.stored_identifier.json"
);

fn sample_let_a() -> StoredIdentifierDefinition {
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

fn sample_have_fn_id() -> StoredIdentifierDefinition {
    let x = BoundName::new(IdentifierId::new(15), "x".to_string());
    StoredIdentifierDefinition::HaveFnEqual((
        "id".to_string(),
        Rc::new(HaveFnEqualStmt {
            name: "id".to_string(),
            equal_to_anonymous_fn: AnonymousFn {
                body: FnSet {
                    set_bound_parameters: SetBoundParameterList {
                        groups: vec![SetBoundParameterGroup {
                            params: vec![x],
                            param_type: Box::new(Obj::StandardSet(StandardSet::R)),
                        }],
                    },
                    dom_facts: Vec::new(),
                    ret_set: Box::new(Obj::StandardSet(StandardSet::R)),
                },
                equal_to: Box::new(Obj::Identifier(IdentifierObj::plain(
                    IdentifierId::new(15),
                    "x".to_string(),
                ))),
            },
            line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
        }),
    ))
}

fn let_a_fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "examples/knowledge_base/stored_identifier/let_a.stored_identifier.json",
    )
}

fn have_fn_id_fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "examples/knowledge_base/stored_identifier/have_fn_id.stored_identifier.json",
    )
}

#[test]
fn store_load_round_trip_let_a() {
    let entry = sample_let_a();
    let text = store_stored_identifier(&entry).expect("store");
    assert_eq!(entry, load_stored_identifier(&text).expect("load"));
}

#[test]
fn store_load_round_trip_have_fn_id() {
    let entry = sample_have_fn_id();
    let text = store_stored_identifier(&entry).expect("store");
    assert_eq!(entry, load_stored_identifier(&text).expect("load"));
}

#[test]
fn load_example_golden_let_a() {
    assert_eq!(
        sample_let_a(),
        load_stored_identifier(LET_A_FIXTURE).expect("load")
    );
}

#[test]
fn load_example_golden_have_fn_id() {
    assert_eq!(
        sample_have_fn_id(),
        load_stored_identifier(HAVE_FN_ID_FIXTURE).expect("load")
    );
}

#[test]
fn store_matches_golden_let_a() {
    let text = store_stored_identifier(&sample_let_a()).expect("store");
    assert_eq!(
        text.trim_end_matches(['\n', '\r']),
        LET_A_FIXTURE.trim_end_matches(['\n', '\r'])
    );
}

#[test]
fn store_matches_golden_have_fn_id() {
    let text = store_stored_identifier(&sample_have_fn_id()).expect("store");
    assert_eq!(
        text.trim_end_matches(['\n', '\r']),
        HAVE_FN_ID_FIXTURE.trim_end_matches(['\n', '\r'])
    );
}

#[test]
fn dump_fixture() {
    if std::env::var_os("LITEX_DUMP_KB_FIXTURES").is_none() {
        return;
    }
    write_stored_identifier(&let_a_fixture_path(), &sample_let_a()).expect("write let_a");
    write_stored_identifier(&have_fn_id_fixture_path(), &sample_have_fn_id())
        .expect("write have_fn_id");
}
