use crate::ast::fact::{AtomicFact, Fact, GreaterFact};
use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::{IdentifierObj, Literal, Number, Obj, StandardSet};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::DefPropStmt;
use crate::knowledge_base::{
    load_def_prop, read_def_prop, store_def_prop, write_def_prop,
};
use crate::runtime::runtime_ids::{FactId, IdentifierId};
use crate::runtime::CodeSource;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

// Golden lives under examples/ (the KB example “repo”), not under tests/.
const IS_POS_FIXTURE: &str =
    include_str!("../../../../examples/knowledge_base/def_prop/is_pos.def_prop.json");

fn sample_is_pos() -> DefPropStmt {
    DefPropStmt {
        name: "is_pos".to_string(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![BoundName::new(IdentifierId::new(7), "x".to_string())],
                param_type: ParamType::Obj(Obj::StandardSet(StandardSet::R)),
            }],
        },
        iff_facts: vec![Fact::AtomicFact(AtomicFact::GreaterFact(GreaterFact {
            fact_id: FactId::new(42),
            left: Obj::Identifier(IdentifierObj::plain(
                IdentifierId::new(7),
                "x".to_string(),
            )),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: "0".to_string(),
            })),
            line_file: None,
        }))],
        line_file: SourceLine::new(
            1,
            CodeSource::RootExport { export_file_id: 0 },
        ),
    }
}

fn example_fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/knowledge_base/def_prop/is_pos.def_prop.json")
}

fn temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("litex_kb_def_prop_{label}_{nanos}"));
    fs::create_dir_all(&dir).expect("mkdir");
    dir
}

#[test]
fn store_load_string_round_trip() {
    let prop = sample_is_pos();
    let text = store_def_prop(&prop).expect("store");
    let back = load_def_prop(&text).expect("load");
    assert_eq!(prop, back);
}

#[test]
fn numeric_decoder_normalizes_old_spelling_and_preserves_hot_cold_identity() {
    let mut prop = sample_is_pos();
    let Fact::AtomicFact(AtomicFact::GreaterFact(fact)) = &mut prop.iff_facts[0] else { panic!("greater"); };
    fact.right = Obj::Literal(Literal::Number(Number { normalized_value: "2.400".into() }));
    let cold = load_def_prop(&store_def_prop(&prop).unwrap()).unwrap();
    let hot = load_def_prop(&store_def_prop(&cold).unwrap()).unwrap();
    assert_eq!(cold, hot);
    let Fact::AtomicFact(AtomicFact::GreaterFact(fact)) = &cold.iff_facts[0] else { panic!("greater"); };
    assert_eq!(fact.right.ir(), Obj::Literal(Literal::Number(Number::new("2.4".into()))).ir());
}

#[test]
fn load_example_golden_matches_sample() {
    let back = load_def_prop(IS_POS_FIXTURE).expect("load example golden");
    assert_eq!(sample_is_pos(), back);
}

#[test]
fn store_matches_example_golden_bytes() {
    let text = store_def_prop(&sample_is_pos()).expect("store");
    let fixture = IS_POS_FIXTURE.trim_end_matches(['\n', '\r']);
    assert_eq!(
        text.trim_end_matches(['\n', '\r']),
        fixture,
        "store_def_prop drifted from examples/.../is_pos.def_prop.json; \
         re-dump with LITEX_DUMP_KB_FIXTURES=1 if intentional"
    );
}

#[test]
fn write_read_temp_file_round_trip() {
    let dir = temp_dir("round_trip");
    let path = dir.join("is_pos.def_prop.json");
    let prop = sample_is_pos();
    write_def_prop(&path, &prop).expect("write");
    assert!(path.is_file(), "expected file at {}", path.display());
    let back = read_def_prop(&path).expect("read");
    assert_eq!(prop, back);
    let _ = fs::remove_dir_all(&dir);
}

/// Regenerates the examples/ golden when requested:
/// `LITEX_DUMP_KB_FIXTURES=1 cargo test --lib …dump_is_pos_fixture -- --exact`
#[test]
fn dump_is_pos_fixture() {
    if std::env::var_os("LITEX_DUMP_KB_FIXTURES").is_none() {
        return;
    }
    let path = example_fixture_path();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("mkdir examples def_prop");
    }
    let text = store_def_prop(&sample_is_pos()).expect("store");
    fs::write(&path, format!("{text}\n")).expect("write example golden");
    eprintln!("wrote {}", path.display());
}
