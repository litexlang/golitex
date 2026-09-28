use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, ForallFact,
};
use crate::new_pipeline::ast::line_file::SourceLine;
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj, StandardSet};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::ast::stmt::AxiomStmt;
use crate::new_pipeline::knowledge_base::{load_axiom, store_axiom, write_axiom};
use crate::new_pipeline::runtime::runtime_ids::{FactId, IdentifierId};
use crate::new_pipeline::runtime::CodeSource;
use std::path::{Path, PathBuf};

const FIXTURE: &str =
    include_str!("../../../../../examples/new_pipeline/knowledge_base/axiom/eq_refl.axiom.json");

fn sample() -> AxiomStmt {
    let x = BoundName::new(IdentifierId::new(11), "x".to_string());
    let x_obj = Obj::Identifier(IdentifierObj::plain(
        IdentifierId::new(11),
        "x".to_string(),
    ));
    AxiomStmt {
        name: "eq_refl".to_string(),
        forall_fact: ForallFact {
            fact_id: FactId::new(20),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![x],
                    param_type: ParamType::Obj(Obj::StandardSet(StandardSet::R)),
                }],
            },
            dom_facts: Vec::new(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(
                AtomicFact::EqualFact(EqualFact {
                    fact_id: FactId::new(21),
                    left: x_obj.clone(),
                    right: x_obj,
                    line_file: None,
                }),
            )],
            line_file: None,
        },
        line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
    }
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/new_pipeline/knowledge_base/axiom/eq_refl.axiom.json")
}

#[test]
fn store_load_round_trip() {
    let stmt = sample();
    let text = store_axiom(&stmt).expect("store");
    assert_eq!(stmt, load_axiom(&text).expect("load"));
}

#[test]
fn load_example_golden() {
    assert_eq!(sample(), load_axiom(FIXTURE).expect("load"));
}

#[test]
fn store_matches_golden() {
    let text = store_axiom(&sample()).expect("store");
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
    write_axiom(&fixture_path(), &sample()).expect("write");
}
