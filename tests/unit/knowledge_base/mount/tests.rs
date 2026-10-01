//! Unit tests for mount / fingerprint / definition_memory.

use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::{IdentifierObj, Literal, Number, Obj, StandardSet};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::DefPropStmt;
use crate::exec_env::exec_env::DefinitionMemory;
use crate::knowledge_base::{
    compute_fingerprint, store_definition_memory, try_mount_module, write_module_kb, ExportKbWrite,
    FingerprintInputs, GlobalIdsSnapshot, KbMountMiss,
};
use crate::runtime::runtime_ids::{FactId, IdentifierId};
use crate::runtime::CodeSource;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_module_root() -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("litex_kb_mount_{nanos}"));
    fs::create_dir_all(&dir).expect("mkdir");
    dir
}

fn sample_prop(id: u64, fact_id: u64) -> DefPropStmt {
    DefPropStmt {
        name: "is_pos".to_string(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![BoundName::new(IdentifierId::new(id), "x".to_string())],
                param_type: ParamType::Obj(Obj::StandardSet(StandardSet::R)),
            }],
        },
        iff_facts: vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: FactId::new(fact_id),
            left: Obj::Identifier(IdentifierObj::plain(IdentifierId::new(id), "x".to_string())),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: "0".to_string(),
            })),
            line_file: None,
        }))],
        line_file: SourceLine::new(1, CodeSource::RootExport { export_file_id: 0 }),
    }
}

fn sample_defs(id: u64, fact_id: u64) -> DefinitionMemory {
    let mut defs = DefinitionMemory::new();
    let prop = sample_prop(id, fact_id);
    defs.predicate_definitions.insert(prop.name.clone(), prop);
    defs
}

#[test]
fn fingerprint_changes_when_export_bytes_change() {
    let a = compute_fingerprint(&FingerprintInputs {
        litex_config_bytes: b"[export]\nmain = \"a.lit\"\n",
        export_files: &[("a.lit".into(), b"prop p(x R): x > 0\n".to_vec())],
        dep_fingerprints: &[],
    });
    let b = compute_fingerprint(&FingerprintInputs {
        litex_config_bytes: b"[export]\nmain = \"a.lit\"\n",
        export_files: &[("a.lit".into(), b"prop p(x R): x > 1\n".to_vec())],
        dep_fingerprints: &[],
    });
    assert_ne!(a, b);
    assert_eq!(a.len(), 16);
}

#[test]
fn write_then_mount_remaps_identifier_and_fact_ids() {
    let root = temp_module_root();
    let fp = compute_fingerprint(&FingerprintInputs {
        litex_config_bytes: b"config",
        export_files: &[("main.lit".into(), b"prop".to_vec())],
        dep_fingerprints: &[],
    });

    let enter = GlobalIdsSnapshot::new(10, 1, 1, 7);
    let leave = GlobalIdsSnapshot::new(43, 1, 1, 8);
    let defs = sample_defs(7, 42);

    let mut mod_paths = BTreeMap::new();
    mod_paths.insert(2, root.to_string_lossy().to_string());

    write_module_kb(
        &root,
        &fp,
        2,
        &mod_paths,
        &[ExportKbWrite {
            export_file_id: 0,
            name: "main".into(),
            relative_path: "main.lit".into(),
            definitions: defs,
            global_ids_at_enter: enter.clone(),
            global_ids_at_leave: leave.clone(),
        }],
    )
    .expect("write");

    // Live session counters are ahead of cached enter (fact 100, id 20).
    let now = GlobalIdsSnapshot::new(100, 1, 1, 20);
    let mut path_to_new = HashMap::new();
    path_to_new.insert(root.to_string_lossy().to_string(), 5);

    let mounted = try_mount_module(&root, &fp, &now, &path_to_new).expect("mount");
    assert_eq!(mounted.exports.len(), 1);
    let prop = mounted.exports[0]
        .definitions
        .predicate_definitions
        .get("is_pos")
        .expect("prop");
    // identifier_delta = 20 - 7 = 13 → id 7 → 20
    assert_eq!(prop.typed_parameters.groups[0].params[0].id.value(), 20);
    // fact_delta = 100 - 10 = 90 → fact 42 → 132
    match &prop.iff_facts[0] {
        Fact::AtomicFact(AtomicFact::EqualFact(eq)) => {
            assert_eq!(eq.fact_id.value(), 132);
            match &eq.left {
                Obj::Identifier(IdentifierObj::Plain { id, .. }) => {
                    assert_eq!(id.value(), 20);
                }
                other => panic!("expected plain id, got {other:?}"),
            }
        }
        other => panic!("expected equal fact, got {other:?}"),
    }
    // remapped leave: fact 43+90=133, id 8+13=21
    assert_eq!(mounted.remapped_global_ids_leave.next_fact_id, 133);
    assert_eq!(mounted.remapped_global_ids_leave.next_identifier_id, 21);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn mount_misses_on_fingerprint_mismatch() {
    let root = temp_module_root();
    let fp = "aaaaaaaaaaaaaaaa";
    write_module_kb(
        &root,
        fp,
        0,
        &BTreeMap::new(),
        &[ExportKbWrite {
            export_file_id: 0,
            name: "main".into(),
            relative_path: "main.lit".into(),
            definitions: DefinitionMemory::new(),
            global_ids_at_enter: GlobalIdsSnapshot::new(1, 1, 1, 1),
            global_ids_at_leave: GlobalIdsSnapshot::new(1, 1, 1, 1),
        }],
    )
    .expect("write");

    let err = try_mount_module(
        &root,
        "bbbbbbbbbbbbbbbb",
        &GlobalIdsSnapshot::new(1, 1, 1, 1),
        &HashMap::new(),
    );
    assert!(matches!(err, Err(KbMountMiss::FingerprintMismatch { .. })));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn definition_memory_round_trip_string() {
    let defs = sample_defs(7, 42);
    let text = store_definition_memory(&defs).expect("store");
    let back = crate::knowledge_base::load_definition_memory(&text).expect("load");
    assert_eq!(store_definition_memory(&back).expect("re-store"), text);
}

#[test]
fn old_module_abi_is_a_cache_miss() {
    let root = temp_module_root();
    let fingerprint = "aaaaaaaaaaaaaaaa";
    write_module_kb(&root, fingerprint, 0, &BTreeMap::new(), &[]).expect("write current cache");
    let manifest = crate::knowledge_base::manifest_path(&root);
    let current = fs::read_to_string(&manifest).unwrap();
    let old = current.replace(
        &format!("\"abi\": \"{}\"", crate::knowledge_base::KB_ABI),
        "\"abi\": \"1\"",
    );
    assert_ne!(current, old);
    fs::write(&manifest, old).unwrap();
    let mounted = try_mount_module(
        &root,
        fingerprint,
        &GlobalIdsSnapshot::new(1, 1, 1, 1),
        &HashMap::new(),
    );
    assert!(matches!(
        mounted,
        Err(KbMountMiss::Corrupt(crate::knowledge_base::KbCodecError::Shape(message)))
            if message.contains("kb abi mismatch: file `1`")
    ));
    fs::remove_dir_all(&root).unwrap();
}
