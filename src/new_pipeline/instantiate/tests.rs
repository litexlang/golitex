use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::{IdentifierObj, Number, Obj, SetBuilder, Literal};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::launch_command::LaunchCommand;
use crate::new_pipeline::runtime::Runtime;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::tokenize::Tokenizer;

fn test_runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
    })
}

#[test]
fn inst_equality_replaces_plain_identifier() {
    let mut runtime = test_runtime();
    let x_id = runtime.ids.allocate_identifier_id();
    let x = Obj::Identifier(IdentifierObj::plain(x_id, "x".into()));
    let zero = Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }));
    let one = Obj::Literal(Literal::Number(Number {
        normalized_value: "1".into(),
    }));
    let fact = QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left: x,
        right: zero,
        line_file: None,
    }));
    let mut subst = HashMap::new();
    subst.insert(x_id, one.clone());

    let result = runtime
        .inst_quantifier_free_fact(&fact, &subst)
        .expect("inst");

    match result {
        QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(f)) => {
            assert_eq!(f.left, one);
            assert_eq!(
                f.right,
                Obj::Literal(Literal::Number(Number {
                    normalized_value: "0".into()
                }))
            );
        }
        other => panic!("expected EqualFact, got {other:?}"),
    }
}

#[test]
fn plain_identifier_ir_embeds_id_display_is_name() {
    let id = IdentifierId::new(7);
    let obj = IdentifierObj::plain(id, "x".into());
    assert_eq!(obj.ir_string(), "#7#x");
    assert_eq!(obj.display_string(), "x");
    assert_eq!(obj.ir().as_str(), "#7#x");
}

#[test]
fn set_builder_ir_uses_bound_name_id_display_uses_letter() {
    let binding = BoundName::new(IdentifierId::new(2), "x".into());
    let sb = SetBuilder {
        param_binding: binding,
        param_set: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "0".into(),
        }))),
        facts: vec![],
    };
    assert!(sb.ir().as_str().contains("#2#x"));
    assert!(sb.display_string().starts_with("{x "));
    assert!(!sb.display_string().contains("#2#"));
}

#[test]
fn parse_have_then_free_ref_qualifies_at_file_root() {
    let mut runtime = test_runtime();
    let tokens = Tokenizer::new()
        .tokenize("have x R", runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1);

    // File-root free refs become WithExportFileId (export slot 0 for bare -e).
    let tokens2 = Tokenizer::new()
        .tokenize("x = x", runtime.current_file.clone())
        .expect("tokenize");
    let stmts2 = runtime.parse(&tokens2).expect("parse");
    assert_eq!(stmts2.len(), 1);

    use crate::new_pipeline::ast::fact::Fact;
    use crate::new_pipeline::ast::stmt::Stmt;
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = &stmts2[0] else {
        panic!("expected EqualFact stmt");
    };
    let Obj::Identifier(IdentifierObj::WithExportFileId {
        export_file_id: left_fid,
        name: left_name,
    }) = &eq.left
    else {
        panic!("left should be file-root qualified, got {:?}", eq.left);
    };
    let Obj::Identifier(IdentifierObj::WithExportFileId {
        export_file_id: right_fid,
        name: right_name,
    }) = &eq.right
    else {
        panic!("right should be file-root qualified, got {:?}", eq.right);
    };
    assert_eq!(left_name, "x");
    assert_eq!(right_name, "x");
    assert_eq!(*left_fid, 0);
    assert_eq!(*right_fid, 0);
    assert_eq!(eq.left.ir().as_str(), "f0::x");
}

#[test]
fn sketch_local_have_free_ref_stays_plain() {
    let mut runtime = test_runtime();
    let code = "\
sketch:
    have x R
    x = x
";
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1);

    use crate::new_pipeline::ast::fact::Fact;
    use crate::new_pipeline::ast::stmt::{ProofBlockStmt, Stmt};
    let Stmt::ProofBlock(ProofBlockStmt::SketchStmt(sketch)) = &stmts[0] else {
        panic!("expected sketch");
    };
    assert_eq!(sketch.proof.len(), 2);
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = &sketch.proof[1] else {
        panic!("expected x = x inside sketch");
    };
    let Obj::Identifier(IdentifierObj::Plain {
        name: left_name, ..
    }) = &eq.left
    else {
        panic!("sketch-local x must stay Plain, got {:?}", eq.left);
    };
    assert_eq!(left_name, "x");
}

#[test]
fn imported_mod_context_qualifies_with_mod_id() {
    let mut runtime = test_runtime();
    // Pretend we are parsing inside imports[0] as current module.
    let mod_id = runtime
        .global_module_manager
        .record_import(
            "modB".to_string(),
            std::path::PathBuf::from("/tmp/modB"),
            crate::new_pipeline::module_manager::LitexConfig::new(),
        )
        .expect("record_import");
    runtime
        .global_module_manager
        .set_current_mod_id(Some(mod_id))
        .expect("set_current_mod_id");
    runtime.set_current_export_file_id(0);

    let tokens = Tokenizer::new()
        .tokenize("have x R", runtime.current_file.clone())
        .expect("tokenize");
    runtime.parse(&tokens).expect("parse have");
    let tokens2 = Tokenizer::new()
        .tokenize("x = 1", runtime.current_file.clone())
        .expect("tokenize");
    let stmts2 = runtime.parse(&tokens2).expect("parse fact");
    use crate::new_pipeline::ast::fact::Fact;
    use crate::new_pipeline::ast::stmt::Stmt;
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = &stmts2[0] else {
        panic!("expected EqualFact");
    };
    let Obj::Identifier(IdentifierObj::WithModAndExportFileId {
        global_mod_id,
        export_file_id,
        name,
    }) = &eq.left
    else {
        panic!("expected WithModAndExportFileId, got {:?}", eq.left);
    };
    assert_eq!(*global_mod_id, mod_id);
    assert_eq!(*export_file_id, 0);
    assert_eq!(name, "x");
}
