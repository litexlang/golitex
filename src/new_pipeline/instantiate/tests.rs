use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::{IdentifierObj, Number, Obj, SetBuilder};
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
    let zero = Obj::Number(Number {
        normalized_value: "0".into(),
    });
    let one = Obj::Number(Number {
        normalized_value: "1".into(),
    });
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
                Obj::Number(Number {
                    normalized_value: "0".into()
                })
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
        param_set: Box::new(Obj::Number(Number {
            normalized_value: "0".into(),
        })),
        facts: vec![],
    };
    assert!(sb.ir().as_str().contains("#2#x"));
    assert!(sb.display_string().starts_with("{x "));
    assert!(!sb.display_string().contains("#2#"));
}

#[test]
fn parse_have_allocates_plain_id_and_resolves_refs() {
    let mut runtime = test_runtime();
    let tokens = Tokenizer::new()
        .tokenize("have x R", runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1);

    // After have, a following fact mentioning x should resolve the same id.
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
    let Obj::Identifier(IdentifierObj::Plain { id: left_id, name: left_name }) = &eq.left else {
        panic!("left");
    };
    let Obj::Identifier(IdentifierObj::Plain { id: right_id, name: right_name }) = &eq.right else {
        panic!("right");
    };
    assert_eq!(left_name, "x");
    assert_eq!(right_name, "x");
    assert_eq!(left_id, right_id);
    assert_eq!(eq.left.ir().as_str(), format!("#{}#x", left_id.value()));
}
