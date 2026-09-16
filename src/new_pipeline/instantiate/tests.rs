use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::{IdentifierObj, Number, Obj};
use crate::new_pipeline::launch_command::LaunchCommand;
use crate::new_pipeline::runtime::Runtime;

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
    let x = Obj::Identifier(IdentifierObj::plain("x".into()));
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
    subst.insert("x".into(), one.clone());

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
