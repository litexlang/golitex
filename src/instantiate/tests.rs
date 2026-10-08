use std::collections::HashMap;

use crate::ast::fact::{AtomicFact, EqualFact, QuantifierFreeFact};
use crate::ast::names::BoundName;
use crate::ast::obj::{IdentifierObj, Literal, Number, Obj, SetBuilder};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn test_runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

#[test]
fn inst_function_value_parameter_composes_returned_application_groups() {
    use crate::ast::obj::FnObj;
    use crate::ast::stmt::{DefinitionStmt, Stmt};

    let mut rt = test_runtime();
    let code = "have fn vec(A,B cart(R,R)) cart(R,R) = (B(1)-A(1),B(2)-A(2))\n\
have fn dot(u,v cart(R,R)) R = u(1)*v(1)+u(2)*v(2)\n\
have a,b cart(R,R)\n\
dot(vec(a,b),vec(a,b)) = vec(a,b)(1)*vec(a,b)(1)+vec(a,b)(2)*vec(a,b)(2)\n";
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let stmts = rt.parse(&tokens).unwrap();
    let Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(dot)) = &stmts[1] else {
        panic!("dot definition");
    };
    let Stmt::Fact(crate::ast::fact::Fact::AtomicFact(AtomicFact::EqualFact(goal))) = &stmts[3]
    else {
        panic!("dot expansion equality");
    };
    let Obj::FnObj(FnObj { body, .. }) = &goal.left else {
        panic!("dot call");
    };
    let subst = dot
        .equal_to_anonymous_fn
        .body
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|group| &group.params)
        .zip(&body[0])
        .map(|(param, arg)| (param.id, arg.as_ref().clone()))
        .collect();
    let actual = rt
        .inst_obj(&dot.equal_to_anonymous_fn.equal_to, &subst)
        .unwrap();
    assert_eq!(actual, goal.right);
}

#[test]
fn inst_returned_application_preserves_simultaneous_substitution_and_argument_groups() {
    use crate::ast::obj::FnObjHead;
    use crate::ast::stmt::Stmt;

    let mut rt = test_runtime();
    let code = "have F fn(seed R) fn(x,y R) R\n\
have p fn(x,y R) R\n\
have a R\n\
p(a,2) = F(a)(7,2)\n";
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let stmts = rt.parse(&tokens).unwrap();
    let Stmt::Fact(crate::ast::fact::Fact::AtomicFact(AtomicFact::EqualFact(goal))) = &stmts[3]
    else {
        panic!("application equality");
    };
    let Obj::FnObj(original) = &goal.left else {
        panic!("original call");
    };
    let FnObjHead::Identifier(IdentifierObj::Plain { id: p_id, .. }) = original.head.as_ref()
    else {
        panic!("function parameter");
    };
    let Obj::Identifier(IdentifierObj::Plain { id: a_id, .. }) = original.body[0][0].as_ref()
    else {
        panic!("argument parameter");
    };
    let Obj::FnObj(expected) = &goal.right else {
        panic!("composed call");
    };
    let mut replacement = expected.clone();
    replacement.body.truncate(1);
    let subst = HashMap::from([
        (*p_id, Obj::FnObj(replacement)),
        (*a_id, expected.body[1][0].as_ref().clone()),
    ]);
    let actual = rt.inst_obj(&goal.left, &subst).unwrap();
    assert_eq!(actual, goal.right);
}

#[test]
fn inst_equality_replaces_plain_identifier() {
    let mut runtime = test_runtime();
    let x_id = runtime.global_ids.allocate_identifier_id();
    let x = Obj::Identifier(IdentifierObj::plain(x_id, "x".into()));
    let zero = Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }));
    let one = Obj::Literal(Literal::Number(Number {
        normalized_value: "1".into(),
    }));
    let fact = QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
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
fn parse_have_then_free_ref_stays_plain_under_eval() {
    let mut runtime = test_runtime();
    let tokens = Tokenizer::new()
        .tokenize("have x R", runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1);

    // Eval has no publication slot: outermost free refs stay Plain (+ id).
    let tokens2 = Tokenizer::new()
        .tokenize("x = x", runtime.current_file.clone())
        .expect("tokenize");
    let stmts2 = runtime.parse(&tokens2).expect("parse");
    assert_eq!(stmts2.len(), 1);

    use crate::ast::fact::Fact;
    use crate::ast::stmt::Stmt;
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = &stmts2[0] else {
        panic!("expected EqualFact stmt");
    };
    let Obj::Identifier(IdentifierObj::Plain {
        name: left_name, ..
    }) = &eq.left
    else {
        panic!("left should stay Plain under Eval, got {:?}", eq.left);
    };
    let Obj::Identifier(IdentifierObj::Plain {
        name: right_name, ..
    }) = &eq.right
    else {
        panic!("right should stay Plain under Eval, got {:?}", eq.right);
    };
    assert_eq!(left_name, "x");
    assert_eq!(right_name, "x");
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

    use crate::ast::fact::Fact;
    use crate::ast::stmt::{ProofBlockStmt, Stmt};
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
            crate::module_manager::LitexConfig::new(),
        )
        .expect("record_import");
    runtime
        .global_module_manager
        .set_current_mod_id(Some(mod_id))
        .expect("set_current_mod_id");
    runtime.set_code_source(crate::runtime::CodeSource::ImportedExport {
        global_mod_id: mod_id,
        export_file_id: 0,
    });

    let tokens = Tokenizer::new()
        .tokenize("have x R", runtime.current_file.clone())
        .expect("tokenize");
    runtime.parse(&tokens).expect("parse have");
    let tokens2 = Tokenizer::new()
        .tokenize("x = 1", runtime.current_file.clone())
        .expect("tokenize");
    let stmts2 = runtime.parse(&tokens2).expect("parse fact");
    use crate::ast::fact::Fact;
    use crate::ast::stmt::Stmt;
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
