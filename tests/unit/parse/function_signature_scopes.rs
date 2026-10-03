use crate::ast::obj::{FnSet, FunctionSpace, IdentifierObj, Obj};
use crate::ast::stmt::{DefineObjStmt, DefinitionStmt, Stmt};
use crate::execute::execute_fact_stmt::{VerifyObjWellDefinedResult, VerifyState};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    })
}

fn parse(rt: &mut Runtime, code: &str) -> RuntimeResult<Vec<Stmt>> {
    let blocks = Tokenizer::new().tokenize(code, rt.current_file.clone())?;
    rt.parse(&blocks)
}

#[test]
fn function_signature_scopes_reject_parameter_and_return_dependencies_during_parse() {
    for code in [
        "let F = fn(S power_set(R), x S) R",
        "let F = fn(x x) R",
        "let F = fn(x y, y R) R",
        "have S fn(t R) power_set(R)\nlet F = fn(x R, y S(x)) R",
        "let F = fn(x R) {x}",
        "let F = fn(x R) {z R: z > x}",
        "let F = fn(S power_set(R)) fn(x S) R",
        "let F = fn(x R) fn(y R: y > x) R",
        "let F = fn(x R) {x} {x}",
        "have fn f(x R) {x} = x",
        "have fn f(S power_set(R), x S) R = x",
        "have fn f(x R) {x} by cases:\n    case x = x: x",
        "have fn f(n N) {n} by induc n from 0:\n    case n = 0: 0\n    case n >= 1: n",
        "algo f(x R) {x} by cases:\n    case x = x: x",
        "algo f(n N) {n} by induc n from 0:\n    case n = 0: 0\n    case n >= 1: n",
        "have fn f by exist!:\n    ? forall S power_set(R), x S:\n        exist! y R st {y = x}",
        "have fn f by exist!:\n    ? forall x R:\n        exist! y {x} st {y = x}",
    ] {
        let error = parse(&mut runtime(), code).expect_err(code);
        let message = format!("{error:?}");
        assert!(message.contains("undefined name") || message.contains("must not reference"), "{code}: {message}");
    }
}

#[test]
fn function_signature_scopes_preserve_conditions_bodies_and_external_carriers() {
    for code in [
        "let F = fn(x R, y Z: y > x) R",
        "let f = fn(x R: x > 0) R {x + 1}",
        "have fn f(x R, y R: y > x) R = x + y",
        "have fn f(x R) R by cases:\n    case x = 0: x\n    case x != 0: x + 1",
        "have fn f(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: f(n - 1)",
        "algo f(x R) R by cases:\n    case x = x: x",
        "algo f(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: f(n - 1)",
        "have fn f by exist!:\n    ? forall x R:\n        exist! y R st {y = x}",
        "forall A set:\n    fn(x A) A = fn(y A) A",
        "forall S power_set(R), x S:\n    x = x",
        "template<A set>:\n    have fn identity(x A) A = x",
        "let F = fn(x R) fn(y R) R",
        "let F = fn(x R) {x R: x > 0}",
        "let F = fn(x {x R: x > 0}) R",
        "obtain k from exist k R st {k = 0}",
    ] {
        parse(&mut runtime(), code).expect(code);
    }
}

#[test]
fn function_signature_scopes_keep_disjoint_same_spelling_binders_independent() {
    let mut rt = runtime();
    let mut statements = parse(&mut rt, "let F = fn(x R) fn(x R) R").unwrap();
    let Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::LetObjStmt(stmt))) = statements.remove(0) else { panic!("let object") };
    let Obj::FunctionSpace(FunctionSpace::FnSet(outer)) = stmt.value else { panic!("outer fn") };
    let Obj::FunctionSpace(FunctionSpace::FnSet(inner)) = *outer.ret_set else { panic!("inner fn") };
    assert_ne!(outer.set_bound_parameters.groups[0].params[0].id, inner.set_bound_parameters.groups[0].params[0].id);
    parse(&mut runtime(), "have fn f(x fn(x R) R) R = x(0)").unwrap();
    assert!(parse(&mut runtime(), "have x R\nlet F = fn(x R) R").is_err(), "visible outer names still cannot be shadowed");
}

#[test]
fn function_signature_scopes_rollback_failed_carriers_and_do_not_leak_binders() {
    let mut rt = runtime();
    assert!(parse(&mut rt, "let F = fn(S power_set(R)) fn(x S) R").is_err());
    for name in ["F", "S", "x"] { assert!(!rt.plain_atom_is_visible(name)); }
    parse(&mut rt, "have fn F(x R: x > 0) R = x").unwrap();
    assert!(rt.plain_atom_is_visible("F"));
    assert!(!rt.plain_atom_is_visible("x"));
    assert!(parse(&mut rt, "let G = fn(x R: x > missing) R").is_err());
    assert!(!rt.plain_atom_is_visible("G"));
    assert!(!rt.plain_atom_is_visible("x"));
}

fn parsed_fn_set(rt: &mut Runtime, code: &str) -> FnSet {
    let mut statements = parse(rt, code).unwrap();
    let Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::LetObjStmt(stmt))) = statements.remove(0) else { panic!("let object") };
    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = stmt.value else { panic!("fn set") };
    signature
}

#[test]
fn function_signature_scopes_wd_rejects_independently_constructed_dependent_asts() {
    let mut rt = runtime();
    let outer = parsed_fn_set(&mut rt, "let F = fn(S power_set(R), x R) R");
    let binder = &outer.set_bound_parameters.groups[0].params[0];
    let reference = Obj::Identifier(IdentifierObj::plain(binder.id, binder.name.clone()));
    let mut inner = parsed_fn_set(&mut rt, "let G = fn(y R) R");
    inner.set_bound_parameters.groups[0].param_type = Box::new(reference.clone());
    let mut dependent_return = outer.clone();
    dependent_return.ret_set = Box::new(Obj::FunctionSpace(FunctionSpace::FnSet(inner)));
    let mut dependent_parameter = outer.clone();
    dependent_parameter.set_bound_parameters.groups[1].param_type = Box::new(reference.clone());
    let mut self_dependent_parameter = outer;
    self_dependent_parameter.set_bound_parameters.groups[0].param_type = Box::new(reference);
    for signature in [dependent_return, dependent_parameter, self_dependent_parameter] {
        for object in [
            Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(crate::ast::obj::AnonymousFn {
                body: signature, equal_to: Box::new(Obj::StandardSet(crate::ast::obj::StandardSet::R)),
            })),
        ] {
            let result = rt.verify_obj_well_definedness(&object, VerifyState::top_level()).unwrap();
            assert!(matches!(result, VerifyObjWellDefinedResult::Failed { .. }));
            assert_eq!(rt.execution_environments_stack.len(), 1);
        }
    }
}

#[test]
fn function_signature_scopes_run_the_durable_positive_tracer() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!("../../../examples/wd/fixed_function_signature_scopes.lit")).unwrap();
    assert!(run.success, "{:?}", run.session_error);
    assert!(run.session_error.is_none());
}
