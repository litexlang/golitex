//! Module-qualified object reference parser regressions.

use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_one_obj_line_with_runtime(rt: &mut Runtime, line: &str) -> Obj {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(line, Rc::from("test.lit"))
        .expect("tokenize object line");
    assert_eq!(blocks.len(), 1, "{line:?}");
    rt.parse_obj(&mut blocks[0]).expect("parse object line")
}

fn parse_one_fact_line_with_runtime(rt: &mut Runtime, line: &str) -> Fact {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(line, Rc::from("test.lit"))
        .expect("tokenize fact line");
    assert_eq!(blocks.len(), 1, "{line:?}");
    rt.parse_fact(&mut blocks[0]).expect("parse fact line")
}

fn parse_one_stmt_line_with_runtime(rt: &mut Runtime, line: &str) -> Stmt {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(line, Rc::from("test.lit"))
        .expect("tokenize stmt line");
    assert_eq!(blocks.len(), 1, "{line:?}");
    rt.parse_statement(&mut blocks[0]).expect("parse stmt line")
}

fn set_test_module_name(rt: &mut Runtime, module_name: &str) {
    if rt.execution_stack.is_empty() {
        rt.start_isolated_source("test.lit");
    }
    rt.current_module_mut().module_name = module_name.to_string();
}

fn assert_with_mod(name: &AtomicName, expected_mod_name: &str, expected_name: &str) {
    let AtomicName::WithMod(mod_name, name) = name else {
        panic!("expected module-qualified name");
    };
    assert_eq!(mod_name, expected_mod_name);
    assert_eq!(name, expected_name);
}

fn assert_without_mod(name: &AtomicName, expected_name: &str) {
    let AtomicName::WithoutMod(name) = name else {
        panic!("expected bare name");
    };
    assert_eq!(name, expected_name);
}

#[test]
fn parses_angle_bracketed_struct_params_and_defined_field_access() {
    let mut rt = Runtime::default();

    let stmt = parse_one_stmt_line_with_runtime(
        &mut rt,
        "struct Group<s set>:\n    inv fn(x s) s\n    op fn(x, y s) s\n    identity s",
    );
    let Stmt::Definition(DefinitionStmt::DefStructStmt(stmt)) = stmt else {
        panic!("expected struct definition");
    };
    let Some((param_def, _)) = &stmt.param_def_with_dom else {
        panic!("expected struct parameter definition");
    };
    assert_eq!(param_def.collect_param_names(), vec!["s".to_string()]);
    assert_eq!(
        strip_free_param_numeric_tags_in_display(&format!("{}", stmt)),
        "struct Group<s set>:"
    );
    rt.execute_statement(&Stmt::Definition(DefinitionStmt::DefStructStmt(stmt)))
        .expect("store struct definition");

    let have = parse_one_stmt_line_with_runtime(&mut rt, "trust have p &Group<R>");
    rt.execute_statement(&have)
        .expect("store defined struct carrier");

    let obj = parse_one_obj_line_with_runtime(&mut rt, "p.op");
    let Obj::ObjAsStructInstanceWithFieldAccess(access) = obj else {
        panic!("expected struct field access");
    };
    assert_without_mod(&access.struct_obj.name, "Group");
    assert_eq!(access.struct_obj.params.len(), 1);
    assert_eq!(access.field_name, "op");
    assert_eq!(
        strip_free_param_numeric_tags_in_display(&format!("{}", access)),
        "p.op"
    );

    let old_obj = parse_one_obj_line_with_runtime(&mut rt, "&Group(R)");
    assert_eq!(
        strip_free_param_numeric_tags_in_display(&format!("{}", old_obj)),
        "&Group<R>"
    );

    let projected_call = parse_one_obj_line_with_runtime(&mut rt, "p[2](x, y)");
    assert_eq!(
        strip_free_param_numeric_tags_in_display(&format!("{}", projected_call)),
        "p[2](x, y)"
    );

    let field_call = parse_one_obj_line_with_runtime(&mut rt, "p.op(x, y)");
    assert_eq!(
        strip_free_param_numeric_tags_in_display(&format!("{}", field_call)),
        "p.op(x, y)"
    );
}

#[test]
fn parses_comma_separated_set_builder_facts() {
    let mut rt = Runtime::default();

    let obj = parse_one_obj_line_with_runtime(&mut rt, "{d N+: d > 0, d < 2}");
    let Obj::SetBuilder(set_builder) = obj else {
        panic!("expected set builder");
    };
    assert_eq!(set_builder.facts.len(), 2);
}

#[test]
fn module_qualification_keeps_definition_name_bare() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let stmt = parse_one_stmt_line_with_runtime(&mut rt, "abstract_prop some_prop(x)");

    let Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(stmt)) = stmt else {
        panic!("expected abstract prop definition");
    };
    assert_eq!(stmt.name, "some_prop");
}

#[test]
fn parses_replacement_object_prop_name_arguments() {
    let mut rt = Runtime::default();

    let obj = parse_one_obj_line_with_runtime(&mut rt, "replacement(P, A)");
    let Obj::Replacement(replacement) = obj else {
        panic!("expected replacement object");
    };
    assert_without_mod(&replacement.prop_name, "P");
    assert_eq!(format!("{}", replacement), "replacement(P, A)");

    let obj = parse_one_obj_line_with_runtime(&mut rt, "replacement(M::P, A)");
    let Obj::Replacement(replacement) = obj else {
        panic!("expected replacement object");
    };
    assert_with_mod(&replacement.prop_name, "M", "P");
    assert_eq!(format!("{}", replacement), "replacement(M::P, A)");
}

#[test]
fn replacement_rejects_non_name_first_argument() {
    let mut rt = Runtime::default();
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("replacement(1, A)", Rc::from("test.lit"))
        .expect("tokenize object line");
    assert_eq!(blocks.len(), 1);
    let err = match rt.parse_obj(&mut blocks[0]) {
        Ok(obj) => panic!("replacement should reject numbers, parsed {}", obj),
        Err(err) => err,
    };
    let RuntimeError::ParseError(err) = err else {
        panic!("expected parse error");
    };
    assert!(
        err.msg
            .contains("replacement expects its first argument to be a prop name"),
        "unexpected error: {}",
        err.msg
    );
}

#[test]
fn module_qualification_qualifies_bare_predicate_but_not_bound_arg() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let fact = parse_one_fact_line_with_runtime(&mut rt, "forall x Z:\n    $some_prop(x)");

    let Fact::ForallFact(forall_fact) = fact else {
        panic!("expected forall fact");
    };
    assert_eq!(forall_fact.then_facts.len(), 1);
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(atomic_fact)) =
        &forall_fact.then_facts[0]
    else {
        panic!("expected normal atomic fact");
    };
    let AtomicName::WithMod(mod_name, name) = &atomic_fact.predicate else {
        panic!("expected module-qualified predicate");
    };
    assert_eq!(mod_name, "Nat");
    assert_eq!(name, "some_prop");
    let Obj::Atom(AtomObj::Bound(arg)) = &atomic_fact.body[0] else {
        panic!("expected forall-bound argument");
    };
    assert_eq!(arg.name(), "x");
}

#[test]
fn module_qualification_qualifies_bare_identifier() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let obj = parse_one_obj_line_with_runtime(&mut rt, "a");

    let Obj::Atom(AtomObj::IdentifierWithMod(id)) = obj else {
        panic!("expected module-qualified identifier");
    };
    assert_eq!(id.mod_name, "Nat");
    assert_eq!(id.name, "a");
}

#[test]
fn backtick_infix_function_syntax_is_rejected() {
    let mut rt = Runtime::default();
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("a ` f b = c", Rc::from("test.lit"))
        .expect("tokenize stmt line");
    assert_eq!(blocks.len(), 1);
    assert!(rt.parse_statement(&mut blocks[0]).is_err());
}

#[test]
fn module_qualification_keeps_native_constants_structural() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let euler = parse_one_obj_line_with_runtime(&mut rt, "e");
    let pi = parse_one_obj_line_with_runtime(&mut rt, "pi");

    assert!(matches!(euler, Obj::EulerNumber(_)));
    assert!(matches!(pi, Obj::Pi(_)));
    assert_eq!(euler.to_string(), "e");
    assert_eq!(pi.to_string(), "pi");
}

#[test]
fn native_constants_are_hard_reserved_only_as_exact_names() {
    assert!(is_keyword(E));
    assert!(is_keyword(PI));

    let tokenizer = Tokenizer::new();
    for source in ["have e R", "have pi R", "forall e R:\n    e = e"] {
        let mut blocks = tokenizer
            .parse_blocks(source, Rc::from("test.lit"))
            .expect("tokenize reserved-name statement");
        assert_eq!(blocks.len(), 1, "{source:?}");
        assert!(
            Runtime::default().parse_statement(&mut blocks[0]).is_err(),
            "{source:?} should reject the reserved binding"
        );
    }

    parse_one_stmt_line_with_runtime(&mut Runtime::default(), "have e1, pi1 R");
}

#[test]
fn module_qualification_keeps_finite_set_size_builtin_bare() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let obj = parse_one_obj_line_with_runtime(&mut rt, "finite_set_size({1, 2})");

    let Obj::FiniteSetSize(_) = obj else {
        panic!("expected finite_set_size builtin object");
    };
}

#[test]
fn module_qualification_qualifies_bare_thm_strategy_template_and_struct_refs() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "release thm T(a)");
    let Stmt::ReleaseThmStmt(thm_stmt) = thm_stmt else {
        panic!("expected release thm stmt");
    };
    assert_with_mod(&thm_stmt.name, "Nat", "T");

    let def_stmt = parse_one_stmt_line_with_runtime(&mut rt, "by def $P(a)");
    let Stmt::By(ByStmt::ByDefStmt(def_stmt)) = def_stmt else {
        panic!("expected by def stmt");
    };
    let AtomicFact::NormalAtomicFact(fact) = &def_stmt.fact else {
        panic!("expected normal atomic fact");
    };
    assert_with_mod(&fact.predicate, "Nat", "P");

    let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\Template<2>");
    let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
        panic!("expected instantiated template object");
    };
    assert_with_mod(&template_obj.template_name, "Nat", "Template");

    let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&Struct");
    let Obj::StructObj(struct_obj) = struct_obj else {
        panic!("expected struct object");
    };
    assert_with_mod(&struct_obj.name, "Nat", "Struct");
}

#[test]
fn module_qualification_preserves_explicit_reference_module_names() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "release thm Other::T(a)");
    let Stmt::ReleaseThmStmt(thm_stmt) = thm_stmt else {
        panic!("expected release thm stmt");
    };
    assert_with_mod(&thm_stmt.name, "Other", "T");

    let def_stmt = parse_one_stmt_line_with_runtime(&mut rt, "by def $Other::P(a)");
    let Stmt::By(ByStmt::ByDefStmt(def_stmt)) = def_stmt else {
        panic!("expected by def stmt");
    };
    let AtomicFact::NormalAtomicFact(fact) = &def_stmt.fact else {
        panic!("expected normal atomic fact");
    };
    assert_with_mod(&fact.predicate, "Other", "P");

    let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\Other::Template<2>");
    let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
        panic!("expected instantiated template object");
    };
    assert_with_mod(&template_obj.template_name, "Other", "Template");

    let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&Other::Struct");
    let Obj::StructObj(struct_obj) = struct_obj else {
        panic!("expected struct object");
    };
    assert_with_mod(&struct_obj.name, "Other", "Struct");
}

#[test]
fn standard_library_namespace_is_valid_only_as_a_qualified_module_root() {
    let mut rt = Runtime::default();

    let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "release thm basics::T(a)");
    let Stmt::ReleaseThmStmt(thm_stmt) = thm_stmt else {
        panic!("expected release thm stmt");
    };
    assert_with_mod(&thm_stmt.name, "basics", "T");

    let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\basics::Template<2>");
    let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
        panic!("expected instantiated template object");
    };
    assert_with_mod(&template_obj.template_name, "basics", "Template");

    let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&basics::Struct");
    let Obj::StructObj(struct_obj) = struct_obj else {
        panic!("expected struct object");
    };
    assert_with_mod(&struct_obj.name, "basics", "Struct");

    let replacement_obj = parse_one_obj_line_with_runtime(&mut rt, "replacement(basics::P, A)");
    let Obj::Replacement(replacement_obj) = replacement_obj else {
        panic!("expected replacement object");
    };
    assert_with_mod(&replacement_obj.prop_name, "basics", "P");

    let obj = parse_one_obj_line_with_runtime(&mut rt, "basics::value");
    let Obj::Atom(AtomObj::IdentifierWithMod(obj)) = obj else {
        panic!("expected module-qualified identifier");
    };
    assert_eq!(obj.mod_name, "basics");
    assert_eq!(obj.name, "value");

    let fact = parse_one_fact_line_with_runtime(&mut rt, "$basics::P(a)");
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(fact)) = fact else {
        panic!("expected normal atomic fact");
    };
    assert_with_mod(&fact.predicate, "basics", "P");

    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks("release thm std(a)", Rc::from("test.lit"))
        .expect("tokenize theorem reference");
    assert_eq!(blocks.len(), 1);
    assert!(rt.parse_statement(&mut blocks[0]).is_err());

    let mut blocks = tokenizer
        .parse_blocks("release thm Other::std::T(a)", Rc::from("test.lit"))
        .expect("tokenize nested module reference");
    assert_eq!(blocks.len(), 1);
    assert!(rt.parse_statement(&mut blocks[0]).is_err());
}

#[test]
fn module_qualification_preserves_explicit_module_names() {
    let mut rt = Runtime::default();
    set_test_module_name(&mut rt, "Nat");

    let obj = parse_one_obj_line_with_runtime(&mut rt, "Other::a");

    let Obj::Atom(AtomObj::IdentifierWithMod(id)) = obj else {
        panic!("expected module-qualified identifier");
    };
    assert_eq!(id.mod_name, "Other");
    assert_eq!(id.name, "a");
}

#[test]
fn module_qualification_keeps_names_bare_without_module_context() {
    let mut rt = Runtime::default();

    let obj = parse_one_obj_line_with_runtime(&mut rt, "a");
    let Obj::Atom(AtomObj::Identifier(id)) = obj else {
        panic!("expected bare identifier");
    };
    assert_eq!(id.name, "a");

    let fact = parse_one_fact_line_with_runtime(&mut rt, "$some_prop(a)");
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(atomic_fact)) = fact else {
        panic!("expected normal atomic fact");
    };
    let AtomicName::WithoutMod(name) = &atomic_fact.predicate else {
        panic!("expected bare predicate");
    };
    assert_eq!(name, "some_prop");

    let thm_stmt = parse_one_stmt_line_with_runtime(&mut rt, "release thm T(a)");
    let Stmt::ReleaseThmStmt(thm_stmt) = thm_stmt else {
        panic!("expected release thm stmt");
    };
    assert_without_mod(&thm_stmt.name, "T");

    let template_obj = parse_one_obj_line_with_runtime(&mut rt, "\\Template<2>");
    let Obj::InstantiatedTemplateObj(template_obj) = template_obj else {
        panic!("expected instantiated template object");
    };
    assert_without_mod(&template_obj.template_name, "Template");

    let struct_obj = parse_one_obj_line_with_runtime(&mut rt, "&Struct");
    let Obj::StructObj(struct_obj) = struct_obj else {
        panic!("expected struct object");
    };
    assert_without_mod(&struct_obj.name, "Struct");
}
