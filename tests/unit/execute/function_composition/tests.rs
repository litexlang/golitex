use crate::prelude::*;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn check(rt: &mut Runtime, code: &str, accepted: bool) {
    let run = rt.run_litex_code(code).expect(code);
    assert!(
        run.session_error.is_none(),
        "hard error: {code}\n{:?}",
        run.session_error
    );
    assert_eq!(
        run.success,
        accepted,
        "{code}\n{}",
        crate::json_output::emit_run_detailed(&run, rt, "test", None)
    );
}
fn base() -> Runtime {
    let mut rt = runtime();
    check(&mut rt, "have fn square(t R) R = t^2", true);
    check(&mut rt, "have fn gap(x,y R: x<y) R = y-x", true);
    check(&mut rt, "have fn add1(x R) R = x+1", true);
    check(&mut rt, "have fn identity(x R) R = x", true);
    rt
}
#[test]
fn function_composition_guarded_tracer_and_failure_retention() {
    let mut rt = base();
    check(&mut rt, "have h fn(x,y R: x<y) R = square ∘ gap", true);
    check(&mut rt, "h(1,3)=4", true);
    check(&mut rt, "compose(square,gap)(1,3)=4", true);
    check(&mut rt, "(square ∘ gap)(1,3)=square(gap(1,3))", true);
    for bad in ["h(3,1)=4", "h(1)=4", "h(1,3,4)=4", "h(1,3)=9"] {
        check(&mut rt, bad, false);
    }
    check(&mut rt, "h(2,5)=9", true);
    check(&mut rt, "let alias = square ∘ gap", true);
    check(&mut rt, "alias(1,3)=4", true);
}
#[test]
fn function_composition_strict_domain_and_arity() {
    let mut rt = base();
    check(&mut rt, "have fn inv(t R: t!=0) R = 1/t", true);
    check(&mut rt, "have fn one(x R) R = 1", true);
    check(&mut rt, "let good = inv ∘ one", true);
    check(&mut rt, "good(0)=1", true);
    for bad in [
        "let bad = inv ∘ identity",
        "let bad = compose(123,one)",
        "let bad = gap ∘ one",
        "let bad = one ∘ 123",
        "let bad = (inv ∘ identity) ∘ one",
    ] {
        check(&mut rt, bad, false);
    }
    // The existing nonzero checker does not unfold arbitrary nested bodies.
    // Expose the universal guard explicitly, then retry in the same runtime.
    check(&mut rt, "let good_nested = inv ∘ (identity ∘ one)", false);
    check(
        &mut rt,
        "forall x R:\n    (identity ∘ one)(x)=1\n    (identity ∘ one)(x)!=0",
        true,
    );
    check(&mut rt, "let good_nested = inv ∘ (identity ∘ one)", true);
    check(&mut rt, "good_nested(7)=1", true);
    check(&mut rt, "square(3)=9", true);
}
#[test]
fn function_composition_laws_and_false_neighbors() {
    let mut rt = base();
    for code in [
        "(square ∘ add1)(2)=9",
        "(add1 ∘ square)(2)=5",
        "(square ∘ add1) ∘ gap = square ∘ (add1 ∘ gap)",
        "identity ∘ gap = gap",
        "square ∘ identity = square",
        "square ∘ gap = fn(x,y R: x<y) R {square(gap(x,y))}",
        "square ∘ gap $in fn(x,y R: x<y) R",
        "fn_range(square ∘ gap) $subset fn_range(square)",
        "$is_set(preimage(square ∘ gap,4))",
    ] {
        check(&mut rt, code, true);
    }
    for code in [
        "(square ∘ add1)(2)=5",
        "square ∘ add1 = add1 ∘ square",
        "square ∘ (fn(x N) N {x}) = square",
        "square ∘ gap $in fn(x,y R) R",
    ] {
        check(&mut rt, code, false);
    }
}
#[test]
fn function_composition_guarded_unit_and_congruence() {
    let mut rt = base();
    check(&mut rt, "have fn inv(x R: x!=0) R = 1/x", true);
    check(&mut rt, "inv ∘ (fn(x R: x!=0) R {x}) = inv", true);
    check(&mut rt,"forall f1,f2 fn(x R) R, g1,g2 fn(x,y R: x<y) R:\n    f1=f2\n    g1=g2\n    =>:\n        f1 ∘ g1 = f2 ∘ g2",true);
    check(
        &mut rt,
        "by fn_extension square ∘ gap = fn(x,y R: x<y) R {square(gap(x,y))}",
        true,
    );
}
#[test]
fn function_composition_abstract_guard_proof() {
    let mut rt = runtime();
    check(&mut rt, "have fn inv(x R: x!=0) R = 1/x", true);
    check(&mut rt,"forall g fn(x R) R:\n    forall x R:\n        g(x)!=0\n    =>:\n        compose(inv,g) $in fn(x R) R",true);
    check(
        &mut rt,
        "forall g fn(x R) R:\n    compose(inv,g) $in fn(x R) R",
        false,
    );
}
#[test]
fn function_composition_returned_functions_and_capture() {
    let mut rt = base();
    for code in [
        "have shift R = 7",
        "have fn shifted(x R) R = x+shift",
        "let captured = shifted ∘ add1",
        "captured(2)=3+shift",
        "3+shift=10",
        "captured(2)=10",
    ] {
        check(&mut rt, code, true);
    }
}
#[test]
fn function_composition_returned_function() {
    let mut rt = base();
    for code in [
        "have fn factory(x R) fn(y R) R = fn(y R) R {x+y}",
        "let nested = factory ∘ add1",
        "nested(2)(4)=7",
    ] {
        check(&mut rt, code, true);
    }
}
#[test]
fn function_composition_higher_order_argument() {
    let mut rt = base();
    for code in [
        "have fn factory(x R) fn(y R) R = fn(y R) R {x+y}",
        "have fn consumer(f fn(x R) R) R = f(2)",
        "let higher = consumer ∘ factory",
        "higher(3)=5",
    ] {
        check(&mut rt, code, true);
    }
}
#[test]
fn function_composition_as_returned_value() {
    let mut rt = base();
    for code in [
        "have fn returns(x R) fn(y R) R = square ∘ add1",
        "returns(0)(2)=9",
    ] {
        check(&mut rt, code, true);
    }
}
#[test]
fn function_composition_finite_function_and_tuple_argument() {
    let mut rt = base();
    for code in [
        "let finite = square ∘ (2,3)",
        "finite(1)=4",
        "finite(2)=9",
        "have fn pair(x R) cart(R,R) = (x,x+1)",
        "have fn fst(p cart(R,R)) R = p(1)",
        "(fst ∘ pair)(3)=3",
    ] {
        check(&mut rt, code, true);
    }
    check(&mut rt, "let invalid = gap ∘ pair", false);
}

fn expression(rt: &mut Runtime, code: &str) -> Obj {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(&format!("eval {code}"), rt.current_file.clone())
        .unwrap();
    let Stmt::Command(crate::ast::stmt::CommandStmt::EvalStmt(eval)) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("eval");
    };
    eval.obj_to_eval
}
#[test]
fn function_composition_syntax_roundtrip_and_precedence() {
    let mut rt = base();
    for (unicode, ascii) in [
        ("square ∘ add1", "compose(square,add1)"),
        (
            "square ∘ add1 ∘ identity",
            "compose(square,compose(add1,identity))",
        ),
        (
            "(square ∘ add1) ∘ identity",
            "compose(compose(square,add1),identity)",
        ),
        ("(square ∘ add1)(2)", "compose(square,add1)(2)"),
        ("square ∘ add1(2)", "compose(square,add1(2))"),
        ("1+square ∘ add1*2", "1+compose(square,add1)*2"),
        ("-square ∘ add1^2", "compose(-square,add1^2)"),
    ] {
        let a = expression(&mut rt, unicode);
        let b = expression(&mut rt, ascii);
        assert_eq!(a, b, "{unicode}");
        assert_eq!(a.ir(), expression(&mut rt, &a.readable_string()).ir());
    }
    assert_ne!(
        expression(&mut rt, "square ∘ add1 ∘ identity"),
        expression(&mut rt, "(square ∘ add1) ∘ identity")
    );
    for code in [
        "compose(square)=square",
        "compose(square,add1,identity)=square",
        "have compose R=1",
        "forall compose R:\n    compose=compose",
    ] {
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "{code}");
    }
}
#[test]
fn function_composition_latex_parentheses() {
    let latex = crate::compile_to_latex::to_latex_from_source(
        "forall f,g,h fn(x R) R:\n    (f ∘ g) ∘ h = f ∘ g ∘ h\n    (f ∘ g)(2)=f(g(2))",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(latex.contains("\\circ"), "{latex}");
    assert!(latex.contains("(f \\circ g)"), "{latex}");
}

#[test]
fn function_composition_field_template_and_heterogeneous_inputs() {
    let mut rt = base();
    for code in [
        "struct Ops:\n    op fn(x R) R\n    tag N",
        "have ops &Ops=(add1,0)",
        "have field_comp fn(x R) R = square ∘ ops.op",
        "field_comp(2)=square(ops.op(2))",
        "ops.op(2)=3",
        "square(ops.op(2))=square(3)",
        "square(3)=9",
        "square(ops.op(2))=9",
        "field_comp(2)=9",
        "square ∘ add1 $in fn(x R) R",
        "have composed_ops &Ops=(square ∘ add1,0)",
        "composed_ops.op(2)=square(add1(2))",
        "square(add1(2))=9",
        "composed_ops.op(2)=9",
        "template<a R>:\n    have fn translated(x R) R=x+a",
        "(square ∘ \\translated<1>)(2)=9",
        "have fn mixed(x R,n N: x<n) R=n-x",
        "have hm fn(x R,n N: x<n) R = square ∘ mixed",
        "hm(1,3)=4",
    ] {
        check(&mut rt, code, true);
    }
    check(&mut rt, "hm(1,-3)=4", false);
    check(&mut rt, "hm(3,1)=4", false);
}

#[test]
fn function_composition_empty_domain_and_cyclic_equalities() {
    let mut rt = base();
    for code in [
        "have fn empty_fn(x {}) R=0",
        "square ∘ empty_fn $in fn(x {}) R",
        "fn_range(square ∘ empty_fn)={}",
        "identity ∘ square = square",
        "(identity ∘ square)(2)=4",
        "square ∘ identity = square",
        "(square ∘ identity)(2)=4",
        "forall f,g fn(x R) R:\n    f=identity ∘ g\n    g=identity ∘ f\n    =>:\n        (square ∘ f)(0) $in R",
    ] { check(&mut rt,code,true); }
    for code in [
        "let invalid=compose(123,empty_fn)",
        "(square ∘ empty_fn)(0)=0",
        "fn_range(square ∘ empty_fn)={0}",
    ] {
        check(&mut rt, code, false);
    }
}

#[test]
fn function_composition_evidence_and_permission_ceiling() {
    use crate::execute::execute_fact_stmt::VerifyStateLevel;
    for (code, rule) in [
        (
            "(square ∘ add1) ∘ gap = square ∘ (add1 ∘ gap)",
            "CompositionAssociativity",
        ),
        ("identity ∘ gap=gap", "CompositionLeftIdentity"),
        ("square ∘ identity=square", "CompositionRightIdentity"),
        (
            "square ∘ gap=fn(x,y R: x<y) R {square(gap(x,y))}",
            "CompositionDefinition",
        ),
        (
            "fn_range(square ∘ gap) $subset fn_range(square)",
            "CompositionRangeSubset",
        ),
    ] {
        let mut rt = base();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact");
        };
        assert!(rt
            .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
            .unwrap()
            .is_failed());
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success, "{code}");
        let detailed = crate::json_output::emit_run_detailed(&run, &rt, "test", None);
        assert!(detailed.contains(rule), "{rule}: {detailed}");
    }
    let mut rt = base();
    let rejected = rt
        .run_litex_code("have invalid fn(x,y R) R = square ∘ gap")
        .unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
    let json = crate::json_output::project_run_normal(&rejected, &rt, "test", None);
    let row = &json
        .as_object()
        .unwrap()
        .get("statement_results")
        .unwrap()
        .as_array()
        .unwrap()[0];
    for key in ["stores", "infers"] {
        assert!(row
            .as_object()
            .unwrap()
            .get(key)
            .unwrap()
            .as_array()
            .unwrap()
            .is_empty());
    }
    check(&mut rt, "have invalid R=7", true);
    check(&mut rt, "invalid=7", true);
    check(&mut rt, "have fn inv(x R:x!=0) R=1/x", true);
    let run=rt.run_litex_code("forall g fn(x R) R:\n    forall x R:\n        g(x)!=0\n    =>:\n        compose(inv,g) $in fn(x R) R").unwrap();
    assert!(run.success);
    let detailed = crate::json_output::emit_run_detailed(&run, &rt, "test", None);
    for fragment in [
        "parent_atomic_well_defined",
        "function_well_defined",
        "by_known_forall",
    ] {
        assert!(detailed.contains(fragment), "{fragment}");
    }
    check(
        &mut rt,
        "forall g fn(x R) R:\n    compose(inv,g) $in fn(x R) R",
        false,
    );
}

#[test]
fn function_composition_durable_examples_and_lean_boundary() {
    let files = [
        "examples/wd/function_composition.lit",
        "examples/proof_nodes/equal/by_builtin_rule/composition_associativity.lit",
        "examples/proof_nodes/equal/by_builtin_rule/composition_left_identity.lit",
        "examples/proof_nodes/equal/by_builtin_rule/composition_right_identity.lit",
        "examples/proof_nodes/equal/by_builtin_rule/composition_definition.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/composition_range_subset.lit",
    ];
    for file in files {
        check(
            &mut runtime(),
            &std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(file))
                .unwrap(),
            true,
        );
    }
    let command = crate::launch_command::parse_launch_command(&[
        "-lean".into(),
        "-f".into(),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(files[0])
            .to_string_lossy()
            .into_owned(),
    ])
    .unwrap();
    let error = crate::run::run_command(command)
        .err()
        .expect("native composition Lean replay is unsupported");
    assert!(
        error.to_string().contains("WD/FunctionSpace/Composition"),
        "{error}"
    );
}

#[test]
fn function_composition_never_infers_unpublished_alias_interfaces() {
    let mut rt = base();
    check(&mut rt, "have abstract_function fn(x R) R", true);
    check(&mut rt, "let untyped_alias=abstract_function", true);
    check(&mut rt, "let bad=square ∘ untyped_alias", false);
    check(
        &mut rt,
        "have typed_alias fn(x R) R=abstract_function",
        true,
    );
    check(&mut rt, "let good=square ∘ typed_alias", true);
    check(&mut rt, "good(0) $in R", true);
    check(&mut rt, "square ∘ gap $in fn(x,y R: x<y) C", true);
    check(&mut rt, "have fn inv(x R:x!=0) R=1/x", true);
    check(
        &mut rt,
        "compose(inv,identity)=compose(inv,identity)",
        false,
    );
    check(&mut rt, "0*compose(inv,identity)(0)=0", false);
}
