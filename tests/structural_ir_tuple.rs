use litex::ast::obj::{ArithmeticOperator, Literal, Number, Obj, Pow};
use litex::ast::stmt::{CommandStmt, Stmt};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;
use litex::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn object(source: &str) -> Obj {
    let mut rt = runtime();
    let blocks = Tokenizer::new()
        .tokenize(&format!("eval {source}"), rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&blocks).unwrap();
    let Stmt::Command(CommandStmt::EvalStmt(stmt)) = statements.remove(0) else {
        panic!("eval expected")
    };
    stmt.obj_to_eval
}
fn accepted(rt: &mut Runtime, source: &str) {
    let result = rt.run_litex_code(source).unwrap();
    assert!(
        result.success && result.session_error.is_none(),
        "rejected {source}: {:?}",
        result.session_error
    );
}
fn rejected(rt: &mut Runtime, source: &str) {
    let result = rt.run_litex_code(source).unwrap();
    assert!(
        !result.success && result.session_error.is_none(),
        "unexpected result for {source}: {:?}",
        result.session_error
    );
}

#[test]
fn arithmetic_ir_preserves_every_binary_nesting_and_roundtrips() {
    // All mixed operator pairs on both sides, including equal precedence.
    for outer in ["+", "-", "*", "/", "%", "^"] {
        for inner in ["+", "-", "*", "/", "%", "^"] {
            let left = object(&format!("(2 {inner} 3) {outer} 4"));
            let right = object(&format!("2 {outer} (3 {inner} 4)"));
            assert_ne!(left.ir(), right.ir(), "{inner}, {outer}");
            for obj in [left, right] {
                assert_eq!(obj, object(&obj.ir().to_string()), "{}", obj.ir());
            }
        }
    }
    for source in [
        "(-2)^2", "-(2^2)", "-(-2)", "2^(-3)", "(1,)", "tuple()", "((1,),)",
    ] {
        let obj = object(source);
        assert_eq!(obj, object(&obj.ir().to_string()), "{source}");
    }
    assert_ne!(object("(-2)^2").ir(), object("-(2^2)").ir());
}

#[test]
fn generated_negative_literals_keep_their_sign_under_powers() {
    let negative = Obj::Literal(Literal::Number(Number::new("-2".into())));
    assert_eq!(negative.ir(), object("-2").ir());
    let power = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(negative),
        exponent: Box::new(object("2")),
    }));
    assert_eq!(power.ir(), object("(-2)^2").ir());
    assert_eq!(object(power.ir().as_str()).ir(), power.ir());
    assert_ne!(power.ir(), object("-(2^2)").ir());
    accepted(&mut runtime(), &format!("{} = 4", power.ir()));
}

#[test]
fn false_equalities_cannot_enter_identity_or_equivalence_classes() {
    let mut rt = runtime();
    for source in [
        "(2^3)^2 = 2^(3^2)",
        "(10%7)%4 = 10%(7%4)",
        "(-2)^2 = -(2^2)",
        "8/(4/2)=8/4/2",
    ] {
        rejected(&mut rt, source);
    }
    accepted(&mut rt, "(2^3)^2 = 64\n2^(3^2) = 512");
    rejected(&mut rt, "64 = 512");
    accepted(&mut rt, "have a R = (2^3)^2\nhave b R = 2^(3^2)");
    rejected(&mut rt, "a = b");
    accepted(&mut rt, "a = 64\nb = 512");
    // Closed numeric substitutions must keep the two stored subjects separate.
    accepted(&mut rt, "a + 1 = 65\nb + 1 = 513");
    rejected(&mut rt, "a + 1 = 513");
    rejected(&mut rt, "b + 1 = 65");
}

#[test]
fn arithmetic_ir_keys_separate_predicate_index_and_order_consumers() {
    for (goal, expected) in [
        ("$P((a^b)^2)", true),
        ("(a^b)^2 > 0", true),
        ("$P(a^(b^2))", false),
        ("a^(b^2) > 0", false),
    ] {
        let mut rt = runtime();
        accepted(&mut rt, "abstract_prop P(x)");
        let source = format!(
            "forall a R, b N:\n    $P((a^b)^2)\n    (a^b)^2 > 0\n    =>:\n        {goal}\n"
        );
        let result = rt.run_litex_code(&source).unwrap();
        assert!(result.session_error.is_none(), "{:?}", result.session_error);
        assert_eq!(result.success, expected, "{source}");
    }
}

#[test]
fn forall_equality_index_does_not_follow_colliding_power_views() {
    for (goal, expected) in [("f(0) = (a^b)^2", true), ("f(0) = a^(b^2)", false)] {
        let source = format!("forall a R, b N, f fn(t R) R:\n    forall x R:\n        f(x) = (a^b)^2\n    =>:\n        {goal}\n");
        let result = runtime().run_litex_code(&source).unwrap();
        assert!(result.session_error.is_none(), "{:?}", result.session_error);
        assert_eq!(result.success, expected, "{source}");
    }
}

#[test]
fn tuple_comma_syntax_and_explicit_empty_constructor() {
    assert_eq!(object("(1)"), object("1"));
    assert_eq!(object("(1,)"), object("tuple(1)"));
    assert_eq!(object("(1,2,)"), object("tuple(1,2)"));
    assert_eq!(object("tuple()").ir().to_string(), "tuple()");
    assert_eq!(object("tuple(1)").ir().to_string(), "(1,)");
    assert_ne!(object("(1,)").ir(), object("1").ir());
    let mut rt = runtime();
    accepted(&mut rt, "tuple() = {}\n(1,)(1)=1\n((1,),)(1)(1)=1\n(1)=1");
    for source in ["eval ()", "eval (,)", "eval (1,,)", "eval (1,2,,)"] {
        let run = runtime().run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_some(), "{source}");
    }
    rejected(&mut rt, "(1,) = 1");
}
