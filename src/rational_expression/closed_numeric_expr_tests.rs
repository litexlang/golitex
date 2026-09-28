use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Div, ExpLogOperator, Factorial, Floor, IntegerOperator,
    Literal, Log, Max, Min, Mod, Mul, Number, Obj, Pow, Sign, Sqrt,
};
use crate::rational_expression::{is_closed_numeric_expr, ClosedNumericExpr};

fn n(s: &str) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: s.to_string(),
    }))
}

#[test]
fn number_and_arithmetic_pow_are_closed() {
    assert!(is_closed_numeric_expr(&n("2")));

    // 2^3/7 + 10 * 2.5
    let pow = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(n("2")),
        exponent: Box::new(n("3")),
    }));
    let frac = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(pow),
        right: Box::new(n("7")),
    }));
    let product = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(n("10")),
        right: Box::new(n("2.5")),
    }));
    let sum = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(frac),
        right: Box::new(product),
    }));
    let view = ClosedNumericExpr::try_from_obj(&sum).expect("closed");
    assert_eq!(view.to_obj().ir(), sum.ir());
}

#[test]
fn abs_min_max_floor_sign_of_numbers_are_closed() {
    let abs = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(n("-3")),
    }));
    assert!(is_closed_numeric_expr(&abs));
    assert_eq!(
        ClosedNumericExpr::try_from_obj(&abs)
            .unwrap()
            .to_obj()
            .ir(),
        abs.ir()
    );

    let min = Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
        left: Box::new(n("1")),
        right: Box::new(n("2")),
    }));
    assert!(is_closed_numeric_expr(&min));

    let max = Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
        left: Box::new(n("1")),
        right: Box::new(n("2")),
    }));
    assert!(is_closed_numeric_expr(&max));

    let floor = Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
        arg: Box::new(n("2.5")),
    }));
    assert!(is_closed_numeric_expr(&floor));

    let sign = Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
        arg: Box::new(n("-2")),
    }));
    assert!(is_closed_numeric_expr(&sign));
}

#[test]
fn unary_neg_of_number_is_closed() {
    use crate::ast::obj::Neg;
    let neg = Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
        arg: Box::new(n("3")),
    }));
    assert!(is_closed_numeric_expr(&neg));
    assert_eq!(
        ClosedNumericExpr::try_from_obj(&neg)
            .unwrap()
            .to_obj()
            .ir(),
        neg.ir()
    );
}

#[test]
fn integer_ops_and_sqrt_log_are_closed_when_domain_ok() {
    let factorial = Obj::IntegerOperator(IntegerOperator::Factorial(Factorial {
        arg: Box::new(n("3")),
    }));
    assert!(is_closed_numeric_expr(&factorial));

    let modulus = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
        left: Box::new(n("-7")),
        right: Box::new(n("3")),
    }));
    assert!(is_closed_numeric_expr(&modulus));

    let bad_mod = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
        left: Box::new(n("2.5")),
        right: Box::new(n("1")),
    }));
    assert!(!is_closed_numeric_expr(&bad_mod));

    let sqrt = Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
        arg: Box::new(n("4")),
    }));
    assert!(is_closed_numeric_expr(&sqrt));

    let log = Obj::ExpLogOperator(ExpLogOperator::Log(Log {
        base: Box::new(n("2")),
        arg: Box::new(n("8")),
    }));
    assert!(is_closed_numeric_expr(&log));
}

#[test]
fn identifier_is_not_closed() {
    use crate::ast::obj::IdentifierObj;
    use crate::runtime::runtime_ids::IdentifierId;

    let ident = Obj::Identifier(IdentifierObj::plain(IdentifierId::new(0), "a".into()));
    assert!(ClosedNumericExpr::try_from_obj(&ident).is_none());
}
