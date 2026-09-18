//! Syntactic closed numeric expressions (v1).
//!
//! A closed numeric expr is built only from decimal `Number` leaves and
//! Add / Sub / Mul / Div / Pow. No identifiers, function calls, or other ops.
//!
//! Example that is closed: `2^3/7 + 10 * 2.5`
//! Example that is not: `a + 1`, `abs(1)`, `1 % 2`

use crate::new_pipeline::ast::obj::Obj;

pub fn is_closed_numeric_expr(obj: &Obj) -> bool {
    match obj {
        Obj::Number(_) => true,
        Obj::Add(add) => {
            is_closed_numeric_expr(&add.left) && is_closed_numeric_expr(&add.right)
        }
        Obj::Sub(sub) => {
            is_closed_numeric_expr(&sub.left) && is_closed_numeric_expr(&sub.right)
        }
        Obj::Mul(mul) => {
            is_closed_numeric_expr(&mul.left) && is_closed_numeric_expr(&mul.right)
        }
        Obj::Div(div) => {
            is_closed_numeric_expr(&div.left) && is_closed_numeric_expr(&div.right)
        }
        Obj::Pow(pow) => {
            is_closed_numeric_expr(&pow.base) && is_closed_numeric_expr(&pow.exponent)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::is_closed_numeric_expr;
    use crate::new_pipeline::ast::obj::{Add, Div, Mul, Number, Obj, Pow};

    fn n(s: &str) -> Obj {
        Obj::Number(Number {
            normalized_value: s.to_string(),
        })
    }

    #[test]
    fn number_and_arithmetic_pow_are_closed() {
        assert!(is_closed_numeric_expr(&n("2")));

        // 2^3/7 + 10 * 2.5
        let pow = Obj::Pow(Pow {
            base: Box::new(n("2")),
            exponent: Box::new(n("3")),
        });
        let frac = Obj::Div(Div {
            left: Box::new(pow),
            right: Box::new(n("7")),
        });
        let product = Obj::Mul(Mul {
            left: Box::new(n("10")),
            right: Box::new(n("2.5")),
        });
        let sum = Obj::Add(Add {
            left: Box::new(frac),
            right: Box::new(product),
        });
        assert!(is_closed_numeric_expr(&sum));
    }

    #[test]
    fn identifier_and_abs_are_not_closed() {
        use crate::new_pipeline::ast::obj::{Abs, IdentifierObj};
        use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

        let ident = Obj::Identifier(IdentifierObj::plain(IdentifierId::new(0), "a".into()));
        assert!(!is_closed_numeric_expr(&ident));

        let abs = Obj::Abs(Abs {
            arg: Box::new(n("1")),
        });
        assert!(!is_closed_numeric_expr(&abs));
    }
}
