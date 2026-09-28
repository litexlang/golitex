//! Resolve an object to a normalized decimal when it is a closed foldable
//! value or has a known_closed_numeric_equal representative.

use crate::ast::obj::{Literal, Number, Obj};
use crate::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::runtime::Runtime;

impl Runtime {
    // Prefer closed-numeric fold (covers `(-1)` / Neg); else known equal rep.
    // Example: after `have a R = 3`, resolve `a` to `"3"`.
    pub(crate) fn resolve_obj_to_normalized_number(&self, obj: &Obj) -> Option<String> {
        if let Some(n) = evaluate_obj_to_normalized_decimal_number(obj) {
            return Some(n.normalized_value);
        }
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_closed_numeric_equal.get(&obj.ir()) {
                if let Some((rep, _)) = entries.first() {
                    if let Some(n) = evaluate_obj_to_normalized_decimal_number(rep) {
                        return Some(n.normalized_value);
                    }
                    if let Obj::Literal(Literal::Number(Number { normalized_value })) = rep {
                        return Some(normalized_value.clone());
                    }
                }
            }
        }
        None
    }
}
