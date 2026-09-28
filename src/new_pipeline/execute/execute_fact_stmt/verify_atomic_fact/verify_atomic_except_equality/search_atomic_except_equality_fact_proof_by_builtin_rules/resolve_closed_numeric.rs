//! Resolve an object to a normalized decimal when it is a literal number
//! or has a known_closed_numeric_equal representative.

use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
use crate::new_pipeline::runtime::Runtime;

impl Runtime {
    // Prefer a literal number; otherwise the first closed-numeric equal rep.
    // Example: after `have a R = 3`, resolve `a` to `"3"`.
    pub(crate) fn resolve_obj_to_normalized_number(&self, obj: &Obj) -> Option<String> {
        if let Obj::Literal(Literal::Number(Number { normalized_value })) = obj {
            return Some(normalized_value.clone());
        }
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_closed_numeric_equal.get(&obj.ir()) {
                if let Some((rep, _)) = entries.first() {
                    if let Obj::Literal(Literal::Number(Number { normalized_value })) = rep {
                        return Some(normalized_value.clone());
                    }
                }
            }
        }
        None
    }
}
