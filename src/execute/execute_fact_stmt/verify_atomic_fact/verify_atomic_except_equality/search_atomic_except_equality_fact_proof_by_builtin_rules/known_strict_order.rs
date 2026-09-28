//! Look up a known strict / weak order fact with the same sides (by Obj IR).

use crate::ast::fact::AtomicFact;
use crate::ast::names::AtomicName;
use crate::ast::obj::Obj;
use crate::parse::keywords::{GREATER, GREATER_EQUAL, LESS};
use crate::runtime::{FactId, Runtime};

impl Runtime {
    // Known `left > right` with matching IR sides.
    pub(crate) fn known_greater_fact_id(&self, left: &Obj, right: &Obj) -> Option<FactId> {
        self.known_order_fact_id(GREATER, true, left, right, |a| match a {
            AtomicFact::GreaterFact(g) => Some((&g.left, &g.right, g.fact_id)),
            _ => None,
        })
    }

    // Known `left < right` with matching IR sides.
    pub(crate) fn known_less_fact_id(&self, left: &Obj, right: &Obj) -> Option<FactId> {
        self.known_order_fact_id(LESS, true, left, right, |a| match a {
            AtomicFact::LessFact(l) => Some((&l.left, &l.right, l.fact_id)),
            _ => None,
        })
    }

    // Known `left >= right` with matching IR sides.
    pub(crate) fn known_greater_equal_fact_id(&self, left: &Obj, right: &Obj) -> Option<FactId> {
        self.known_order_fact_id(GREATER_EQUAL, true, left, right, |a| match a {
            AtomicFact::GreaterEqualFact(g) => Some((&g.left, &g.right, g.fact_id)),
            _ => None,
        })
    }

    fn known_order_fact_id(
        &self,
        prop: &str,
        positive: bool,
        left: &Obj,
        right: &Obj,
        project: impl Fn(&AtomicFact) -> Option<(&Obj, &Obj, FactId)>,
    ) -> Option<FactId> {
        let key = (AtomicName::Plain { name: prop.into() }, positive);
        let left_ir = left.ir();
        let right_ir = right.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let Some((kl, kr, id)) = project(known) {
                    if kl.ir() == left_ir && kr.ir() == right_ir {
                        return Some(id);
                    }
                }
            }
        }
        None
    }
}
