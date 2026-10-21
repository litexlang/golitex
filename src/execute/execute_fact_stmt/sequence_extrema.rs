//! Finite sequence extremal candidates: an eventual bound AND hits on every tail.
use super::function_limit::{function_limit_exists, function_limit_forall};
use super::sequence_limit::{identifier, real, typed};
use crate::ast::names::BoundName;
use crate::ast::param::*;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, sub_objs};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SequenceExtremum {
    Upper,
    Lower,
}
pub(crate) struct SequenceExtremaClauses {
    pub eventual_bound: Fact,
    pub tail_hits: Fact,
}
impl Runtime {
    pub(crate) fn sequence_extrema_clauses(
        &mut self,
        a: Obj,
        l: Obj,
        kind: SequenceExtremum,
    ) -> SequenceExtremaClauses {
        let epsilon = self.fresh_internal_param();
        let cutoff = self.fresh_internal_param();
        let inclusion = self.sequence_extrema_bound(
            a.clone(),
            l.clone(),
            kind,
            identifier(&epsilon),
            identifier(&cutoff),
        );
        let exists = function_limit_exists(self, cutoff, nat_pos(), vec![inclusion]);
        let eventual_bound =
            function_limit_forall(self, epsilon, positive_real(), vec![], vec![exists]);
        let epsilon = self.fresh_internal_param();
        let cutoff = self.fresh_internal_param();
        let hits = self.sequence_extrema_hit(a, l, kind, identifier(&epsilon), identifier(&cutoff));
        let tail_hits = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![group(epsilon, positive_real()), group(cutoff, nat_pos())],
            },
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(hits)],
            line_file: None,
        });
        SequenceExtremaClauses {
            eventual_bound,
            tail_hits,
        }
    }
    pub(crate) fn sequence_extrema_bound(
        &mut self,
        a: Obj,
        l: Obj,
        kind: SequenceExtremum,
        epsilon: Obj,
        cutoff: Obj,
    ) -> AtomicFact {
        let n = self.fresh_internal_param();
        let v = self.fresh_internal_param();
        let guard = ge(self, identifier(&n), cutoff);
        let tail = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: n,
            param_set: Box::new(nat_pos()),
            facts: vec![QuantifierFreeFact::AtomicFact(guard)],
        }));
        let bound = match kind {
            SequenceExtremum::Upper => less(self, identifier(&v), add_objs(l, epsilon)),
            SequenceExtremum::Lower => less(self, sub_objs(l, epsilon), identifier(&v)),
        };
        let ray = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
            param_binding: v,
            param_set: Box::new(real()),
            facts: vec![QuantifierFreeFact::AtomicFact(bound)],
        }));
        SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: tail,
            right: PreimageSet::new(a, ray).into(),
            line_file: None,
        }
        .into()
    }
    pub(crate) fn sequence_extrema_hit(
        &mut self,
        a: Obj,
        l: Obj,
        kind: SequenceExtremum,
        epsilon: Obj,
        cutoff: Obj,
    ) -> PlainExistFact {
        let n = self.fresh_internal_param();
        let index = identifier(&n);
        let after = ge(self, index.clone(), cutoff);
        let value = super::function_domain::function_application(&a, vec![Box::new(index)])
            .expect("unary sequence call");
        let hit = match kind {
            SequenceExtremum::Upper => less(self, sub_objs(l, epsilon), value),
            SequenceExtremum::Lower => less(self, value, add_objs(l, epsilon)),
        };
        PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed(n, nat_pos()),
            facts: vec![QuantifierFreeFact::AndFact(AndFact {
                fact_id: self.global_ids.allocate_fact_id(),
                facts: vec![after, hit],
                line_file: None,
            })],
            line_file: None,
        }
    }
}
fn nat_pos() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
fn positive_real() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
fn group(name: BoundName, set: Obj) -> TypedParameterGroup {
    TypedParameterGroup {
        params: vec![name],
        param_type: ParamType::Obj(set),
    }
}
fn ge(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    GreaterEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
fn less(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/sequence_extrema/tests.rs"]
mod sequence_extrema_tests;
