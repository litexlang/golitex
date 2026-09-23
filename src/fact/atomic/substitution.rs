//! Capture-aware atomic fact substitution.

use crate::prelude::*;
impl AtomicFact {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        self.replace_bound_identifier_with_runtime(&Runtime::default(), from, to)
    }

    pub fn replace_bound_identifier_with_runtime(
        self,
        runtime: &Runtime,
        from: &str,
        to: &str,
    ) -> Self {
        if from == to {
            return self;
        }
        fn r(runtime: &Runtime, o: Obj, from: &str, to: &str) -> Obj {
            Obj::replace_bound_identifier_with_runtime(o, runtime, from, to)
        }
        match self {
            AtomicFact::NormalAtomicFact(x) => runtime
                .new_normal_atomic_fact(
                    x.predicate,
                    x.body
                        .into_iter()
                        .map(|o| r(runtime, o, from, to))
                        .collect(),
                    x.line_file,
                )
                .into(),
            AtomicFact::EqualFact(x) => runtime
                .new_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::LessFact(x) => runtime
                .new_less_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::GreaterFact(x) => runtime
                .new_greater_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::LessEqualFact(x) => runtime
                .new_less_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::GreaterEqualFact(x) => runtime
                .new_greater_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::IsSetFact(x) => runtime
                .new_is_set_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::IsNonemptySetFact(x) => runtime
                .new_is_nonempty_set_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::IsFiniteSetFact(x) => runtime
                .new_is_finite_set_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::InFact(x) => runtime
                .new_in_fact(
                    r(runtime, x.element, from, to),
                    r(runtime, x.set, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::IsCartFact(x) => runtime
                .new_is_cart_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::IsTupleFact(x) => runtime
                .new_is_tuple_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::SubsetFact(x) => runtime
                .new_subset_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::SupersetFact(x) => runtime
                .new_superset_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotNormalAtomicFact(x) => runtime
                .new_not_normal_atomic_fact(
                    x.predicate,
                    x.body
                        .into_iter()
                        .map(|o| r(runtime, o, from, to))
                        .collect(),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotEqualFact(x) => runtime
                .new_not_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotLessFact(x) => runtime
                .new_not_less_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotGreaterFact(x) => runtime
                .new_not_greater_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotLessEqualFact(x) => runtime
                .new_not_less_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotGreaterEqualFact(x) => runtime
                .new_not_greater_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotIsSetFact(x) => runtime
                .new_not_is_set_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::NotIsNonemptySetFact(x) => runtime
                .new_not_is_nonempty_set_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::NotIsFiniteSetFact(x) => runtime
                .new_not_is_finite_set_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::NotInFact(x) => runtime
                .new_not_in_fact(
                    r(runtime, x.element, from, to),
                    r(runtime, x.set, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotIsCartFact(x) => runtime
                .new_not_is_cart_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::NotIsTupleFact(x) => runtime
                .new_not_is_tuple_fact(r(runtime, x.set, from, to), x.line_file)
                .into(),
            AtomicFact::NotSubsetFact(x) => runtime
                .new_not_subset_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::NotSupersetFact(x) => runtime
                .new_not_superset_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
            AtomicFact::FnEqualFact(x) => runtime
                .new_fn_equal_fact(
                    r(runtime, x.left, from, to),
                    r(runtime, x.right, from, to),
                    x.line_file,
                )
                .into(),
        }
    }
}
