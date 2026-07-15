use crate::prelude::*;

impl AtomicFact {
    pub fn args(&self) -> Vec<Obj> {
        match self {
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => normal_atomic_fact.body.clone(),
            AtomicFact::EqualFact(equal_fact) => {
                vec![equal_fact.left.clone(), equal_fact.right.clone()]
            }
            AtomicFact::LessFact(less_fact) => {
                vec![less_fact.left.clone(), less_fact.right.clone()]
            }
            AtomicFact::GreaterFact(greater_fact) => {
                vec![greater_fact.left.clone(), greater_fact.right.clone()]
            }
            AtomicFact::LessEqualFact(less_equal_fact) => {
                vec![less_equal_fact.left.clone(), less_equal_fact.right.clone()]
            }
            AtomicFact::GreaterEqualFact(greater_equal_fact) => vec![
                greater_equal_fact.left.clone(),
                greater_equal_fact.right.clone(),
            ],
            AtomicFact::IsSetFact(is_set_fact) => vec![is_set_fact.set.clone()],
            AtomicFact::IsNonemptySetFact(is_nonempty_set_fact) => {
                vec![is_nonempty_set_fact.set.clone()]
            }
            AtomicFact::IsFiniteSetFact(is_finite_set_fact) => vec![is_finite_set_fact.set.clone()],
            AtomicFact::InFact(in_fact) => vec![in_fact.element.clone(), in_fact.set.clone()],
            AtomicFact::IsCartFact(is_cart_fact) => vec![is_cart_fact.set.clone()],
            AtomicFact::IsTupleFact(is_tuple_fact) => vec![is_tuple_fact.set.clone()],
            AtomicFact::SubsetFact(subset_fact) => {
                vec![subset_fact.left.clone(), subset_fact.right.clone()]
            }
            AtomicFact::SupersetFact(superset_fact) => {
                vec![superset_fact.left.clone(), superset_fact.right.clone()]
            }
            AtomicFact::NotNormalAtomicFact(not_normal_atomic_fact) => {
                not_normal_atomic_fact.body.clone()
            }
            AtomicFact::NotEqualFact(not_equal_fact) => {
                vec![not_equal_fact.left.clone(), not_equal_fact.right.clone()]
            }
            AtomicFact::NotLessFact(not_less_fact) => {
                vec![not_less_fact.left.clone(), not_less_fact.right.clone()]
            }
            AtomicFact::NotGreaterFact(not_greater_fact) => vec![
                not_greater_fact.left.clone(),
                not_greater_fact.right.clone(),
            ],
            AtomicFact::NotLessEqualFact(not_less_equal_fact) => vec![
                not_less_equal_fact.left.clone(),
                not_less_equal_fact.right.clone(),
            ],
            AtomicFact::NotGreaterEqualFact(not_greater_equal_fact) => vec![
                not_greater_equal_fact.left.clone(),
                not_greater_equal_fact.right.clone(),
            ],
            AtomicFact::NotIsSetFact(not_is_set_fact) => vec![not_is_set_fact.set.clone()],
            AtomicFact::NotIsNonemptySetFact(not_is_nonempty_set_fact) => {
                vec![not_is_nonempty_set_fact.set.clone()]
            }
            AtomicFact::NotIsFiniteSetFact(not_is_finite_set_fact) => {
                vec![not_is_finite_set_fact.set.clone()]
            }
            AtomicFact::NotInFact(not_in_fact) => {
                vec![not_in_fact.element.clone(), not_in_fact.set.clone()]
            }
            AtomicFact::NotIsCartFact(not_is_cart_fact) => vec![not_is_cart_fact.set.clone()],
            AtomicFact::NotIsTupleFact(not_is_tuple_fact) => vec![not_is_tuple_fact.set.clone()],
            AtomicFact::NotSubsetFact(not_subset_fact) => {
                vec![not_subset_fact.left.clone(), not_subset_fact.right.clone()]
            }
            AtomicFact::NotSupersetFact(not_superset_fact) => vec![
                not_superset_fact.left.clone(),
                not_superset_fact.right.clone(),
            ],
            AtomicFact::FnEqualInFact(f) => {
                vec![f.left.clone(), f.right.clone(), f.set.clone()]
            }
            AtomicFact::FnEqualFact(f) => vec![f.left.clone(), f.right.clone()],
        }
    }

    pub fn args_ref(&self) -> Vec<&Obj> {
        match self {
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                normal_atomic_fact.body.iter().collect()
            }
            AtomicFact::EqualFact(equal_fact) => vec![&equal_fact.left, &equal_fact.right],
            AtomicFact::LessFact(less_fact) => vec![&less_fact.left, &less_fact.right],
            AtomicFact::GreaterFact(greater_fact) => {
                vec![&greater_fact.left, &greater_fact.right]
            }
            AtomicFact::LessEqualFact(less_equal_fact) => {
                vec![&less_equal_fact.left, &less_equal_fact.right]
            }
            AtomicFact::GreaterEqualFact(greater_equal_fact) => {
                vec![&greater_equal_fact.left, &greater_equal_fact.right]
            }
            AtomicFact::IsSetFact(is_set_fact) => vec![&is_set_fact.set],
            AtomicFact::IsNonemptySetFact(is_nonempty_set_fact) => {
                vec![&is_nonempty_set_fact.set]
            }
            AtomicFact::IsFiniteSetFact(is_finite_set_fact) => vec![&is_finite_set_fact.set],
            AtomicFact::InFact(in_fact) => vec![&in_fact.element, &in_fact.set],
            AtomicFact::IsCartFact(is_cart_fact) => vec![&is_cart_fact.set],
            AtomicFact::IsTupleFact(is_tuple_fact) => vec![&is_tuple_fact.set],
            AtomicFact::SubsetFact(subset_fact) => vec![&subset_fact.left, &subset_fact.right],
            AtomicFact::SupersetFact(superset_fact) => {
                vec![&superset_fact.left, &superset_fact.right]
            }
            AtomicFact::NotNormalAtomicFact(not_normal_atomic_fact) => {
                not_normal_atomic_fact.body.iter().collect()
            }
            AtomicFact::NotEqualFact(not_equal_fact) => {
                vec![&not_equal_fact.left, &not_equal_fact.right]
            }
            AtomicFact::NotLessFact(not_less_fact) => {
                vec![&not_less_fact.left, &not_less_fact.right]
            }
            AtomicFact::NotGreaterFact(not_greater_fact) => {
                vec![&not_greater_fact.left, &not_greater_fact.right]
            }
            AtomicFact::NotLessEqualFact(not_less_equal_fact) => {
                vec![&not_less_equal_fact.left, &not_less_equal_fact.right]
            }
            AtomicFact::NotGreaterEqualFact(not_greater_equal_fact) => {
                vec![&not_greater_equal_fact.left, &not_greater_equal_fact.right]
            }
            AtomicFact::NotIsSetFact(not_is_set_fact) => vec![&not_is_set_fact.set],
            AtomicFact::NotIsNonemptySetFact(not_is_nonempty_set_fact) => {
                vec![&not_is_nonempty_set_fact.set]
            }
            AtomicFact::NotIsFiniteSetFact(not_is_finite_set_fact) => {
                vec![&not_is_finite_set_fact.set]
            }
            AtomicFact::NotInFact(not_in_fact) => vec![&not_in_fact.element, &not_in_fact.set],
            AtomicFact::NotIsCartFact(not_is_cart_fact) => vec![&not_is_cart_fact.set],
            AtomicFact::NotIsTupleFact(not_is_tuple_fact) => vec![&not_is_tuple_fact.set],
            AtomicFact::NotSubsetFact(not_subset_fact) => {
                vec![&not_subset_fact.left, &not_subset_fact.right]
            }
            AtomicFact::NotSupersetFact(not_superset_fact) => {
                vec![&not_superset_fact.left, &not_superset_fact.right]
            }
            AtomicFact::FnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
            AtomicFact::FnEqualFact(f) => vec![&f.left, &f.right],
        }
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        self.args()
    }

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        self.args_ref()
    }
}
