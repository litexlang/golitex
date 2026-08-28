//! Set relation and finite-set builtin rules.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetRelationDualityBuiltinRule {
    SubsetFromSuperset,
    SupersetFromSubset,
    NotSubsetFromNotSuperset,
    NotSupersetFromNotSubset,
}

impl SetRelationDualityBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::SubsetFromSuperset => "set.subset_from_superset",
            Self::SupersetFromSubset => "set.superset_from_subset",
            Self::NotSubsetFromNotSuperset => "set.not_subset_from_not_superset",
            Self::NotSupersetFromNotSubset => "set.not_superset_from_not_subset",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetBuiltinRule {
    EmptySubset,
    SubsetReflexivity,
    SupersetReflexivity,
    SubsetTransitivity,
    SubsetUnionLeft,
    SubsetUnionRight,
    UnionCommutative,
    UnionAssociative,
    UnionIdempotent,
    UnionEmptyLeft,
    UnionEmptyRight,
    UnionSetMinusDecomposition,
    UnionEqRightOfSubset,
    UnionFinite,
    UnionNonemptyLeft,
    UnionNonemptyRight,
    UnionSubset,
    IntersectCommutative,
    IntersectAssociative,
    IntersectIdempotent,
    IntersectEqLeftOfSubset,
    IntersectEqRightOfSubset,
    IntersectFinite,
    IntersectSubsetLeft,
    IntersectSubsetRight,
    IntersectUnionDistributive,
    IntersectSetMinusSelfEmpty,
    IntersectSetMinusDisjointFromSubset,
    PowerSetFinite,
    PowerSetMembershipOfSubset,
    PowerSetNonempty,
    SetMinusSelfEmpty,
    SetMinusEmptyRight,
    SetMinusEmptyLeft,
    SetMinusFiniteLeft,
    SetMinusInfiniteOfInfiniteFinite,
    SetMinusIntersectDeMorgan,
    SetMinusIntersectSelf,
    SetMinusRecoverSubset,
    SetMinusSubsetLeft,
    SetMinusUnionDeMorgan,
    SubsetEqSetMinusRecovery,
    UnionMembershipLeft,
    UnionMembershipRight,
    IntersectMembershipBoth,
    IntersectNonMembershipLeft,
    IntersectNonMembershipRight,
    SetMinusMembership,
}

impl SetBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::EmptySubset => "set.empty_subset",
            Self::SubsetReflexivity => "set.subset_reflexivity",
            Self::SupersetReflexivity => "set.superset_reflexivity",
            Self::SubsetTransitivity => "set.subset_transitivity",
            Self::SubsetUnionLeft => "set.subset_union_left",
            Self::SubsetUnionRight => "set.subset_union_right",
            Self::UnionCommutative => "set.union_commutative",
            Self::UnionAssociative => "set.union_associative",
            Self::UnionIdempotent => "set.union_idempotent",
            Self::UnionEmptyLeft => "set.union_empty_left",
            Self::UnionEmptyRight => "set.union_empty_right",
            Self::UnionSetMinusDecomposition => "set.union_set_minus_decomposition",
            Self::UnionEqRightOfSubset => "set.union_eq_right_of_subset",
            Self::UnionFinite => "set.union_finite",
            Self::UnionNonemptyLeft => "set.union_nonempty_left",
            Self::UnionNonemptyRight => "set.union_nonempty_right",
            Self::UnionSubset => "set.union_subset",
            Self::IntersectCommutative => "set.intersect_commutative",
            Self::IntersectAssociative => "set.intersect_associative",
            Self::IntersectIdempotent => "set.intersect_idempotent",
            Self::IntersectEqLeftOfSubset => "set.intersect_eq_left_of_subset",
            Self::IntersectEqRightOfSubset => "set.intersect_eq_right_of_subset",
            Self::IntersectFinite => "set.intersect_finite",
            Self::IntersectSubsetLeft => "set.intersect_subset_left",
            Self::IntersectSubsetRight => "set.intersect_subset_right",
            Self::IntersectUnionDistributive => "set.intersect_union_distributive",
            Self::IntersectSetMinusSelfEmpty => "set.intersect_set_minus_self_empty",
            Self::IntersectSetMinusDisjointFromSubset => "set.intersect_set_minus_of_subset_empty",
            Self::PowerSetFinite => "set.power_set_finite",
            Self::PowerSetMembershipOfSubset => "set.power_set_membership_of_subset",
            Self::PowerSetNonempty => "set.power_set_nonempty",
            Self::SetMinusSelfEmpty => "set.set_minus_self_empty",
            Self::SetMinusEmptyRight => "set.set_minus_empty_right",
            Self::SetMinusEmptyLeft => "set.set_minus_empty_left",
            Self::SetMinusFiniteLeft => "set.set_minus_finite_left",
            Self::SetMinusInfiniteOfInfiniteFinite => "set.set_minus_infinite_of_infinite_finite",
            Self::SetMinusIntersectDeMorgan => "set.set_minus_intersect_de_morgan",
            Self::SetMinusIntersectSelf => "set.set_minus_intersect_self",
            Self::SetMinusRecoverSubset => "set.set_minus_recover_subset",
            Self::SetMinusSubsetLeft => "set.set_minus_subset_left",
            Self::SetMinusUnionDeMorgan => "set.set_minus_union_de_morgan",
            Self::SubsetEqSetMinusRecovery => "set.subset_eq_set_minus_recovery",
            Self::UnionMembershipLeft => "set.union_membership_left",
            Self::UnionMembershipRight => "set.union_membership_right",
            Self::IntersectMembershipBoth => "set.intersect_membership",
            Self::IntersectNonMembershipLeft => "set.intersect_nonmembership_left",
            Self::IntersectNonMembershipRight => "set.intersect_nonmembership_right",
            Self::SetMinusMembership => "set.set_minus_membership",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteSetBuiltinRule {
    ListSet,
    Range,
    ClosedRange,
}

impl FiniteSetBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::ListSet => "set.finite.literal",
            Self::Range => "set.finite.range",
            Self::ClosedRange => "set.finite.closed_range",
        }
    }
}
