use crate::prelude::*;

/// `A $subset B` introduces the reusable local theorem
/// `forall x A: x $in B`. The generated binder identity is retained because
/// it occurs recursively in the conclusion and must not be reconstructed by
/// a compiler from the binder's display name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubsetImpliesElementwiseMembershipForallInferRule {
    pub binder_symbol_id: SymbolId,
}

/// `A $superset B` introduces the reusable local theorem
/// `forall x B: x $in A` with the same exact-binder identity contract as the
/// subset direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupersetImpliesElementwiseMembershipForallInferRule {
    pub binder_symbol_id: SymbolId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownSetEqualityOrientation {
    SourceSetOnLeft,
    SourceSetOnRight,
}

/// The premise list is ordered as source membership followed by the exact
/// previously stored equality between the source and target sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule {
    pub equality_orientation: KnownSetEqualityOrientation,
}

/// `x $in {a_1, ..., a_n}` exposes exactly the ordered alternatives
/// `x = a_1 or ... or x = a_n`. For a singleton the conclusion is the one
/// equality itself. The source list remains in the premise Fact; this field
/// freezes the arity so consumers reject a truncated or extended conclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListSetMembershipImpliesEqualityAlternativesInferRule {
    pub element_count: usize,
}
