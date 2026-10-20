use super::{
    InferInFactCartCoordinatesResult, InferInFactClosedRangeResult,
    InferInFactEqualFnSetExpandResult, InferInFactFamilyUnionResult,
    InferInFactFiniteSeqExpandResult, InferInFactFnRangeResult, InferInFactIndexCartResult,
    InferInFactIndexIntersectResult, InferInFactIndexUnionResult, InferInFactIntersectBothResult,
    InferInFactListSetOrEqualitiesResult, InferInFactListSetSingletonEqualResult,
    InferInFactOneSideRealIntervalResult, InferInFactPreimageResult, InferInFactPreimageSetResult,
    InferInFactRangeResult, InferInFactRealIntervalResult, InferInFactSeqExpandResult,
    InferInFactSetMinusSplitResult, InferInFactSignedStandardSetSignResult,
    InferInFactUnionOrResult, InferPowerSetMembershipProjectionResult,
    InferSetBuilderMembershipProjectionResult,
};
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferInFactResult {
    Template(super::InferTemplateMembershipResult),
    SetBuilder(InferSetBuilderMembershipProjectionResult),
    Preimage(InferInFactPreimageResult),
    PreimageSet(InferInFactPreimageSetResult),
    PowerSet(InferPowerSetMembershipProjectionResult),
    ListSetSingletonEqual(InferInFactListSetSingletonEqualResult),
    ListSetOrEqualities(InferInFactListSetOrEqualitiesResult),
    UnionOr(InferInFactUnionOrResult),
    IntersectBoth(InferInFactIntersectBothResult),
    SetMinusSplit(InferInFactSetMinusSplitResult),
    CartCoordinates(InferInFactCartCoordinatesResult),
    Range(InferInFactRangeResult),
    ClosedRange(InferInFactClosedRangeResult),
    RealInterval(InferInFactRealIntervalResult),
    OneSideRealInterval(InferInFactOneSideRealIntervalResult),
    SignedStandardSetSign(InferInFactSignedStandardSetSignResult),
    EqualFnSetExpand(InferInFactEqualFnSetExpandResult),
    FnRange(InferInFactFnRangeResult),
    FiniteSeqExpand(InferInFactFiniteSeqExpandResult),
    SeqExpand(InferInFactSeqExpandResult),
    FamilyUnion(InferInFactFamilyUnionResult),
    IndexUnion(InferInFactIndexUnionResult),
    IndexIntersect(InferInFactIndexIntersectResult),
    IndexCart(InferInFactIndexCartResult),
}

impl InferInFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::Template(p) => p
                .stores
                .iter()
                .chain(p.native_rules.iter().flat_map(|r| r.stored_conclusions()))
                .collect(),
            Self::SetBuilder(p) => p
                .steps
                .iter()
                .flat_map(|s| s.stored_conclusions())
                .collect(),
            Self::Preimage(p) => p.derived.iter().collect(),
            Self::PreimageSet(p) => p.derived.iter().collect(),
            Self::PowerSet(p) => vec![p.derived.as_ref()],
            Self::ListSetSingletonEqual(p) => vec![p.derived.as_ref()],
            Self::ListSetOrEqualities(p) => vec![p.derived.as_ref()],
            Self::UnionOr(p) => vec![p.derived.as_ref()],
            Self::IntersectBoth(p) => vec![&p.left_membership, &p.right_membership],
            Self::SetMinusSplit(p) => [&p.base_membership, &p.excluded_membership]
                .into_iter()
                .chain(p.singleton_inequality.iter())
                .collect(),
            Self::CartCoordinates(p) => p.coordinates.iter().map(|c| &c.membership).collect(),
            Self::Range(p) => p.bounds.stored_conclusions(),
            Self::ClosedRange(p) => p.bounds.stored_conclusions(),
            Self::RealInterval(p) => vec![&p.real_membership, &p.lower_bound, &p.upper_bound],
            Self::OneSideRealInterval(p) => vec![&p.real_membership, &p.bound],
            Self::SignedStandardSetSign(p) => p.derived.iter().collect(),
            Self::EqualFnSetExpand(p) => p.transports.iter().map(|s| &s.derived).collect(),
            Self::FnRange(p) => std::iter::once(&p.codomain_membership)
                .chain(p.preimage_witness.iter())
                .collect(),
            Self::FiniteSeqExpand(p) => vec![p.derived.as_ref()],
            Self::SeqExpand(p) => vec![p.derived.as_ref()],
            Self::FamilyUnion(p) => vec![p.derived.as_ref()],
            Self::IndexUnion(p) => std::iter::once(&p.ambient_membership)
                .chain(p.fiber_witness.iter())
                .collect(),
            Self::IndexIntersect(p) => std::iter::once(&p.ambient_membership)
                .chain(p.fiber_membership.iter())
                .collect(),
            Self::IndexCart(p) => vec![&p.function_membership, &p.choice_certificate],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
