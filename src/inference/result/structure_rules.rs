#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownTupleEqualitySide {
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleEqualityWithKnownTupleImpliesTupleShapeInferRule {
    pub known_side: KnownTupleEqualitySide,
    pub tuple_length: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CartesianMembershipProjectionInferRule {
    pub coordinate_count: usize,
    pub projection: CartesianMembershipProjectionKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CartesianMembershipProjectionKind {
    TupleShape,
    TupleDimension,
    Coordinate { index: usize },
}
