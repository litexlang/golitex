use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferEqualFactTupleCoordinatesResult {
    pub source_fact_id: FactId,
    /// The literal tuple is on the source equality's left side.
    pub reversed: bool,
    /// Direct coordinate equalities in the tuple's original order.
    pub coordinates: Vec<StoreInferredFactResult>,
}
