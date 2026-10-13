use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferCartCoordinateResult {
    /// Zero-based index in the original Cartesian product factors.
    pub coordinate_index: usize,
    pub membership: StoreInferredFactResult,
}
