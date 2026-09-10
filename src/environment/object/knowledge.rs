//! Reusable facets known about one Environment object equality key.

use crate::prelude::*;

/// All reusable information known about one object equality key.
#[derive(Clone, Default)]
pub struct SpecialObjectPropertyMemory {
    pub tuple_equality: Option<(Option<Tuple>, Option<Cart>, LineFile)>,
    pub cart_equality: Option<(Cart, LineFile)>,
    pub finite_sequence_list_equality: Option<(FiniteSeqListObj, Option<FiniteSeqSet>, LineFile)>,
    pub matrix_list_equality: Option<(MatrixListObj, Option<MatrixSet>, LineFile)>,
    pub matrix_set_membership: Option<(MatrixSet, LineFile)>,
    pub simplified_value: Option<KnownObjValue>,
    pub set_builder_equality: Option<(SetBuilder, LineFile)>,
    pub function_set: Option<KnownFnInfo>,
}
