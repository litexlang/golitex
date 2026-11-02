use crate::prelude::*;
use crate::store_fact_and_infer::InferEqualFactTupleCoordinatesResult;

impl Runtime {
    // A stored equality to a literal tuple certifies its complete finite domain.
    // Publish one layer only: x = (a,b) gives x(1) = a and x(2) = b.
    pub(super) fn infer_equal_fact_tuple_coordinates(
        &mut self,
        source: &EqualFact,
    ) -> RuntimeResult<Option<InferEqualFactTupleCoordinatesResult>> {
        let (subject, tuple, reversed) = match (&source.left, &source.right) {
            (subject, Obj::ProductShape(ProductShape::Tuple(tuple))) => (subject, tuple, false),
            (Obj::ProductShape(ProductShape::Tuple(tuple)), subject) => (subject, tuple, true),
            _ => return Ok(None),
        };
        let mut equalities = Vec::new();
        for (index, value) in tuple.args.iter().enumerate() {
            let Ok(coordinate) =
                crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate(
                    subject, index,
                )
            else {
                return Ok(None);
            };
            let equality: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: coordinate,
                right: value.as_ref().clone(),
                line_file: source.line_file.clone(),
            }
            .into();
            equalities.push(equality);
        }
        let mut coordinates = Vec::new();
        for equality in equalities {
            coordinates.push(self.store_inferred_fact(&equality)?);
        }
        Ok(Some(InferEqualFactTupleCoordinatesResult {
            source_fact_id: source.fact_id,
            reversed,
            coordinates,
        }))
    }
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/tuple_coordinate_inference/tests.rs"]
mod tests;
