//! Equality from cited tuple structure. Both goal objects have already passed WD.
use super::result::EqualFactSearchedProof;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{Literal, Number, Obj, ProductShape};
use crate::execute::execute_fact_stmt::known_tuple::{
    literal_positive_usize, KnownFunctionTupleValueProof, KnownTupleShapeProof,
    KnownTupleValueProof,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(in crate::execute) fn search_equal_fact_proof_by_known_special_property(
        &mut self,
        fact: &EqualFact,
    ) -> RuntimeResult<Option<EqualFactSearchProofByKnownSpecialProperty>> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if let Obj::ProductShape(ProductShape::TupleDim(dim)) = left {
                if let Some(shape) = self.lookup_known_tuple_shape(dim.arg.as_ref()) {
                    let n = Obj::Literal(Literal::Number(Number {
                        normalized_value: shape.dimension().to_string(),
                    }));
                    if let Some(equal) = self.lookup_known_obj_equality(&n, right) {
                        return Ok(Some(
                            EqualFactSearchProofByKnownSpecialProperty::TupleDimension(
                                TupleDimensionKnownProof {
                                    reversed,
                                    shape,
                                    dimension_equal: Box::new(equal),
                                },
                            ),
                        ));
                    }
                }
            }
            if let Obj::ProductShape(ProductShape::ObjAtIndex(at)) = left {
                let Some(index) = literal_positive_usize(at.index.as_ref()) else {
                    continue;
                };
                for tuple in self.known_literal_tuple_candidates(at.obj.as_ref()) {
                    let Some(component) = tuple.value.args.get(index - 1) else {
                        continue;
                    };
                    let Some(equal) = self.lookup_known_obj_equality(component, right) else {
                        continue;
                    };
                    return Ok(Some(
                        EqualFactSearchProofByKnownSpecialProperty::TupleProjection(
                            TupleProjectionKnownProof {
                                reversed,
                                index,
                                tuple,
                                component_equal: Box::new(equal),
                            },
                        ),
                    ));
                }
                if let Obj::FnObj(app) = at.obj.as_ref() {
                    if let Some(function) = self.lookup_known_function_tuple_value(app) {
                        if let Some(component) = function.value.args.get(index - 1) {
                            if let Some(equal) = self.lookup_known_obj_equality(component, right) {
                                return Ok(Some(
                                    EqualFactSearchProofByKnownSpecialProperty::FnTupleProjection(
                                        FnTupleProjectionKnownProof {
                                            reversed,
                                            index,
                                            function,
                                            component_equal: Box::new(equal),
                                        },
                                    ),
                                ));
                            }
                        }
                    }
                }
            }
            // Eta: a known n-tuple equals its n ordered projections.
            // Example: p in cart(R,R) implies p = (p[1],p[2]).
            let Obj::ProductShape(ProductShape::Tuple(tuple)) = right else {
                continue;
            };
            // Reject other tuple spellings before consulting the environment.
            if !tuple.args.iter().enumerate().all(|(i, item)| {
                matches!(item.as_ref(), Obj::ProductShape(ProductShape::ObjAtIndex(at))
                    if literal_positive_usize(at.index.as_ref()) == Some(i + 1))
            }) {
                continue;
            }
            let Some(shape) = self.lookup_known_tuple_shape(left) else {
                continue;
            };
            if shape.dimension() != tuple.args.len() {
                continue;
            }
            let mut subjects = Vec::new();
            for item in &tuple.args {
                let Obj::ProductShape(ProductShape::ObjAtIndex(at)) = item.as_ref() else {
                    unreachable!()
                };
                let Some(equal) = self.lookup_known_obj_equality(at.obj.as_ref(), left) else {
                    break;
                };
                subjects.push(equal);
            }
            if subjects.len() == tuple.args.len() {
                return Ok(Some(
                    EqualFactSearchProofByKnownSpecialProperty::TupleReconstruction(
                        TupleReconstructionKnownProof {
                            reversed,
                            shape,
                            subjects,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }
}

pub enum EqualFactSearchProofByKnownSpecialProperty {
    TupleReconstruction(TupleReconstructionKnownProof),
    TupleProjection(TupleProjectionKnownProof),
    FnTupleProjection(FnTupleProjectionKnownProof),
    TupleDimension(TupleDimensionKnownProof),
}

pub struct TupleReconstructionKnownProof {
    pub reversed: bool,
    pub shape: KnownTupleShapeProof,
    pub subjects: Vec<EqualFactSearchedProof>,
}

pub struct TupleProjectionKnownProof {
    pub reversed: bool,
    pub index: usize,
    pub tuple: KnownTupleValueProof,
    pub component_equal: Box<EqualFactSearchedProof>,
}

pub struct FnTupleProjectionKnownProof {
    pub reversed: bool,
    pub index: usize,
    pub function: KnownFunctionTupleValueProof,
    pub component_equal: Box<EqualFactSearchedProof>,
}

pub struct TupleDimensionKnownProof {
    pub reversed: bool,
    pub shape: KnownTupleShapeProof,
    pub dimension_equal: Box<EqualFactSearchedProof>,
}
