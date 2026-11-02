use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_composed_structure::CartesianCoordinateEqualityProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_cartesian_coordinate_strategy(
        &self,
        goal: &EqualFact,
        proof: &CartesianCoordinateEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let n = proof.left_shape.dimension();
        if proof.right_shape.dimension() != n {
            return Err(LeanCompileError::unsupported(
                "CartesianCoordinateEquality/Dimension",
            ));
        }
        if proof.requirement_facts.len() != n || proof.proof_of_requirement_facts.len() != n {
            return Err(LeanCompileError::unsupported(
                "CartesianCoordinateEquality/Requirements",
            ));
        }
        let left = self.compile_object_reference(&goal.left, position)?;
        let right = self.compile_object_reference(&goal.right, position)?;
        let (left_cart, left_member) =
            self.compile_cart_shape_member(&goal.left, &proof.left_shape, position)?;
        let (right_cart, right_member) =
            self.compile_cart_shape_member(&goal.right, &proof.right_shape, position)?;
        let children = &proof.proof_of_requirement_facts;
        let mut coordinates = Vec::with_capacity(n);
        for (index, (requirement, child)) in
            proof.requirement_facts.iter().zip(children).enumerate()
        {
            let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = requirement else {
                return Err(LeanCompileError::unsupported(
                    "CartesianCoordinateEquality/RequirementFamily",
                ));
            };
            let a = finite_function_coordinate(&goal.left, index).map_err(|message| {
                LeanCompileError::new("CartesianCoordinateEquality/Coordinate", &message)
            })?;
            let b = finite_function_coordinate(&goal.right, index).map_err(|message| {
                LeanCompileError::new("CartesianCoordinateEquality/Coordinate", &message)
            })?;
            if equal.left.ir() != a.ir()
                || equal.right.ir() != b.ir()
                || source_subject(child)? != *requirement
            {
                return Err(LeanCompileError::unsupported(
                    "CartesianCoordinateEquality/RequirementSubject",
                ));
            }
            // These verifications do not publish truth. Earlier checked WD is
            // visible through the existing borrowed requirement-stage cursor.
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let compiled = self.compile_verify(child, &prior)?;
            let checked = SourcePosition {
                before: index + 1,
                ..prior
            };
            let mut sides = Vec::with_capacity(2);
            for (side, (object, coordinate)) in [(&goal.left, &a), (&goal.right, &b)]
                .into_iter()
                .enumerate()
            {
                let value = self.compile_normalization_value(coordinate, &checked)?;
                let bridge = if matches!(object, Obj::ProductShape(ProductShape::Tuple(_))) {
                    format!("Litex.tuple_coordinate _coordinate_point_{side} ({index} : Fin {n})")
                } else {
                    format!("by\n    have _index : Litex.FiniteFunction.index (M := M) ({index} : Fin {n}) = M.number ({} : ℂ) := by norm_num [Litex.FiniteFunction.index]\n    exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _coordinate_point_{side})) _index", index + 1)
                };
                sides.push(format!("(show Litex.FunctionSemantics.callValue (M := M) (Litex.denote _coordinate_point_{side}) (Litex.FiniteFunction.index ({index} : Fin {n})) = {value} from {bridge})"));
            }
            coordinates.push(format!("(by\n  have _coordinate : {} := {}\n  exact ({}).trans (_coordinate.trans ({}).symm))", compiled.0, compiled.1, sides[0], sides[1]));
        }
        let pointwise = finite_vector_proof(&coordinates);
        Ok(format!("(by\n  let _coordinate_point_0 := {left}\n  let _coordinate_point_1 := {right}\n  let _coordinate_cart_0 := {left_cart}\n  let _coordinate_cart_1 := {right_cart}\n  have _coordinate_member_0 : Litex.In _coordinate_point_0 _coordinate_cart_0 := {left_member}\n  have _coordinate_member_1 : Litex.In _coordinate_point_1 _coordinate_cart_1 := {right_member}\n  exact Litex.FiniteFunction.cart_ext (M := M) _coordinate_member_0 _coordinate_member_1 {pointwise})"))
    }
}
