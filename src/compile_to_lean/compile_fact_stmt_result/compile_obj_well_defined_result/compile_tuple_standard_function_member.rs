//! A known literal tuple is a total function on its exact finite index set.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FiniteTupleInStandardFunctionSpaceProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_tuple_standard_function_member(
        &self,
        goal: &InFact,
        proof: &FiniteTupleInStandardFunctionSpaceProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let n = proof.source.value.args.len();
        if proof.coordinates.len() != n {
            return Err(LeanCompileError::unsupported(
                "TupleFunction/CoordinateArity",
            ));
        }
        let Obj::StandardSet(scalar) = proof.signature.ret_set.as_ref() else {
            return Err(LeanCompileError::unsupported(
                "TupleFunction/StandardCarrier",
            ));
        };
        Self::validate_finite_seq_signature(
            &FiniteSeqSet {
                set: proof.signature.ret_set.clone(),
                n: Box::new(Obj::Literal(Literal::Number(Number::new(n.to_string())))),
            },
            &proof.signature,
        )?;
        self.validate_function_carrier_signature(&goal.set, &proof.signature)?;
        let tuple_obj = Obj::ProductShape(ProductShape::Tuple(proof.source.value.clone()));
        let tuple = self.compile_object_reference(&tuple_obj, position)?;
        let source = self.compile_object_reference(&goal.element, position)?;
        let target = self.compile_object_reference(&goal.set, position)?;
        let equality = self.compile_equality_path(
            &goal.element,
            &tuple_obj,
            &proof.source.tuple_equal,
            position,
        )?;
        let signature = match &goal.set {
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => {
                format!("(Litex.finiteSeqSignature {target})")
            }
            Obj::FunctionSpace(FunctionSpace::FnSet(_)) => format!("({target}).val"),
            _ => return Err(LeanCompileError::unsupported("TupleFunction/Target")),
        };
        let mut checked = Vec::new();
        for (coordinate, element) in proof.coordinates.iter().zip(&proof.source.value.args) {
            if coordinate.element.ir() != element.ir() || &coordinate.set != scalar {
                return Err(LeanCompileError::unsupported(
                    "TupleFunction/CoordinateSubject",
                ));
            }
            checked.push(self.compile_structural(coordinate, position)?);
        }
        let coordinates = finite_vector_proof(&checked);
        Ok(format!(
            "(by\n  let _tuple := {tuple}\n  let _signature := {signature}\n  have _domain : _signature.domain = Litex.FiniteFunction.indexSet (M := M) {n} := by\n    change Litex.finiteSeqDomain (Litex.number (M := M) ({n} : ℂ)) = _\n    exact Litex.finiteSeqDomain_number {n}\n  have _coordinates : ∀ i : Fin {n}, M.mem (_tuple.val.values i) _signature.output := {coordinates}\n  have _member := Litex.tupleInFunctionSet _tuple _signature _domain _coordinates\n  exact Litex.inOfSame _tuple {source} (Litex.fnSet _signature) {target} ({equality}).symm (by rfl) _member)"
        ))
    }
}
