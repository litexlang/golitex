use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::{finite_call_parts, validate_finite_signature};
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::known_tuple::{literal_positive_usize, KnownTupleShapeProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::FiniteCoordinateBodyExpansionProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_finite_coordinate_expansion(
        &self,
        proof: &FiniteCoordinateBodyExpansionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(application) = &proof.application else {
            return Err(LeanCompileError::unsupported("FiniteExpansion/Application"));
        };
        validate_finite_signature(&proof.source)?;
        let KnownTupleShapeProof::TupleEquality(tuple) = &proof.source.source else {
            return Err(LeanCompileError::unsupported("FiniteExpansion/TupleSource"));
        };
        let (receiver, argument) = finite_call_parts(application)?;
        let index = proof.index;
        let n = tuple.value.args.len();
        if index == 0
            || index > n
            || literal_positive_usize(argument) != Some(index)
            || tuple.value.args[index - 1].ir() != proof.expanded_body.ir()
            || proof.continued_body.ir() != proof.expanded_body.ir()
        {
            return Err(LeanCompileError::unsupported("FiniteExpansion/Coordinate"));
        }
        ensure_object(&proof.application, &proof.application_well_defined)?;
        let step = SourcePosition::new(Some(position), SourceOwner::FiniteExpansion(proof), 0);
        let actual = self.compile_wd(&proof.application_well_defined, &step)?;
        let completed = SourcePosition { before: 1, ..step };
        let tuple_object = Obj::ProductShape(ProductShape::Tuple(tuple.value.clone()));
        let equality =
            self.compile_equality_path(&receiver, &tuple_object, &tuple.tuple_equal, &completed)?;
        let tuple_term = self.compile_object_reference(&tuple_object, &completed)?;
        let receiver = self.compile_object_reference(&receiver, &completed)?;
        let application = self.compile_normalization_value(&proof.application, &completed)?;
        let expanded = self.compile_normalization_value(&proof.expanded_body, &completed)?;
        let i = index - 1;
        Ok(format!("(show {application} = {expanded} from by\n  let _checked_call := {actual}\n  let _tuple := {tuple_term}\n  have _receiver : Litex.Same {receiver} _tuple := {equality}\n  have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number ({index} : ℂ)) = _tuple.val.values ({i} : Fin {n}) := by\n    simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple ({i} : Fin {n}))\n  have _component : _tuple.val.values ({i} : Fin {n}) = {expanded} := rfl\n  exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number ({index} : ℂ))) _receiver).trans (_coordinate.trans _component)\n)"))
    }
}
