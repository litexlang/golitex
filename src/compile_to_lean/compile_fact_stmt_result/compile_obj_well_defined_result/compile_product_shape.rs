use crate::compile_to_lean::helper::{ensure_object, finite_vector_proof};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ProductShapeObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_product_shape_wd(
        &self,
        shape: &ProductShape,
        proof: &ProductShapeObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (constructor, arguments, children, requirements) = match (shape, proof) {
            (ProductShape::Cart(cart), ProductShapeObjWellDefinedProofByDef::Cart(proof)) => (
                "cart",
                &cart.args,
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            (ProductShape::Tuple(tuple), ProductShapeObjWellDefinedProofByDef::Tuple(proof)) => (
                "tuple",
                &tuple.args,
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            _ => {
                return Err(LeanCompileError::new(
                    "ProductShape/Constructor",
                    "Finite-product evidence belongs to another source constructor.",
                ))
            }
        };
        if children.len() != arguments.len() || !requirements.is_empty() {
            return Err(LeanCompileError::new(
                "ProductShape/Stages",
                "Finite-product formation needs exactly its ordered child WD stages.",
            ));
        }
        let mut definitions = Vec::new();
        let mut values = Vec::new();
        let mut sethood = Vec::new();
        for (index, (argument, wd)) in arguments.iter().zip(children).enumerate() {
            ensure_object(argument, wd)?;
            let child = self.compile_wd(
                wd,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
            let name = format!("_productChild_{index}");
            definitions.push(format!("let {name} := {child}"));
            values.push(format!("Litex.denote {name}"));
            sethood.push(format!("Litex.isSet {name}"));
        }
        let h_sets = finite_vector_proof(&sethood);
        let term = format!(
            "Litex.{constructor} (M := M) ![{}] {h_sets}",
            values.join(", ")
        );
        if definitions.is_empty() {
            Ok(format!("({term})"))
        } else {
            definitions.push(term);
            Ok(format!("({})", definitions.join(";\n")))
        }
    }
}
