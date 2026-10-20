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
        let leaves = arguments.iter().all(|argument| {
            matches!(
                argument.as_ref(),
                Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
            )
        });
        for (index, (argument, wd)) in arguments.iter().zip(children).enumerate() {
            ensure_object(argument, wd)?;
            let child = self.compile_wd(
                wd,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
            let name = if leaves {
                child
            } else {
                let name = format!("_productChild_{index}");
                definitions.push(format!("let {name} := {child}"));
                name
            };
            values.push(format!("Litex.denote {name}"));
            sethood.push(format!("(Litex.isSet {name})"));
        }
        let h_sets = if leaves {
            sethood
                .iter()
                .rev()
                .fold("(fun i => Fin.elim0 i)".to_owned(), |tail, proof| {
                    format!("(Fin.cases {proof} {tail})")
                })
        } else {
            finite_vector_proof(&sethood)
        };
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
