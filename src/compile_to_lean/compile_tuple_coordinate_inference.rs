use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferEqualFactResult, InferEqualFactTupleCoordinatesResult};
use std::collections::HashSet;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_tuple_coordinate_inference(
        &self,
        rule: &InferEqualFactTupleCoordinatesResult,
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if rule.source_fact_id != source.fact_id {
            return Err(LeanCompileError::unsupported("TupleInference/Seed"));
        }
        let (subject, value, equality) = if rule.reversed {
            (
                &source.right,
                &source.left,
                format!("(Eq.symm {})", compiled.1),
            )
        } else {
            (&source.left, &source.right, compiled.1.clone())
        };
        let Obj::ProductShape(ProductShape::Tuple(tuple)) = value else {
            return Err(LeanCompileError::unsupported("TupleInference/Constructor"));
        };
        if rule.coordinates.len() != tuple.args.len() {
            return Err(LeanCompileError::unsupported("TupleInference/Arity"));
        }
        let receiver = self.compile_object_reference(subject, position)?;
        let tuple_term = self.compile_object_reference(value, position)?;
        let n = tuple.args.len();
        let mut identities = HashSet::from([source.fact_id]);
        let mut declarations = Vec::new();
        for (index, captured) in rule.coordinates.iter().enumerate() {
            if !identities.insert(captured.primary_fact_id()) {
                return Err(LeanCompileError::unsupported("TupleInference/Identity"));
            }
            let expected = finite_function_coordinate(subject, index)
                .map_err(|e| LeanCompileError::new("TupleInference/Coordinate", &e))?;
            let fact = self.resolve_fact(captured.primary_fact_id(), position)?;
            if !matches!(&fact, Fact::AtomicFact(AtomicFact::EqualFact(equal))
                if equal.left.ir() == expected.ir() && equal.right.ir() == tuple.args[index].ir())
            {
                return Err(LeanCompileError::unsupported("TupleInference/Subject"));
            }
            self.validate_store(&captured.store, &fact)?;
            let k = index + 1;
            let coordinate = if matches!(subject, Obj::ProductShape(ProductShape::Tuple(_))) {
                self.compile_object_reference(&expected, position)?
            } else {
                format!("(Litex.cartCall {receiver} (Litex.tupleSingletonCart {tuple_term}) (Litex.number (M := M) ({k} : ℂ)) (Litex.inOfSame {tuple_term} {receiver} _ _ (Eq.symm {equality}) (Litex.sameRefl _) (Litex.tupleInSingletonCart {tuple_term})) (by change M.mem (M.number ({k} : ℂ)) (Litex.FiniteFunction.indexSet {n}); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) ({index} : Fin {n}))))")
            };
            let name = format!("_object_h{}", captured.primary_fact_id().value());
            declarations.push(if position.is_local() {
                format!("let {name} := {coordinate}")
            } else {
                format!(
                    "noncomputable def {name}{} := {coordinate}",
                    self.context_header(position)?
                )
            });
            let coordinate_ref = if position.is_local() {
                name
            } else {
                self.context_application(&name, position)
            };
            let target = self.compile_object_reference(&tuple.args[index], position)?;
            let left_beta = if let Obj::ProductShape(ProductShape::Tuple(left)) = subject {
                format!("by\n    have _projection : Litex.FunctionSemantics.callValue (M := M) (Litex.denote {receiver}) (M.number ({k} : ℂ)) = ({receiver}).val.values ({index} : Fin {}) := by\n      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate {receiver} ({index} : Fin {}))\n    have _component : ({receiver}).val.values ({index} : Fin {}) = Litex.denote {coordinate_ref} := rfl\n    exact _projection.trans _component", left.args.len(), left.args.len(), left.args.len())
            } else {
                "rfl".into()
            };
            let proof = format!("(by\n  let _tuple := {tuple_term}\n  have _same : Litex.Same {receiver} _tuple := {equality}\n  have _left : Litex.FunctionSemantics.callValue (M := M) (Litex.denote {receiver}) (M.number ({k} : ℂ)) = Litex.denote {coordinate_ref} := {left_beta}\n  have _right : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number ({k} : ℂ)) = _tuple.val.values ({index} : Fin {n}) := by\n    simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple ({index} : Fin {n}))\n  have _component : _tuple.val.values ({index} : Fin {n}) = Litex.denote {target} := rfl\n  exact _left.symm.trans ((congrArg (fun v => Litex.FunctionSemantics.callValue (M := M) v (M.number ({k} : ℂ))) _same).trans (_right.trans _component))\n)");
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            let conclusion = (format!("Litex.Same {coordinate_ref} {target}"), proof);
            declarations.push(self.emit_internal_fact(&fact, &conclusion, &formed)?);
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn compile_tuple_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let StoreFactResult::AtomicFact(stored) = store else {
            return Ok(None);
        };
        let AtomicFact::EqualFact(equal) = &stored.fact else {
            return Ok(None);
        };
        if equal.left.ir() != object.ir() {
            return Ok(None);
        }
        let mut current = Some(position);
        while let Some(cursor) = current {
            if let SourceOwner::EqualityInferences(rules) = cursor.owner {
                for rule in rules {
                    let InferEqualFactResult::TupleCoordinates(rule) = rule else {
                        continue;
                    };
                    if rule
                        .coordinates
                        .iter()
                        .any(|coordinate| std::ptr::eq(&coordinate.store, store))
                    {
                        let name = format!("_object_h{}", stored.fact_id.value());
                        return Ok(Some(if cursor.is_local() {
                            name
                        } else {
                            self.context_application(&name, cursor)
                        }));
                    }
                }
            }
            current = cursor.parent;
        }
        Ok(None)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/compile_to_lean/tuple_coordinate_inference_tests.rs"]
mod tests;
