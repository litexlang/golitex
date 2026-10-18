use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactCartCoordinatesResult;
use std::collections::HashSet;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_cart_coordinate_inferences(
        &self,
        proof: &InferInFactCartCoordinatesResult,
        seed: &Fact,
        member: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(source)) = seed else {
            return Err(LeanCompileError::unsupported("CartInference/SeedFamily"));
        };
        let Obj::ProductShape(ProductShape::Cart(cart)) = &source.set else {
            return Err(LeanCompileError::new(
                "CartInference/Carrier",
                "Coordinate projections require the original Cartesian membership.",
            ));
        };
        if proof.coordinates.len() != cart.args.len() {
            return Err(LeanCompileError::new(
                "CartInference/Arity",
                "The captured coordinate stores differ from the complete source factor list.",
            ));
        }
        let mut declarations = Vec::new();
        let mut identities = HashSet::from([source.fact_id]);
        for (index, projection) in proof.coordinates.iter().enumerate() {
            if projection.coordinate_index != index {
                return Err(LeanCompileError::new(
                    "CartInference/Order",
                    "Coordinate stores must retain their original zero-based order.",
                ));
            }
            let captured = &projection.membership;
            if !identities.insert(captured.primary_fact_id()) {
                return Err(LeanCompileError::new(
                    "CartInference/Identity",
                    "Each coordinate projection needs its distinct original FactId.",
                ));
            }
            let prior = SourcePosition {
                before: position.before + index,
                ..*position
            };
            let expected = finite_function_coordinate(&source.element, index)
                .map_err(|error| LeanCompileError::new("CartInference/Coordinate", &error))?;
            let fact = self.resolve_fact(captured.primary_fact_id(), &prior)?;
            match &fact {
                Fact::AtomicFact(AtomicFact::InFact(derived))
                    if derived.element.ir() == expected.ir()
                        && derived.set.ir() == cart.args[index].ir() => {}
                _ => return Err(LeanCompileError::new(
                    "CartInference/Subject",
                    "The stored conclusion differs from this source receiver, coordinate or factor.",
                )),
            }
            self.validate_store(&captured.store, &fact)?;
            let (coordinate, certificate) =
                self.compile_cart_inference_coordinate(source, index, &member.1, &prior)?;
            let factor = self.compile_object_reference(&cart.args[index], &prior)?;
            let compiled = (format!("Litex.In {coordinate} {factor}"), certificate);
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            declarations.push(self.emit_internal_fact(&fact, &compiled, &formed)?);
        }
        Ok(declarations)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferCartCoordinateResult, InferInFactResult, InferResult,
        StoreAtomicFactResult, StoreInferredFactResult,
    };

    fn checked() -> (RunLitexCodeResult, LitexToLeanCompiler) {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let result = runtime
            .run_litex_code("have coordinate_receiver cart(R, R)\n")
            .unwrap();
        assert!(result.success && result.session_error.is_none());
        (result, LitexToLeanCompiler::new(runtime))
    }

    fn capture(
        result: &RunLitexCodeResult,
    ) -> (
        Fact,
        &InferAtomicFactResult,
        &InferInFactCartCoordinatesResult,
    ) {
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) = &result.statement_results[0]
        else {
            panic!("original parameter declaration")
        };
        let store = &proof.store_and_infer_result.store_and_infer_results[0];
        let StoreFactResult::AtomicFact(stored) = &store.store else {
            panic!("membership store")
        };
        let Some(InferResult::AtomicFact(infer @ InferAtomicFactResult::InFact(rules))) =
            &store.infer
        else {
            panic!("membership inference")
        };
        let coordinates = rules
            .iter()
            .find_map(|rule| match rule {
                InferInFactResult::CartCoordinates(proof) => Some(proof),
                _ => None,
            })
            .expect("original coordinate projections");
        (Fact::AtomicFact(stored.fact.clone()), infer, coordinates)
    }

    fn copy_projection(source: &InferCartCoordinateResult) -> InferCartCoordinateResult {
        let StoreFactResult::AtomicFact(stored) = &source.membership.store else {
            panic!("coordinate membership")
        };
        InferCartCoordinateResult {
            coordinate_index: source.coordinate_index,
            membership: StoreInferredFactResult {
                store: StoreFactResult::AtomicFact(StoreAtomicFactResult {
                    fact_id: stored.fact_id,
                    fact: stored.fact.clone(),
                }),
            },
        }
    }

    fn membership_store(result: &RunLitexCodeResult) -> &StoreFactAndInferResult {
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) = &result.statement_results[0]
        else {
            panic!("original parameter declaration")
        };
        &proof.store_and_infer_result.store_and_infer_results[0]
    }

    #[test]
    fn cart_projection_constructor_replays_the_original_prop_inference_owner() {
        let (result, compiler) = checked();
        let (_, _, proof) = capture(&result);
        let store = &proof.coordinates[0].membership.store;
        let StoreFactResult::AtomicFact(stored) = store else {
            panic!("original coordinate membership")
        };
        let AtomicFact::InFact(member) = &stored.fact else {
            panic!("original coordinate membership")
        };
        let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let current = SourcePosition::new(
            Some(&root),
            SourceOwner::PropInference(membership_store(&result)),
            1,
        );
        let term = compiler
            .compile_cart_inferred_subject(&member.element, store, &current)
            .unwrap()
            .expect("the completed original projection supplies its constructor");
        assert!(term.contains("Litex.cartCall"));
    }

    #[test]
    fn cart_projection_prop_owner_rejects_same_id_with_another_factor() {
        let (result, compiler) = checked();
        let (_, _, proof) = capture(&result);
        let mut projection = copy_projection(&proof.coordinates[0]);
        let StoreFactResult::AtomicFact(stored) = &mut projection.membership.store else {
            panic!("original coordinate membership")
        };
        let AtomicFact::InFact(member) = &mut stored.fact else {
            panic!("original coordinate membership")
        };
        member.set = Obj::StandardSet(StandardSet::Q);
        let object = member.element.clone();
        let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let current = SourcePosition::new(
            Some(&root),
            SourceOwner::PropInference(membership_store(&result)),
            1,
        );
        let error = compiler
            .compile_cart_inferred_subject(&object, &projection.membership.store, &current)
            .unwrap_err();
        assert!(error.to_string().contains("CartInference/Subject"));
    }

    #[test]
    fn cart_projection_emits_each_original_coordinate_once() {
        let (result, compiler) = checked();
        let (seed, infer, proof) = capture(&result);
        let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let current =
            SourcePosition::new(Some(&root), SourceOwner::AtomicInference(&seed, infer), 0);
        let member = (String::new(), format!("h_{}", seed.fact_id().value()));
        let declarations = compiler
            .compile_cart_coordinate_inferences(proof, &seed, &member, &current)
            .unwrap();
        assert_eq!(declarations.len(), 2);
        for (declaration, projection) in declarations.iter().zip(&proof.coordinates) {
            assert!(declaration.starts_with(&format!(
                "theorem h_{}",
                projection.membership.primary_fact_id().value()
            )));
        }
    }

    #[test]
    fn cart_projection_rejects_wrong_source_coordinate_order() {
        let (result, compiler) = checked();
        let (seed, infer, proof) = capture(&result);
        let mut copied = InferInFactCartCoordinatesResult {
            coordinates: proof.coordinates.iter().map(copy_projection).collect(),
        };
        copied.coordinates[0].coordinate_index = 1;
        let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let current =
            SourcePosition::new(Some(&root), SourceOwner::AtomicInference(&seed, infer), 0);
        let error = compiler
            .compile_cart_coordinate_inferences(
                &copied,
                &seed,
                &(String::new(), String::new()),
                &current,
            )
            .unwrap_err();
        assert!(error.to_string().contains("CartInference/Order"));
    }

    #[test]
    fn cart_projection_rejects_mutated_stored_factor() {
        let (result, compiler) = checked();
        let (seed, infer, proof) = capture(&result);
        let mut copied = InferInFactCartCoordinatesResult {
            coordinates: proof.coordinates.iter().map(copy_projection).collect(),
        };
        let StoreFactResult::AtomicFact(stored) = &mut copied.coordinates[0].membership.store
        else {
            unreachable!()
        };
        let AtomicFact::InFact(derived) = &mut stored.fact else {
            unreachable!()
        };
        derived.set = Obj::StandardSet(StandardSet::Q);
        let root = SourcePosition::new(None, SourceOwner::Run(&result), 1);
        let current =
            SourcePosition::new(Some(&root), SourceOwner::AtomicInference(&seed, infer), 0);
        let error = compiler
            .compile_cart_coordinate_inferences(
                &copied,
                &seed,
                &(String::new(), String::new()),
                &current,
            )
            .unwrap_err();
        assert!(error.to_string().contains("Store/Subject"));
    }
}
