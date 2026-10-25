use super::compile_function_preimage::{preimage_parts, validate_preimage_builder};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferPreimageConstructionResult, StoreInferredFactResult};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_preimage_inference(
        &self,
        expected_set_target: bool,
        source_id: FactId,
        source_equal: &KnownEqualityPathProof,
        construction: &InferPreimageConstructionResult,
        derived: &[StoreInferredFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = seed else {
            return Err(LeanCompileError::unsupported("PreimageInference/Seed"));
        };
        if source_id != member.fact_id {
            return Err(LeanCompileError::unsupported("PreimageInference/SourceId"));
        }
        let root = source_equal
            .path
            .last()
            .map(|(_, to, _)| to)
            .unwrap_or(&member.set);
        validate_preimage_builder(root, &construction.source, &construction.builder)?;
        let (function, target, set_target) = preimage_parts(root)?;
        if set_target != expected_set_target {
            return Err(LeanCompileError::unsupported(
                "PreimageInference/SelectedConstructor",
            ));
        }
        let same = self.compile_equality_path(&member.set, root, source_equal, position)?;
        let input = self.compile_object_reference(&member.element, position)?;
        let set = self.compile_object_reference(&member.set, position)?;
        let root_term = self.compile_object_reference(root, position)?;
        let hf = self.compile_complete_domain_member(function, &construction.source, position)?;
        let signature = &construction.source.signature;
        let sig = self.compile_fn_signature(signature, position)?;
        let law = if set_target {
            "preimageSetMembers"
        } else {
            "preimageMembers"
        };
        let membership = format!(
            "(Litex.inOfSame {input} {input} {set} {root_term} (Litex.sameRefl {input}) {same} {})",
            compiled.1
        );
        let input_raw = format!("(Litex.denote {input})");
        let (mut lines, values, explicit) =
            self.compile_preimage_domain_parts(signature, &input_raw, position)?;
        lines.insert(0, format!("obtain ⟨_preimage_domain, _preimage_output⟩ := (Litex.{law} {root_term} {sig} {hf} {input_raw}).mp {membership}"));
        let repack = self.compile_preimage_repack(&values, "_preimage_base");
        if values.len() > 1 {
            lines.push(format!("have _preimage_repack : {input_raw} = Litex.FiniteFunction.tupleValue (M := M) ![{}] := {repack}",values.join(", ")));
        }
        let mut bodies = vec!["_preimage_base".to_string()];
        bodies.extend(explicit);
        bodies.push(if values.len() == 1 {
            "_preimage_output".into()
        } else {
            let f = self.compile_object_reference(function, position)?;
            let target = self.compile_object_reference(target, position)?;
            let output = format!("Litex.FunctionSemantics.callValue (M := M) (Litex.denote {f}) x");
            let predicate = if set_target {
                format!("fun x => M.mem ({output}) (Litex.denote {target})")
            } else {
                format!("fun x => ({output}) = Litex.denote {target}")
            };
            format!("(Eq.mp (congrArg ({predicate}) _preimage_repack) _preimage_output)")
        });
        let substitution = HashMap::from([(
            construction.builder.param_binding.id,
            member.element.clone(),
        )]);
        let mut next = 0;
        let mut seen = vec![source_id];
        let mut declarations = Vec::new();
        for (offset, store) in derived.iter().enumerate() {
            let id = store.primary_fact_id();
            if seen.contains(&id) {
                return Err(LeanCompileError::unsupported("PreimageInference/Identity"));
            }
            seen.push(id);
            let prior = SourcePosition {
                before: position.before + offset,
                ..*position
            };
            let fact = self.resolve_fact(id, &prior)?;
            let selected=(next..bodies.len()).find(|&i|if i==0 {
                matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==member.element.ir()&&p.set.ir()==construction.builder.param_set.ir())
            } else {instantiated_fact_matches(&crate::instantiate::quantifier_free_fact_to_fact(construction.builder.facts[i-1].clone()),&fact,&substitution)}).ok_or_else(||LeanCompileError::unsupported("PreimageInference/OrderedSubject"))?;
            next = selected + 1;
            self.validate_store(&store.store, &fact)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&store.store),
                usize::MAX,
            );
            // Interpret the validated builder clause at its original bound input.
            // Its coordinates are certified by the complete domain above; no
            // separate coordinate-inference stores were produced by the runtime.
            let proposition = if selected == 0 {
                self.compile_function_raw_predicate(&fact, &formed, &HashMap::new())?
            } else {
                let clause = crate::instantiate::quantifier_free_fact_to_fact(
                    construction.builder.facts[selected - 1].clone(),
                );
                let bindings =
                    HashMap::from([(construction.builder.param_binding.id, input_raw.clone())]);
                self.compile_function_raw_predicate(&clause, &formed, &bindings)?
            };
            let proof = (
                proposition,
                format!(
                    "(by\n  {}\n  exact {})",
                    lines.join("\n  "),
                    bodies[selected]
                ),
            );
            declarations.push(self.emit_internal_fact(&fact, &proof, &formed)?);
            declarations.extend(self.compile_stored_projections(
                &store.store,
                &fact,
                &proof,
                &formed,
            )?);
        }
        Ok(declarations)
    }
    pub(super) fn compile_preimage_domain_parts(
        &self,
        signature: &FnSet,
        input_raw: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), LeanCompileError> {
        let (base, base_set) = self.compile_function_semantic_base_domain(signature, position)?;
        let output = self.compile_object_reference(&signature.ret_set, position)?;
        let guard = self.compile_function_packed_guard_template(signature, position)?;
        let values = self.compile_function_packed_values(signature, &input_raw)?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        let positive = self.compile_function_positive_inputs(signature, position)?;
        let mut lines = vec![format!("obtain ⟨_preimage_members, _preimage_guard⟩ := (Litex.FunctionSignature.withGuard_domain {base} (Litex.denote {output}) {base_set} (Litex.isSet {output}) {guard} _).mp _preimage_domain")];
        let mut guards = positive
            .iter()
            .map(|id| format!("_preimage_positive_i{}", id.value()))
            .collect::<Vec<_>>();
        let explicit = (0..signature.dom_facts.len())
            .map(|i| format!("_preimage_guard_{i}"))
            .collect::<Vec<_>>();
        guards.extend(explicit.iter().cloned());
        if guards.len() == 1 {
            lines.push(format!("have {} := _preimage_guard", guards[0]));
        } else if guards.len() > 1 {
            lines.push(format!(
                "rcases _preimage_guard with ⟨{}⟩",
                guards.join(", ")
            ));
        }
        let mut members = Vec::new();
        for (i, value) in values.iter().enumerate() {
            let h = if values.len() == 1 {
                "_preimage_members".to_string()
            } else {
                format!("(by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _preimage_members ({i} : Fin {}))",values.len())
            };
            let h = if positive.contains(&parameters[i].id) {
                format!("((Litex.positiveReal_members (M := M) {value}).mpr ⟨{h}, _preimage_positive_i{}⟩)",parameters[i].id.value())
            } else {
                h
            };
            members.push(h);
        }
        let (original_base, _) = self.compile_function_base_domain(signature, position)?;
        let base_proof = if values.len() == 1 {
            members[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.cart_of_coordinates _preimage_members {})",
                finite_vector_proof(&members)
            )
        };
        lines.push(format!(
            "have _preimage_base : M.mem {input_raw} {original_base} := {base_proof}"
        ));
        Ok((lines, values, explicit))
    }
}
