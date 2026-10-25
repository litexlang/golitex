use super::compile_function_preimage::{preimage_parts, validate_preimage_builder};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Reuse only constructors introduced by this exact preimage projection.
    pub(super) fn compile_preimage_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(String, Option<StandardSet>)>, LeanCompileError> {
        if !matches!(
            object,
            Obj::FnObj(_) | Obj::ProductShape(ProductShape::Cart(_))
        ) {
            return Ok(None);
        }
        let Some((id, path, construction)) = position.inferred_preimage_step(store) else {
            return Ok(None);
        };
        let (seed, cited) = self.cited_fact_reference(id, position)?;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = seed else {
            return Err(LeanCompileError::unsupported("PreimageCall/Source"));
        };
        let root = path.path.last().map(|(_, to, _)| to).unwrap_or(&member.set);
        validate_preimage_builder(root, &construction.source, &construction.builder)?;
        if let Obj::ProductShape(ProductShape::Cart(cart)) = object {
            if object.ir() != construction.builder.param_set.ir() {
                return Ok(None);
            }
            let sets = cart
                .args
                .iter()
                .map(|set| self.compile_object_reference(set, position))
                .collect::<Result<Vec<_>, _>>()?;
            let values = sets
                .iter()
                .map(|set| format!("Litex.denote {set}"))
                .collect::<Vec<_>>();
            let proofs = sets
                .iter()
                .map(|set| format!("Litex.isSet {set}"))
                .collect::<Vec<_>>();
            return Ok(Some((
                format!(
                    "(Litex.cart (M := M) ![{}] {})",
                    values.join(", "),
                    finite_vector_proof(&proofs)
                ),
                None,
            )));
        }
        let source_call = match construction.builder.facts.last() {
            Some(QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(p))) => &p.left,
            Some(QuantifierFreeFact::AtomicFact(AtomicFact::InFact(p))) => &p.element,
            _ => return Err(LeanCompileError::unsupported("PreimageCall/Output")),
        };
        let substitution = HashMap::from([(
            construction.builder.param_binding.id,
            member.element.clone(),
        )]);
        if !instantiated_object_matches(source_call, object, &substitution) {
            return Ok(None);
        }
        let (function, _, set_target) = preimage_parts(root)?;
        let same = self.compile_equality_path(&member.set, root, path, position)?;
        let input = self.compile_object_reference(&member.element, position)?;
        let carrier = self.compile_object_reference(&member.set, position)?;
        let root_term = self.compile_object_reference(root, position)?;
        let hf = self.compile_complete_domain_member(function, &construction.source, position)?;
        let signature = &construction.source.signature;
        let sig = self.compile_fn_signature(signature, position)?;
        let f = self.compile_object_reference(function, position)?;
        let law = if set_target {
            "preimageSetMembers"
        } else {
            "preimageMembers"
        };
        let mut lines=vec![format!("have _preimage_domain := ((Litex.{law} {root_term} {sig} {hf} (Litex.denote {input})).mp (Litex.inOfSame {input} {input} {carrier} {root_term} (Litex.sameRefl {input}) {same} {cited})).1")];
        let (domain_parts, values, _) = self.compile_preimage_domain_parts(
            signature,
            &format!("(Litex.denote {input})"),
            position,
        )?;
        let (argument, domain) = if values.len() == 1 {
            (input.clone(), "_preimage_domain".to_string())
        } else {
            // Keep elimination of domain proofs inside a proof-valued binding.
            // It must not wrap the call object and obstruct its denotation.
            let (base, _) = self.compile_function_base_domain(signature, position)?;
            lines.push(format!("have _preimage_base : M.mem (Litex.denote {input}) {base} := by\n    {}\n    exact _preimage_base", domain_parts.join("\n    ")));
            let repack = self.compile_preimage_repack(&values, "_preimage_base");
            lines.push(format!("have _preimage_repack : Litex.denote {input} = Litex.FiniteFunction.tupleValue (M := M) ![{}] := {repack}",values.join(", ")));
            let wd=finite_vector_proof(&values.iter().enumerate().map(|(i,_)|format!("M.member_isSet (Litex.FiniteFunction.coordinate_mem_number _preimage_base ({i} : Fin {}) ({} : ℂ) (by norm_num))",values.len(),i+1)).collect::<Vec<_>>());
            (format!("(Litex.tuple (M := M) ![{}] {wd})",values.join(", ")),
             format!("(Eq.mp (congrArg (fun x => M.mem x ({sig}).domain) _preimage_repack) _preimage_domain)"))
        };
        lines.push(format!(
            "exact Litex.callOn {sig} {f} {argument} {hf} {domain}"
        ));
        Ok(Some((
            format!("(by\n  {})", lines.join("\n  ")),
            self.compile_numeric_carrier(&signature.ret_set, position)
                .ok(),
        )))
    }

    pub(super) fn numeric_preimage_call(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(String, String, String, Option<EvalRational>)>, LeanCompileError> {
        if !matches!(object, Obj::FnObj(_)) {
            return Ok(None);
        }
        position.with_visible_inferred_subject_filter(object,&mut |store,producer| {
            let Some((term,Some(output)))=self.compile_preimage_inferred_subject(object,store,producer)? else {return Ok(None);};
            let member=standard_inclusion_term(&output,&StandardSet::C,"_preimage_call","(Litex.callOnInOutput _preimage_call)")?;
            Ok(Some((format!("(let _preimage_call := {term}; Litex.NativeBridge.asComplex _preimage_call {member})"),
                format!("(let _preimage_call := {term}; Litex.NativeBridge.asComplex_spec _preimage_call {member})"),
                format!("(let _preimage_call := {term}; {member})"),None)))
        })
    }
}
