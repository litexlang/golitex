use super::compile_function_preimage::preimage_parts;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionPreimageInputView;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_preimage_membership(
        &self,
        fact: &AtomicFact,
        expected_set_target: bool,
        construction: &FunctionPreimageConstructionProof,
        input_view: &FunctionPreimageInputView,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::InFact(member) = fact else {
            return Err(LeanCompileError::unsupported("PreimageMembership/Family"));
        };
        let (function, target, set_target) = preimage_parts(&member.set)?;
        if set_target != expected_set_target {
            return Err(LeanCompileError::unsupported(
                "PreimageMembership/SelectedConstructor",
            ));
        }

        let (hf, checked) = self.compile_preimage_construction(
            &member.set,
            construction,
            &position.atomic_search_prior(0)?,
        )?;
        let signature = &construction.source.signature;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        if proofs.len() != requirements.len() || proofs.is_empty() {
            return Err(LeanCompileError::unsupported("PreimageMembership/Stages"));
        }
        let mut children = Vec::new();
        for (index, (requirement, proof)) in requirements.iter().zip(proofs).enumerate() {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "PreimageMembership/RequirementSubject",
                ));
            }
            children.push(
                self.compile_verify(proof, &position.atomic_search_prior(index + 1)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(proofs.len() + 1)?;
        let input = self.compile_object_reference(&member.element, &complete)?;
        let input_raw = format!("(Litex.denote {input})");
        let (arguments, domain_proofs, input_same) = match input_view {
            FunctionPreimageInputView::BoundedAssignment => {
                if requirements.len() != construction.builder.facts.len() + 1
                    || !matches!(&requirements[0],Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==member.element.ir() && p.set.ir()==construction.builder.param_set.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "PreimageMembership/BoundedInput",
                    ));
                }
                let substitution = HashMap::from([(
                    construction.builder.param_binding.id,
                    member.element.clone(),
                )]);
                for (source, actual) in construction.builder.facts.iter().zip(&requirements[1..]) {
                    if !instantiated_fact_matches(
                        &crate::instantiate::quantifier_free_fact_to_fact(source.clone()),
                        actual,
                        &substitution,
                    ) {
                        return Err(LeanCompileError::unsupported(
                            "PreimageMembership/BoundedCondition",
                        ));
                    }
                }
                let values = self.compile_function_packed_values(signature, &input_raw)?;
                let mut args = Vec::new();
                let mut domain = Vec::new();
                for (i, value) in values.iter().enumerate() {
                    let hm = if values.len() == 1 {
                        children[0].clone()
                    } else {
                        format!("(by simpa only [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem {} ({i} : Fin {}))",children[0],values.len())
                    };
                    args.push(if values.len() == 1 {
                        input.clone()
                    } else {
                        format!("(Litex.semanticObject {value} (M.member_isSet {hm}))")
                    });
                    domain.push(hm);
                }
                domain.extend_from_slice(&children[1..children.len() - 1]);
                let eq = self.compile_preimage_repack(&values, &children[0]);
                (args, domain, eq)
            }
            FunctionPreimageInputView::LiteralTuple { tuple, input_equal } => {
                if parameters.len() == 1
                    || tuple.args.len() != parameters.len()
                    || requirements.len() != parameters.len() + signature.dom_facts.len() + 1
                {
                    return Err(LeanCompileError::unsupported(
                        "PreimageMembership/TupleArity",
                    ));
                }
                let substitution = parameters
                    .iter()
                    .zip(&tuple.args)
                    .map(|((p, _), arg)| (p.id, arg.as_ref().clone()))
                    .collect::<HashMap<_, _>>();
                for (index, ((_, carrier), arg)) in parameters.iter().zip(&tuple.args).enumerate() {
                    if !matches!(&requirements[index],Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==arg.ir() && p.set.ir()==carrier.ir())
                    {
                        return Err(LeanCompileError::unsupported(
                            "PreimageMembership/TupleInput",
                        ));
                    }
                }
                for (guard, actual) in signature
                    .dom_facts
                    .iter()
                    .zip(&requirements[parameters.len()..])
                {
                    if !instantiated_fact_matches(
                        &crate::instantiate::quantifier_free_fact_to_fact(guard.clone()),
                        actual,
                        &substitution,
                    ) {
                        return Err(LeanCompileError::unsupported(
                            "PreimageMembership/TupleGuard",
                        ));
                    }
                }
                let call =
                    crate::execute::execute_fact_stmt::function_domain::function_application(
                        function,
                        tuple.args.clone(),
                    )
                    .map_err(|_| LeanCompileError::unsupported("PreimageMembership/TupleCall"))?;
                let matches = match (set_target, requirements.last()) {
                    (false, Some(Fact::AtomicFact(AtomicFact::EqualFact(p)))) => {
                        p.left.ir() == call.ir() && p.right.ir() == target.ir()
                    }
                    (true, Some(Fact::AtomicFact(AtomicFact::InFact(p)))) => {
                        p.element.ir() == call.ir() && p.set.ir() == target.ir()
                    }
                    _ => false,
                };
                if !matches {
                    return Err(LeanCompileError::unsupported(
                        "PreimageMembership/TupleOutput",
                    ));
                }
                let tuple_obj = Obj::ProductShape(ProductShape::Tuple(tuple.clone()));
                let same = self.compile_equality_path(
                    &member.element,
                    &tuple_obj,
                    input_equal,
                    &complete,
                )?;
                let args = tuple
                    .args
                    .iter()
                    .map(|x| self.compile_object_reference(x, &complete))
                    .collect::<Result<Vec<_>, _>>()?;
                (args, children[..children.len() - 1].to_vec(), same)
            }
        };
        let (packed, domain) =
            self.compile_complete_input(signature, &arguments, &domain_proofs, &complete)?;
        let sig = self.compile_fn_signature(signature, &complete)?;
        let root = self.compile_object_reference(&member.set, &complete)?;
        let predicate = if set_target {
            "fun x => M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x) (Litex.denote _preimage.val.target)"
        } else {
            "fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x = Litex.denote _preimage.val.target"
        };
        let law = if set_target {
            "preimageSetMembers"
        } else {
            "preimageMembers"
        };
        let conclusion = children.last().unwrap();
        Ok(format!("(by\n  let _preimage := {root}\n  let _preimage_builder := {checked}\n  have _preimage_same : {input_raw} = {packed} := {input_same}\n  exact (Litex.{law} _preimage {sig} {hf} {input_raw}).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ({sig}).domain) _preimage_same) {domain}, Eq.mpr (congrArg ({predicate}) _preimage_same) {conclusion}⟩)"))
    }

    pub(super) fn compile_preimage_repack(&self, values: &[String], member: &str) -> String {
        if values.len() == 1 {
            return "rfl".into();
        }
        format!("(by\n  apply (Litex.FiniteFunction.reconstruct {member}).trans\n  apply congrArg (Litex.FiniteFunction.tupleValue (M := M))\n  funext i\n  fin_cases i <;> norm_num [Litex.FiniteFunction.index])")
    }
}
