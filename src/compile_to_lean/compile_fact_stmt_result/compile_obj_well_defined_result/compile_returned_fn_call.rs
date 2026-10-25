use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Read fixed codomain layers, without substituting or searching for a
    /// different signature. Dependent return carriers are rejected by their
    /// signature compiler; sequence/Cartesian layers retain separate consumers.
    pub(in crate::compile_to_lean) fn fixed_function_call_layers<'a>(
        application: &FnObj,
        signature: &'a FnSet,
    ) -> Result<Vec<&'a FnSet>, LeanCompileError> {
        let mut layers = Vec::new();
        let mut current = signature;
        for (index, arguments) in application.body.iter().enumerate() {
            if arguments.len()
                != current
                    .set_bound_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>()
            {
                return Err(LeanCompileError::unsupported("ReturnedFunction/LayerArity"));
            }
            layers.push(current);
            if index + 1 < application.body.len() {
                let Obj::FunctionSpace(FunctionSpace::FnSet(next)) = current.ret_set.as_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "ReturnedFunction/LayerCarrier",
                    ));
                };
                current = next;
            }
        }
        if layers.is_empty() {
            return Err(LeanCompileError::unsupported("ReturnedFunction/EmptyCall"));
        }
        Ok(layers)
    }

    /// Continue the original call's actual child/requirement slices. The first
    /// call already supplies membership of its result in the next function set.
    pub(super) fn compile_returned_fn_calls(
        &self,
        application: &FnObj,
        evidence: &FnObjObjWellDefinedProof,
        mut receiver: String,
        mut output: Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj, String), LeanCompileError> {
        let total_args = application.body.iter().map(Vec::len).sum::<usize>();
        let head_offset = evidence
            .child_obj_well_defined
            .len()
            .checked_sub(total_args)
            .ok_or_else(|| LeanCompileError::unsupported("ReturnedFunction/ChildStages"))?;
        let mut child_offset = head_offset + application.body[0].len();
        let mut requirement_offset = evidence.requirement_fact_verified.len();
        // Count the trailing layers to find their actual first requirement.
        let Obj::FunctionSpace(FunctionSpace::FnSet(first_return)) = &output else {
            return Err(LeanCompileError::unsupported(
                "ReturnedFunction/LayerCarrier",
            ));
        };
        let mut space = first_return;
        for index in 1..application.body.len() {
            let count = application.body[index].len() + space.dom_facts.len();
            requirement_offset = requirement_offset.checked_sub(count).ok_or_else(|| {
                LeanCompileError::unsupported("ReturnedFunction/RequirementStages")
            })?;
            if index + 1 < application.body.len() {
                let Obj::FunctionSpace(FunctionSpace::FnSet(next)) = space.ret_set.as_ref() else {
                    return Err(LeanCompileError::unsupported(
                        "ReturnedFunction/LayerCarrier",
                    ));
                };
                space = next;
            }
        }
        for arguments in &application.body[1..] {
            let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &output else {
                return Err(LeanCompileError::unsupported(
                    "ReturnedFunction/LayerCarrier",
                ));
            };
            let parameters = signature
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
                .collect::<Vec<_>>();
            let substitution: HashMap<IdentifierId, Obj> = parameters
                .iter()
                .zip(arguments)
                .map(|((p, _), a)| (p.id, a.as_ref().clone()))
                .collect();
            let mut terms = Vec::new();
            for (index, argument) in arguments.iter().enumerate() {
                let child = &evidence.child_obj_well_defined[child_offset + index];
                ensure_object(argument, child)?;
                terms.push(self.compile_wd(
                    child,
                    &SourcePosition {
                        before: child_offset + index,
                        ..*position
                    },
                )?);
            }
            let mut proofs = Vec::new();
            for index in 0..arguments.len() + signature.dom_facts.len() {
                let proof = &evidence.requirement_fact_verified[requirement_offset + index];
                let subject = source_subject(proof)?;
                if index < arguments.len() {
                    if !matches!(&subject, Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir() == arguments[index].ir() && p.set.ir() == parameters[index].1.ir())
                    {
                        return Err(LeanCompileError::unsupported(
                            "ReturnedFunction/ArgumentMembership",
                        ));
                    }
                } else if !instantiated_fact_matches(
                    &function_guard_fact(&signature.dom_facts[index - arguments.len()])?,
                    &subject,
                    &substitution,
                ) {
                    return Err(LeanCompileError::unsupported(
                        "ReturnedFunction/GuardSubject",
                    ));
                }
                proofs.push(
                    self.compile_verify(
                        proof,
                        &SourcePosition {
                            before: evidence.child_obj_well_defined.len()
                                + requirement_offset
                                + index,
                            ..*position
                        },
                    )?
                    .1,
                );
            }
            child_offset += arguments.len();
            requirement_offset += proofs.len();
            let formed = SourcePosition {
                before: evidence.child_obj_well_defined.len() + requirement_offset,
                ..*position
            };
            let sig = self.compile_fn_signature(signature, &formed)?;
            let (_, guard) =
                self.compile_function_domain_certificates(signature, &terms, &proofs, &formed)?;
            // Packing retains the original argument hosts; the full-domain
            // consumer handles numeric refinements such as R+ separately.
            let (_, packed, _, _) = self.compile_packed_call_arguments(
                signature,
                &terms,
                &proofs[..terms.len()],
                &guard,
                &formed,
            )?;
            let (_, domain) = self.compile_complete_input(signature, &terms, &proofs, &formed)?;
            // Every preceding layer is a generic CallOn. Reuse its own output
            // certificate after binding the receiver, so nested terms stay shared.
            receiver = format!("(by\n  let _returned_receiver := {receiver}\n  let _returned_signature : Litex.FunctionSignature M := {sig}\n  have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := by exact Litex.callOnInOutput _returned_receiver\n  have _returned_domain : M.mem (Litex.denote {packed}) _returned_signature.domain := {domain}\n  exact Litex.callOn _returned_signature _returned_receiver {packed} _returned_member _returned_domain)");
            output = signature.ret_set.as_ref().clone();
        }
        let member = format!("(Litex.callOnInOutput {receiver})");
        Ok((receiver, output, member))
    }
}
