use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Borrow one fixed return interface and count its original obligations.
    fn returned_call_layer<'a>(
        output: &'a Obj,
        arguments: &[Box<Obj>],
    ) -> Result<(usize, &'a Obj), LeanCompileError> {
        let (expected, guards, next) = match output {
            Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => (
                signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum(),
                signature.dom_facts.len(),
                signature.ret_set.as_ref(),
            ),
            Obj::ProductShape(ProductShape::Cart(cart)) => {
                let index = arguments
                    .first()
                    .and_then(|a| {
                        crate::execute::execute_fact_stmt::known_tuple::literal_positive_usize(a)
                    })
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("ReturnedCart/VariableCoordinate")
                    })?;
                let next = cart
                    .args
                    .get(index - 1)
                    .ok_or_else(|| LeanCompileError::unsupported("ReturnedCart/Index"))?;
                (1, 0, next.as_ref())
            }
            _ => {
                let (dimensions, carrier, _) =
                    super::compile_returned_array_call::array_parts(output)?;
                (dimensions.len(), 0, carrier)
            }
        };
        if arguments.len() != expected {
            return Err(LeanCompileError::unsupported("ReturnedFunction/LayerArity"));
        }
        Ok((expected + guards, next))
    }

    /// Validate the selected flat record, including the shared verifier's
    /// checked prefix-interface refinement between two application groups.
    /// No membership or signature is searched for or manufactured here.
    pub(super) fn returned_call_layout(
        application: &FnObj,
        mut output: &Obj,
        requirements: &[VerifyFactResult],
        mut offset: usize,
    ) -> Result<(Vec<(usize, bool)>, usize), LeanCompileError> {
        let mut layers = Vec::new();
        let mut needs_refinement = false;
        for (index, arguments) in application.body.iter().enumerate().skip(1) {
            if needs_refinement {
                let mut prefix = application.clone();
                prefix.body.truncate(index);
                let requirement = requirements.get(offset).ok_or_else(|| {
                    LeanCompileError::unsupported("ReturnedFunction/PrefixMembership")
                })?;
                if !matches!(source_subject(requirement)?, Fact::AtomicFact(AtomicFact::InFact(p))
                    if p.element.ir() == Obj::FnObj(prefix).ir() && p.set.ir() == output.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "ReturnedFunction/PrefixMembership",
                    ));
                }
                offset += 1;
            }
            let (count, next) = Self::returned_call_layer(output, arguments)?;
            layers.push((offset, needs_refinement));
            // The native finite-function signature returns the union of all
            // factors. A further call through a multi-factor Cartesian result
            // therefore retains its checked, more precise prefix membership.
            needs_refinement =
                matches!(output, Obj::ProductShape(ProductShape::Cart(c)) if c.args.len() > 1);
            output = next;
            offset += count;
        }
        Ok((layers, offset))
    }

    /// Read the final carrier from the original signature and complete call shape.
    /// Matrix/finite-sequence wrappers have fixed arity and need no fresh binders.
    pub(in crate::compile_to_lean) fn fixed_function_call_output<'a>(
        application: &FnObj,
        signature: &'a FnSet,
    ) -> Result<&'a Obj, LeanCompileError> {
        let Some(first) = application.body.first() else {
            return Err(LeanCompileError::unsupported("ReturnedFunction/EmptyCall"));
        };
        if first.len()
            != signature
                .set_bound_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum::<usize>()
        {
            return Err(LeanCompileError::unsupported("ReturnedFunction/LayerArity"));
        }
        let mut output = signature.ret_set.as_ref();
        for arguments in &application.body[1..] {
            output = Self::returned_call_layer(output, arguments)?.1;
        }
        Ok(output)
    }

    /// Continue the original call's actual child/requirement slices. The first
    /// call already supplies membership of its result in the next function set.
    pub(super) fn compile_returned_fn_calls(
        &self,
        application: &FnObj,
        evidence: &FnObjObjWellDefinedProof,
        mut receiver: String,
        mut output: Obj,
        mut member: String,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj, String), LeanCompileError> {
        let total_args = application.body.iter().map(Vec::len).sum::<usize>();
        let head_offset = evidence
            .child_obj_well_defined
            .len()
            .checked_sub(total_args)
            .ok_or_else(|| LeanCompileError::unsupported("ReturnedFunction/ChildStages"))?;
        let mut child_offset = head_offset + application.body[0].len();
        let first_requirements = match evidence.domain_fn_set.as_ref() {
            Some(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::InFunctionSet {fn_set, ..}
                | crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::AnonymousLiteral {fn_set}
                | crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::TemplateDefinition {fn_set, ..}) =>
                application.body[0].len() + fn_set.dom_facts.len(),
            Some(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::Matrix(p)) =>
                application.body[0].len() + p.function.body.dom_facts.len(),
            Some(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::Composition(p)) =>
                application.body[0].len() + p.function.body.dom_facts.len(),
            Some(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::MultivariableSelector(p)) =>
                application.body[0].len() + p.signature.dom_facts.len(),
            _ => return Err(LeanCompileError::unsupported("ReturnedFunction/DomainEvidence")),
        };
        let (layers, end) = Self::returned_call_layout(
            application,
            &output,
            &evidence.requirement_fact_verified,
            first_requirements,
        )?;
        if end != evidence.requirement_fact_verified.len() {
            return Err(LeanCompileError::unsupported(
                "ReturnedFunction/RequirementStages",
            ));
        }
        for (layer_index, (arguments, (mut requirement_offset, refined))) in
            application.body[1..].iter().zip(layers).enumerate()
        {
            if refined {
                let earlier_children = SourcePosition {
                    before: child_offset,
                    ..*position
                };
                let prior = SourcePosition::new(
                    Some(&earlier_children),
                    SourceOwner::EqualityRequirements(&evidence.requirement_fact_verified),
                    requirement_offset - 1,
                );
                member = self
                    .compile_verify(
                        &evidence.requirement_fact_verified[requirement_offset - 1],
                        &prior,
                    )?
                    .1;
            }
            if matches!(output, Obj::ProductShape(ProductShape::Cart(_))) {
                let final_layer = layer_index + 2 == application.body.len();
                let (call, carrier, checked) = self.compile_returned_cart_call(
                    application,
                    arguments,
                    evidence,
                    &receiver,
                    &output,
                    &member,
                    child_offset,
                    requirement_offset,
                    final_layer,
                    position,
                )?;
                receiver = call;
                output = carrier;
                member = checked;
                child_offset += arguments.len();
                continue;
            }
            let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &output else {
                let (call, carrier) = self.compile_returned_array_step(
                    arguments,
                    evidence,
                    &receiver,
                    &output,
                    &member,
                    child_offset,
                    requirement_offset,
                    position,
                )?;
                receiver = call;
                output = carrier;
                member = format!("(Litex.callOnInOutput {receiver})");
                child_offset += arguments.len();
                continue;
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
            // Reuse the preceding layer's actual membership certificate.
            // Cartesian projections need their retained coordinate proof.
            receiver = format!(
                "(by\n  let _returned_receiver := {receiver}\n  let _returned_signature : Litex.FunctionSignature M := {sig}\n  have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature)  := {member}\n  have _returned_domain : M.mem (Litex.denote {packed}) _returned_signature.domain := {domain}\n  exact Litex.callOn _returned_signature _returned_receiver {packed} _returned_member _returned_domain)"
            );
            output = signature.ret_set.as_ref().clone();
            member = format!("(Litex.callOnInOutput {receiver})");
        }
        Ok((receiver, output, member))
    }
}
