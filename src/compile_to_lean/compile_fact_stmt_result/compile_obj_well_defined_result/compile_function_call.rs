use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjDomainFnSetEvidence, FnObjObjWellDefinedProof,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_fn_obj_wd(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_fn_call_with_return(application, proof, position)
            .map(|(call, _)| call)
    }

    /// Read the output law from this same certified constructor. This is not a
    /// second return-membership search or a replacement for a selected route.
    pub(in crate::compile_to_lean) fn compile_fn_output_membership(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(StandardSet, String), LeanCompileError> {
        let (call, output) = self.compile_fn_call_with_return(application, proof, position)?;
        let law = if application.body[0].len() == 1 {
            "callInOutput"
        } else {
            "call2InOutput"
        };
        Ok((output, format!("(Litex.{law} {call})")))
    }

    pub(in crate::compile_to_lean) fn compile_fn_call_with_return(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, StandardSet), LeanCompileError> {
        let evidence = proof.domain_fn_set.as_ref().ok_or_else(|| {
            LeanCompileError::new(
                "WD/FnObj/DomainEvidence",
                "The call has no selected domain evidence.",
            )
        })?;
        let signature = match evidence {
            FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
            | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => fn_set,
            _ => return Err(LeanCompileError::unsupported("WD/FnObj/DomainEvidence")),
        };
        let domains = self.compile_function_domains(signature)?;
        let Obj::StandardSet(output) = signature.ret_set.as_ref() else {
            return Err(LeanCompileError::unsupported("Function/ReturnCarrier"));
        };
        if application.body.len() != 1 || application.body[0].len() + 1 != domains.len() {
            return Err(LeanCompileError::new(
                "WD/FnObj/Arity",
                "The call must have one argument group matching its recorded one/two-parameter signature.",
            ));
        }
        let arguments = &application.body[0];
        let (head, head_offset) = match (evidence, application.head.as_ref()) {
            (FnObjDomainFnSetEvidence::InFunctionSet { .. }, FnObjHead::Identifier(identifier)) => {
                (Obj::Identifier(identifier.clone()), 0)
            }
            (
                FnObjDomainFnSetEvidence::AnonymousLiteral { .. },
                FnObjHead::AnonymousFnLiteral(function),
            ) => {
                if &function.body != signature {
                    return Err(LeanCompileError::new(
                        "WD/FnObj/Signature",
                        "The selected literal signature differs from its actual source function.",
                    ));
                }
                (
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone())),
                    1,
                )
            }
            _ => return Err(LeanCompileError::unsupported("WD/FnObj/HeadEvidence")),
        };
        let child_count = arguments.len() + head_offset;
        if proof.child_obj_well_defined.len() != child_count
            || proof.requirement_fact_verified.len() != arguments.len() + signature.dom_facts.len()
        {
            return Err(LeanCompileError::new(
                "WD/FnObj/StageArity",
                "The call does not own all ordered argument WD, memberships, and guard stages.",
            ));
        }

        let head_term = if head_offset == 1 {
            ensure_object(&head, &proof.child_obj_well_defined[0])?;
            self.compile_wd(
                &proof.child_obj_well_defined[0],
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?
        } else {
            self.compile_object_reference(
                &head,
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?
        };
        let mut argument_terms = Vec::new();
        for (index, argument) in arguments.iter().enumerate() {
            let child_index = head_offset + index;
            ensure_object(argument, &proof.child_obj_well_defined[child_index])?;
            argument_terms.push(self.compile_wd(
                &proof.child_obj_well_defined[child_index],
                &SourcePosition {
                    before: child_index,
                    ..*position
                },
            )?);
        }

        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(|parameter| (parameter, group.param_type.as_ref()))
            })
            .collect();
        let substitution: HashMap<IdentifierId, Obj> = parameters
            .iter()
            .zip(arguments)
            .map(|((parameter, _), argument)| (parameter.id, argument.as_ref().clone()))
            .collect();
        let mut requirement_terms = Vec::new();
        for (index, requirement) in proof.requirement_fact_verified.iter().enumerate() {
            let subject = source_subject(requirement)?;
            if index < arguments.len() {
                if !matches!(&subject, Fact::AtomicFact(AtomicFact::InFact(member))
                    if member.element.ir() == arguments[index].ir()
                        && member.set.ir() == parameters[index].1.ir())
                {
                    return Err(LeanCompileError::new(
                        "WD/FnObj/ParameterMembership",
                        "The ordered parameter requirement has another argument or domain.",
                    ));
                }
            } else {
                let QuantifierFreeFact::AtomicFact(guard) =
                    &signature.dom_facts[index - arguments.len()]
                else {
                    return Err(LeanCompileError::unsupported("Function/CompoundGuard"));
                };
                if !instantiated_fact_matches(
                    &Fact::AtomicFact(guard.clone()),
                    &subject,
                    &substitution,
                ) {
                    return Err(LeanCompileError::new(
                        "WD/FnObj/GuardSubject",
                        "The guard proof is not the recorded clause instantiated at these arguments.",
                    ));
                }
            }
            requirement_terms.push(
                self.compile_verify(
                    requirement,
                    &SourcePosition {
                        before: child_count + index,
                        ..*position
                    },
                )?
                .1,
            );
        }
        let formed = SourcePosition {
            before: child_count + proof.requirement_fact_verified.len(),
            ..*position
        };
        let compiled_signature = self.compile_fn_signature(signature, &formed)?;
        let guard = self.compile_function_guard_template(signature, &formed)?;
        let membership = match evidence {
            FnObjDomainFnSetEvidence::AnonymousLiteral { .. } => {
                format!("(Litex.formulaFnInFnSet {head_term})")
            }
            FnObjDomainFnSetEvidence::InFunctionSet {
                fact_id,
                function_equal,
                ..
            } => {
                let (source, citation) = self.cited_fact_reference(*fact_id, &formed)?;
                if *source != self.resolve_fact(*fact_id, &formed)? {
                    return Err(LeanCompileError::new(
                        "WD/FnObj/CitationProducer",
                        "The selected citation differs from its active original producer.",
                    ));
                }
                let space = format!("(Litex.fnSet {compiled_signature})");
                match source {
                    Fact::AtomicFact(AtomicFact::InFact(member)) if member.fact_id == *fact_id => {
                        let Obj::FunctionSpace(FunctionSpace::FnSet(source_signature)) =
                            &member.set
                        else {
                            return Err(LeanCompileError::unsupported("WD/FnObj/CitationCarrier"));
                        };
                        if source_signature != signature {
                            return Err(LeanCompileError::new(
                                "WD/FnObj/Signature",
                                "The selected signature differs from the source membership citation.",
                            ));
                        }
                        let path = self.compile_equality_path(
                            &head,
                            &member.element,
                            function_equal,
                            &formed,
                        )?;
                        if function_equal.path.is_empty() {
                            citation
                        } else {
                            let source_head =
                                self.compile_object_reference(&member.element, &formed)?;
                            format!("(Litex.inOfSame {source_head} {head_term} {space} {space} ({path}).symm (Litex.sameRefl {space}) {citation})")
                        }
                    }
                    Fact::AtomicFact(AtomicFact::EqualFact(equal)) if equal.fact_id == *fact_id => {
                        let (literal, source_head, oriented) = match (&equal.left, &equal.right) {
                            (Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)), other) => {
                                (function, other, citation)
                            }
                            (other, Obj::FunctionSpace(FunctionSpace::AnonymousFn(function))) => {
                                (function, other, format!("({citation}).symm"))
                            }
                            _ => {
                                return Err(LeanCompileError::unsupported(
                                    "WD/FnObj/EqualityCitation",
                                ))
                            }
                        };
                        if &literal.body != signature {
                            return Err(LeanCompileError::new(
                                "WD/FnObj/Signature",
                                "The selected signature differs from its cited anonymous function.",
                            ));
                        }
                        let path = self.compile_equality_path(
                            &head,
                            source_head,
                            function_equal,
                            &formed,
                        )?;
                        let literal_object =
                            Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal.clone()));
                        // Resolve only a preceding original constructor of this exact literal.
                        let literal_term =
                            self.compile_object_reference(&literal_object, &formed)?;
                        let equality = format!("(({oriented}).trans (({path}).symm))");
                        format!("(Litex.inOfSame {literal_term} {head_term} {space} {space} {equality} (Litex.sameRefl {space}) (Litex.formulaFnInFnSet {literal_term}))")
                    }
                    _ => return Err(LeanCompileError::unsupported("WD/FnObj/CitationSubject")),
                }
            }
            _ => return Err(LeanCompileError::unsupported("WD/FnObj/DomainEvidence")),
        };
        let guard_proofs = &requirement_terms[arguments.len()..];
        let guard_proof = guard_proofs
            .iter()
            .rev()
            .cloned()
            .reduce(|tail, head| format!("(And.intro {head} {tail})"))
            .unwrap_or_else(|| "True.intro".into());
        let constructor = if arguments.len() == 1 {
            "call"
        } else {
            "call2"
        };
        Ok((
            format!(
                "(Litex.{constructor} {} {guard} {head_term} {} {membership} {} {guard_proof})",
                domains.join(" "),
                argument_terms.join(" "),
                requirement_terms[..arguments.len()].join(" ")
            ),
            output.clone(),
        ))
    }
}
