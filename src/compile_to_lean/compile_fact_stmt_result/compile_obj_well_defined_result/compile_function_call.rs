use crate::compile_to_lean::compile_function_template::function_guard_fact;
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
        if let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) = &proof.domain_fn_set {
            return self.compile_finite_fn_call(application, proof, finite, position);
        }
        self.compile_fn_call(application, proof, position)
            .map(|(call, _, _)| call)
    }

    /// Read the output law from this same certified constructor. This is not a
    /// second return-membership search or a replacement for a selected route.
    pub(in crate::compile_to_lean) fn compile_fn_output_membership(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(StandardSet, String), LeanCompileError> {
        if let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) = &proof.domain_fn_set {
            return self.compile_finite_numeric_output(application, proof, finite, position);
        }
        let (_, output, member) = self.compile_fn_call(application, proof, position)?;
        let output = self.compile_numeric_carrier(&output, position)?;
        Ok((output, member))
    }

    fn compile_call_output_proof(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        call: &str,
    ) -> Result<String, LeanCompileError> {
        // These codomain-rule consumers still describe one signature. A
        // returned coordinate uses the layer-specific member from compile_fn_call.
        if application.body.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "FunctionReturn/LayeredSignature",
            ));
        }
        let signature = match &proof.domain_fn_set {
            Some(
                FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set },
            ) => fn_set,
            _ => return Err(LeanCompileError::unsupported("Function/OutputSignature")),
        };
        let law = if !self.function_uses_numeric_interface(signature) {
            "callOnInOutput"
        } else if application.body[0].len() == 1 {
            "callInOutput"
        } else {
            "call2InOutput"
        };
        Ok(format!("(Litex.{law} {call})"))
    }

    pub(in crate::compile_to_lean) fn compile_fn_call_with_return(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, StandardSet), LeanCompileError> {
        if let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) = &proof.domain_fn_set {
            let call = self.compile_finite_fn_call(application, proof, finite, position)?;
            let (output, _) =
                self.compile_finite_numeric_output(application, proof, finite, position)?;
            return Ok((call, output));
        }
        let (call, output, _) = self.compile_fn_call(application, proof, position)?;
        Ok((call, self.compile_numeric_carrier(&output, position)?))
    }

    fn compile_fn_call(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj, String), LeanCompileError> {
        let (call, output, member) =
            self.compile_fn_first_call_with_member(application, proof, position)?;
        if application.body.len() == 1 {
            return Ok((call, output, member));
        }
        self.compile_returned_cart_call(
            application,
            proof,
            &call,
            &output,
            &member,
            proof.child_obj_well_defined.len() - 1,
            proof.requirement_fact_verified.len() - 1,
            position,
        )
    }

    /// Borrow the first application stage from the actual complete call WD.
    /// Its remaining coordinate stage is retained and checked by the caller;
    /// this view never creates a replacement one-group WD result.
    pub(in crate::compile_to_lean) fn compile_fn_first_call_with_member(
        &self,
        application: &FnObj,
        proof: &FnObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Obj, String), LeanCompileError> {
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
        let parameter_count: usize = signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|group| group.params.len())
            .sum();
        let output = signature.ret_set.as_ref().clone();
        if application.body.is_empty() || application.body[0].len() != parameter_count {
            return Err(LeanCompileError::new(
                "WD/FnObj/Arity",
                "The first argument group must match its recorded signature.",
            ));
        }
        // A Cartesian return is itself a finite function. The original WD
        // stores the second group's child and domain check after the first
        // group's evidence; consume those slices without fabricating a WD.
        let returned_coordinate = application.body.len() > 1;
        if returned_coordinate
            && (application.body.len() != 2
                || application.body[1].len() != 1
                || !matches!(&output, Obj::ProductShape(ProductShape::Cart(_))))
        {
            return Err(LeanCompileError::unsupported(
                "WD/FnObj/ReturnedFunctionShape",
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
        let first_child_count = arguments.len() + head_offset;
        let child_count = first_child_count + usize::from(returned_coordinate);
        let first_requirement_count = arguments.len() + signature.dom_facts.len();
        if proof.child_obj_well_defined.len() != child_count
            || proof.requirement_fact_verified.len()
                != first_requirement_count + usize::from(returned_coordinate)
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
        for (index, requirement) in proof.requirement_fact_verified[..first_requirement_count]
            .iter()
            .enumerate()
        {
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
                let guard = function_guard_fact(&signature.dom_facts[index - arguments.len()])?;
                if !instantiated_fact_matches(&guard, &subject, &substitution) {
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
            before: child_count + first_requirement_count,
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
        let (members, guard_proof) = self.compile_function_domain_certificates(
            signature,
            &argument_terms,
            &requirement_terms,
            &formed,
        )?;
        if !self.function_uses_numeric_interface(signature) {
            // The packed argument, its sethood and its domain all use the
            // same checked children. Bind each source argument separately;
            // nested calls must not be expanded at every use of the tuple.
            let local_arguments = (0..argument_terms.len())
                .map(|index| format!("_litex_call_arg_{index}"))
                .collect::<Vec<_>>();
            let bindings = local_arguments
                .iter()
                .zip(&argument_terms)
                .map(|(name, term)| format!("{name} := {term}"))
                .collect::<Vec<_>>()
                .join(";\nlet ");
            let (domain, argument, base_member, packed_guard_proof) = self
                .compile_packed_call_arguments(
                    signature,
                    &local_arguments,
                    &members,
                    &guard_proof,
                    &formed,
                )?;
            let output_set = self.compile_object_reference(&signature.ret_set, &formed)?;
            let packed_guard = self.compile_function_packed_guard_template(signature, &formed)?;
            let call = format!(
                "(let {bindings};\nLitex.callOnDomain {domain} {output_set} {packed_guard} {head_term} {argument} {membership} {base_member} {packed_guard_proof})"
            );
            let member = format!("(Litex.callOnInOutput {call})");
            return Ok((call, output, member));
        }
        let (constructor_arguments, target) =
            self.compile_function_constructor_arguments(signature, &formed)?;
        let constructor = match (arguments.len() == 1, target) {
            (true, false) => "call",
            (false, false) => "call2",
            (true, true) => "callTarget",
            (false, true) => "call2Target",
        };
        let call = format!(
            "(Litex.{constructor} {} {guard} {head_term} {} {membership} {} {guard_proof})",
            constructor_arguments,
            argument_terms.join(" "),
            members.join(" ")
        );
        let law = if arguments.len() == 1 {
            "callInOutput"
        } else {
            "call2InOutput"
        };
        let member = format!("(Litex.{law} {call})");
        Ok((call, output, member))
    }

    fn compile_packed_call_arguments(
        &self,
        signature: &FnSet,
        arguments: &[String],
        members: &[String],
        guard: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, String), LeanCompileError> {
        let sets = self.compile_function_input_sets(signature, position)?;
        if sets.len() != arguments.len() || sets.len() != members.len() {
            return Err(LeanCompileError::new(
                "Function/PackedDomain",
                "Every source argument needs its own ordered carrier certificate.",
            ));
        }
        let (domain, packed, base_member) = if arguments.len() == 1 {
            (sets[0].clone(), arguments[0].clone(), members[0].clone())
        } else {
            let values = arguments
                .iter()
                .map(|argument| format!("(Litex.denote {argument})"))
                .collect::<Vec<_>>()
                .join(", ");
            let set_values = sets
                .iter()
                .map(|set| format!("(Litex.denote {set})"))
                .collect::<Vec<_>>()
                .join(", ");
            let set_wd = sets
                .iter()
                .map(|set| format!("exact Litex.isSet {set}"))
                .collect::<Vec<_>>()
                .join("\n  · ");
            let wd = arguments
                .iter()
                .map(|argument| format!("exact Litex.isSet {argument}"))
                .collect::<Vec<_>>()
                .join("\n  · ");
            let membership = members
                .iter()
                .map(|member| format!("exact {member}"))
                .collect::<Vec<_>>()
                .join("\n  · ");
            (format!("(Litex.cart (M := M) ![{set_values}] (by\n  intro i\n  fin_cases i\n  · {set_wd}))"),
                format!("(Litex.tuple (M := M) ![{values}] (by\n  intro i\n  fin_cases i\n  · {wd}))"),
                format!("(Litex.FiniteFunction.tuple_inCart (M := M) ![{values}] ![{set_values}] (by\n  intro i\n  fin_cases i\n  · {membership}))"))
        };
        let guard_proof = if signature.dom_facts.is_empty() {
            "True.intro".to_string()
        } else if arguments.len() == 1 {
            guard.to_string()
        } else {
            let values = arguments
                .iter()
                .map(|argument| format!("(Litex.denote {argument})"))
                .collect::<Vec<_>>();
            let raw_guard = self.compile_function_guard_template(signature, position)?;
            let equality =
                self.compile_function_packed_application_equality(&raw_guard, &values)?;
            format!("(Eq.mpr {equality} {guard})")
        };
        Ok((domain, packed, base_member, guard_proof))
    }
}

use crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    FnApplicationInCodomainKnownSpecialPropertyProof, InFactSearchProofByKnownSpecialProperty,
    SignatureCodomainUseProof,
};
use crate::compile_to_lean::source_position::SourceOwner;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_fn_return_rule(
        &self,
        goal: &InFact,
        rule: &InFactSearchProofByKnownSpecialProperty,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let InFactSearchProofByKnownSpecialProperty::KnownSubsetMembership(proof) = rule {
            return self.compile_known_subset_member(goal, proof, position);
        }
        if let InFactSearchProofByKnownSpecialProperty::TupleCoordinate(proof) = rule {
            return self.compile_tuple_coordinate_member(goal, proof, position);
        }
        if let InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(proof) = rule {
            return self.compile_fn_return_codomain(goal, proof, position);
        }
        let proof = position.with_visible_wd(&goal.element, &mut |wd, producer| {
            let ObjWellDefinedProof::ByDef {
                obj: Obj::FnObj(application),
                proof: ObjWellDefinedProofByDef::FnObj(evidence),
            } = wd else {
                return Err(LeanCompileError::new("FunctionReturn/WDSubject", "The original constructor is not this function application."));
            };
            let ctor_position = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
            let call = self.compile_fn_obj_wd(application, evidence, &ctor_position)?;
            let selected = evidence.domain_fn_set.as_ref().ok_or_else(|| LeanCompileError::new("FunctionReturn/DomainEvidence", "The original call has no domain source."))?;
            let (selected_signature, selected_id) = match selected {
                FnObjDomainFnSetEvidence::InFunctionSet { fn_set, fact_id, .. } => (fn_set, Some(*fact_id)),
                FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => (fn_set, None),
                _ => return Err(LeanCompileError::unsupported("FunctionReturn/DomainEvidence")),
            };
            let head = match application.head.as_ref() {
                FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
                FnObjHead::AnonymousFnLiteral(function) => Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone())),
                _ => return Err(LeanCompileError::unsupported("FunctionReturn/Head")),
            };
            let head_term = self.compile_object_reference(&head, position)?;
            match rule {
                InFactSearchProofByKnownSpecialProperty::AnonymousFnApplicationInCodomain(p) => {
                    if selected_id.is_some() || p.signature != *selected_signature || p.applied_return_set != *selected_signature.ret_set {
                        return Err(LeanCompileError::new("FunctionReturn/LiteralSignature", "The literal return payload differs from the actual owned call signature."));
                    }
                    let equality = self.compile_fn_return_set_match(&p.applied_return_set, &goal.set, &p.return_set_match, position)?;
                    let member = self.compile_call_output_proof(application, evidence, &call)?;
                    let source_set = self.compile_object_reference(&p.applied_return_set, position)?;
                    let target_set = self.compile_object_reference(&goal.set, position)?;
                    Ok(format!("(Litex.inOfSame {call} {call} {source_set} {target_set} (Litex.sameRefl {call}) {equality} {member})"))
                }
                InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(p) => {
                    let target = self.compile_numeric_carrier(&goal.set, position)?;
                    let target = &target;
                    if &p.target_set != target || p.signature_returns.is_empty() {
                        return Err(LeanCompileError::new("FunctionReturn/SupersetTarget", "The recorded upper bound differs from the goal or has no source signatures."));
                    }
                    let mut ids = Vec::new();
                    let mut anchored = false;
                    let mut strict = false;
                    for entry in &p.signature_returns {
                        if ids.contains(&entry.cite_signature_fact_id) {
                            return Err(LeanCompileError::new("FunctionReturn/DuplicateSignature", "The return payload repeats a source citation."));
                        }
                        ids.push(entry.cite_signature_fact_id);
                        let (signature, _) = self.compile_fn_return_citation(entry.cite_signature_fact_id, &head, &head_term, Some(&entry.function_equal), position)?;
                        if self.compile_numeric_carrier(&signature.ret_set, position)? != entry.source_set {
                            return Err(LeanCompileError::new("FunctionReturn/SourceCarrier", "The recorded source upper bound differs from its exact signature citation."));
                        }
                        fn_return_bridge(&entry.source_set, target)?;
                        strict |= entry.source_set != *target;
                        if selected_id == Some(entry.cite_signature_fact_id) {
                            if signature != selected_signature {
                                return Err(LeanCompileError::new("FunctionReturn/SelectedSignature", "The payload's source differs from the original constructor's selected signature."));
                            }
                            anchored = true;
                        }
                    }
                    if !anchored || !strict {
                        return Err(LeanCompileError::new("FunctionReturn/SelectedSignature", "The recorded strict-inclusion route does not cover the actual constructor's selected source."));
                    }
                    let (source, member) = self.compile_fn_output_membership(application, evidence, &ctor_position)?;
                    lift_fn_return(&call, &source, target, &member)
                }
                _ => Err(LeanCompileError::unsupported("FunctionReturn/KnownRule")),
            }
        })?;
        proof.ok_or_else(|| {
            LeanCompileError::new(
                "FunctionReturn/Producer",
                "No earlier original call constructor supplies this return proof.",
            )
        })
    }

    /// Consume the original codomain payload without requiring its goal to
    /// have been published as a fact; its signature citations remain checked.
    pub(in crate::compile_to_lean) fn compile_fn_return_codomain(
        &self,
        goal: &InFact,
        p: &FnApplicationInCodomainKnownSpecialPropertyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let proof = position.with_visible_wd(&goal.element, &mut |wd, producer| {
            let ObjWellDefinedProof::ByDef {
                obj: Obj::FnObj(application),
                proof: ObjWellDefinedProofByDef::FnObj(evidence),
            } = wd else {
                return Err(LeanCompileError::new("FunctionReturn/WDSubject", "The original constructor is not this function application."));
            };
            let ctor_position = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
            let call = self.compile_fn_obj_wd(application, evidence, &ctor_position)?;
            let selected = evidence.domain_fn_set.as_ref().ok_or_else(|| LeanCompileError::new("FunctionReturn/DomainEvidence", "The original call has no domain source."))?;
            let (selected_signature, selected_id, selected_path) = match selected {
                FnObjDomainFnSetEvidence::InFunctionSet { fn_set, fact_id, function_equal } => (fn_set, Some(*fact_id), Some(function_equal)),
                FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => (fn_set, None, None),
                _ => return Err(LeanCompileError::unsupported("FunctionReturn/DomainEvidence")),
            };
            let head = match application.head.as_ref() {
                FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
                FnObjHead::AnonymousFnLiteral(function) => Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone())),
                _ => return Err(LeanCompileError::unsupported("FunctionReturn/Head")),
            };
            let head_term = self.compile_object_reference(&head, position)?;
            let (main_signature, main_member) = self.compile_fn_return_citation(p.cite_property_fact_id, &head, &head_term, Some(&p.function_equal), position)?;
            let mut ids = Vec::new();
            let mut main_match = None;
            let mut selected_match = None;
            let mut selected_same_domains = false;
            for entry in &p.signature_uses {
                let (id, path) = match entry {
                    SignatureCodomainUseProof::ReturnSetMatch(entry) => (entry.cite_signature_fact_id, if entry.cite_signature_fact_id == p.cite_property_fact_id { Some(&p.function_equal) } else if selected_id == Some(entry.cite_signature_fact_id) { selected_path } else { None }),
                    SignatureCodomainUseProof::SameCallDomains { cite_signature_fact_id, function_equal, .. } => (*cite_signature_fact_id, Some(function_equal)),
                };
                if ids.contains(&id) {
                    return Err(LeanCompileError::new("FunctionReturn/DuplicateSignature", "The return payload repeats a source citation."));
                }
                ids.push(id);
                let (signature, _) = self.compile_fn_return_citation(id, &head, &head_term, path, position)?;
                match entry {
                    SignatureCodomainUseProof::ReturnSetMatch(entry) => {
                        let equality = self.compile_fn_return_set_match(&signature.ret_set, &goal.set, &entry.return_set_match, position)?;
                        if id == p.cite_property_fact_id { main_match = Some(equality.clone()); }
                        if selected_id == Some(id) {
                            if signature != selected_signature {
                                return Err(LeanCompileError::new("FunctionReturn/SelectedSignature", "The actual constructor signature differs from its source return row."));
                            }
                            selected_match = Some(equality);
                        }
                    }
                    SignatureCodomainUseProof::SameCallDomains { domains, .. } => {
                        if domains.layers.len() != 1 || domains.layers[0].return_carriers.is_some()
                            || &domains.layers[0].selected != main_signature
                            || &domains.layers[0].alternative != signature
                            || !function_domains_alpha_equal(main_signature, signature)
                        {
                            return Err(LeanCompileError::new("FunctionReturn/SameDomains", "The recorded one-layer domains do not match these exact source signatures."));
                        }
                        if selected_id == Some(id) {
                            if signature != selected_signature {
                                return Err(LeanCompileError::new("FunctionReturn/SelectedSignature", "The same-domain row differs from the original selected source."));
                            }
                            selected_same_domains = true;
                        }
                    }
                }
            }
            let main_match = main_match.ok_or_else(|| LeanCompileError::new("FunctionReturn/SelectedSignature", "The chosen return source has no recorded return-set match."))?;
            let (source_set, equality, member) = if let Some(equality) = selected_match {
                let member = self.compile_call_output_proof(application, evidence, "_litex_return_call")?;
                (selected_signature.ret_set.as_ref(), equality, member)
            } else if selected_same_domains {
                let (packed, domain) = self.compile_fn_return_domain(application, evidence, main_signature, &ctor_position)?;
                let signature = self.compile_fn_signature(main_signature, position)?;
                let member = format!("(Litex.FunctionSemantics.call_mem (M := M) (Litex.FunctionSignature.domain {signature}) (Litex.FunctionSignature.target {signature}) (Litex.denote {head_term}) {packed} {main_member} {domain})");
                (main_signature.ret_set.as_ref(), main_match, member)
            } else {
                return Err(LeanCompileError::new("FunctionReturn/SelectedSignature", "The return payload does not cover the actual constructor's selected signature."));
            };
            let source_set = self.compile_object_reference(source_set, position)?;
            let target_set = self.compile_object_reference(&goal.set, position)?;
            // The exact checked call supplies all three equality endpoints
            // and the output law. Elaborate its constructor once locally.
            Ok(format!("(by\n  let _litex_return_call := {call}\n  exact Litex.inOfSame _litex_return_call _litex_return_call {source_set} {target_set} (Litex.sameRefl _litex_return_call) {equality} {member})"))
        })?;
        proof.ok_or_else(|| {
            LeanCompileError::new(
                "FunctionReturn/Producer",
                "No earlier original call constructor supplies this return proof.",
            )
        })
    }

    pub(in crate::compile_to_lean) fn compile_fn_return_builtin(
        &self,
        goal: &InFact,
        rule: &InFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let target = self.compile_numeric_carrier(&goal.set, position)?;
        let target = &target;
        match rule {
            InFactSearchProofByBuiltinRule::AnonymousFnApplicationScalarCodomain(p) => {
                position.with_visible_wd(&goal.element, &mut |wd, producer| {
                    let ObjWellDefinedProof::ByDef { obj: Obj::FnObj(application), proof: ObjWellDefinedProofByDef::FnObj(evidence) } = wd else {
                        return Err(LeanCompileError::new("FunctionReturn/WDSubject", "The source constructor is not the recorded application."));
                    };
                    let FnObjHead::AnonymousFnLiteral(literal) = application.head.as_ref() else {
                        return Err(LeanCompileError::new("FunctionReturn/LiteralSubject", "The scalar literal rule has another function head."));
                    };
                    if self.compile_numeric_carrier(&literal.body.ret_set, position)? != p.codomain
                        || !matches!(&evidence.domain_fn_set, Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }) if fn_set == &literal.body)
                    {
                        return Err(LeanCompileError::new("FunctionReturn/LiteralSignature", "The literal scalar codomain differs from the actual source signature."));
                    }
                    let ctor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                    let call = self.compile_fn_obj_wd(application, evidence, &ctor)?;
                    let (output, member) = self.compile_fn_output_membership(application, evidence, &ctor)?;
                    lift_fn_return(&call, &output, target, &member)
                })?.ok_or_else(|| LeanCompileError::new("FunctionReturn/Producer", "No original literal call constructor supplies this scalar codomain."))
            }
            InFactSearchProofByBuiltinRule::StandardSetSubsetMembership(p) => {
                if p.source_set == *target || !matches!(&goal.element, Obj::FnObj(_)) {
                    return Err(LeanCompileError::new("FunctionReturn/SubsetSubject", "The subset route must be a proper numeric inclusion for this call."));
                }
                let subject = source_subject(&p.source_membership_proof)?;
                if !matches!(&subject, Fact::AtomicFact(AtomicFact::InFact(source)) if source.element.ir() == goal.element.ir() && source.set == Obj::StandardSet(p.source_set.clone())) {
                    return Err(LeanCompileError::new("FunctionReturn/SubsetSubject", "The child membership differs from the same call and recorded source carrier."));
                }
                let proof = self.compile_verify(&p.source_membership_proof, position)?.1;
                let call = self.compile_object_reference(&goal.element, position)?;
                lift_fn_return(&call, &p.source_set, target, &proof)
            }
            _ => Err(LeanCompileError::unsupported("FunctionReturn/BuiltinRule")),
        }
    }

    fn compile_fn_return_citation<'p>(
        &'p self,
        id: FactId,
        head: &Obj,
        head_term: &str,
        path: Option<&KnownEqualityPathProof>,
        position: &SourcePosition<'p>,
    ) -> Result<(&'p FnSet, String), LeanCompileError> {
        let (source, citation) = self.cited_fact_reference(id, position)?;
        if source.fact_id() != id || *source != self.resolve_fact(id, position)? {
            return Err(LeanCompileError::new(
                "FunctionReturn/Citation",
                "The signature citation differs from its original source producer.",
            ));
        }
        let (signature, subject, literal, oriented) = match source {
            Fact::AtomicFact(AtomicFact::InFact(member)) => {
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
                    return Err(LeanCompileError::unsupported(
                        "FunctionReturn/CitationCarrier",
                    ));
                };
                (signature, &member.element, None, citation)
            }
            Fact::AtomicFact(AtomicFact::EqualFact(equal)) => match (&equal.left, &equal.right) {
                (Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)), subject) => {
                    (&literal.body, subject, Some(literal), citation)
                }
                (subject, Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal))) => (
                    &literal.body,
                    subject,
                    Some(literal),
                    format!("({citation}).symm"),
                ),
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "FunctionReturn/EqualityCitation",
                    ))
                }
            },
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FunctionReturn/CitationSubject",
                ))
            }
        };
        let head_equality = if let Some(path) = path {
            format!(
                "({}).symm",
                self.compile_equality_path(head, subject, path, position)?
            )
        } else {
            if head.ir() != subject.ir() {
                return Err(LeanCompileError::new("FunctionReturn/UnrecordedHeadTransport", "An alternative signature needs its recorded head equality or exact subject identity."));
            }
            format!("(Litex.sameRefl {head_term})")
        };
        let space = format!(
            "(Litex.fnSet {})",
            self.compile_fn_signature(signature, position)?
        );
        let (source_term, equality, member) = if let Some(literal) = literal {
            let object = Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal.clone()));
            let term = self.compile_object_reference(&object, position)?;
            (
                term.clone(),
                format!("(({oriented}).trans {head_equality})"),
                format!("(Litex.formulaFnInFnSet {term})"),
            )
        } else {
            (
                self.compile_object_reference(subject, position)?,
                head_equality,
                oriented,
            )
        };
        Ok((signature, format!("(Litex.inOfSame {source_term} {head_term} {space} {space} {equality} (Litex.sameRefl {space}) {member})")))
    }

    pub(in crate::compile_to_lean) fn compile_fn_return_set_match(
        &self,
        source: &Obj,
        target: &Obj,
        proof: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                if source.ir() == target.ir() =>
            {
                Ok(format!(
                    "(Litex.sameRefl {})",
                    self.compile_object_reference(source, position)?
                ))
            }
            EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) => self.compile_equality_path(source, target, path, position),
            _ => Err(LeanCompileError::unsupported(
                "FunctionReturn/ReturnSetMatch",
            )),
        }
    }

    fn compile_fn_return_domain(
        &self,
        application: &FnObj,
        evidence: &FnObjObjWellDefinedProof,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let arguments = &application.body[0];
        let offset = usize::from(matches!(
            evidence.domain_fn_set,
            Some(FnObjDomainFnSetEvidence::AnonymousLiteral { .. })
        ));
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|p| (p, group.param_type.as_ref())))
            .collect();
        if parameters.len() != arguments.len()
            || evidence.requirement_fact_verified.len()
                != parameters.len() + signature.dom_facts.len()
        {
            return Err(LeanCompileError::new(
                "FunctionReturn/DomainStages",
                "The alternate signature has different argument or guard stages.",
            ));
        }
        let substitution: HashMap<IdentifierId, Obj> = parameters
            .iter()
            .zip(arguments)
            .map(|((parameter, _), arg)| (parameter.id, arg.as_ref().clone()))
            .collect();
        let mut terms = Vec::new();
        for (index, argument) in arguments.iter().enumerate() {
            let child = &evidence.child_obj_well_defined[offset + index];
            ensure_object(argument, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: offset + index,
                    ..*position
                },
            )?);
        }
        let mut proofs = Vec::new();
        for (index, requirement) in evidence.requirement_fact_verified.iter().enumerate() {
            let subject = source_subject(requirement)?;
            if index < parameters.len() {
                if !matches!(&subject, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == arguments[index].ir() && f.set.ir() == parameters[index].1.ir())
                {
                    return Err(LeanCompileError::new("FunctionReturn/DomainSubject", "The original argument membership does not meet this recorded alternate domain."));
                }
            } else {
                let guard = function_guard_fact(&signature.dom_facts[index - parameters.len()])?;
                if !instantiated_fact_matches(&guard, &subject, &substitution) {
                    return Err(LeanCompileError::new("FunctionReturn/DomainSubject", "The original guard proof does not meet the source return signature at these arguments."));
                }
            }
            proofs.push(
                self.compile_verify(
                    requirement,
                    &SourcePosition {
                        before: evidence.child_obj_well_defined.len() + index,
                        ..*position
                    },
                )?
                .1,
            );
        }
        let guard = self.compile_function_guard_template(signature, position)?;
        let (members, guard_proof) =
            self.compile_function_domain_certificates(signature, &terms, &proofs, position)?;
        if !self.function_uses_numeric_interface(signature) {
            let (domain, packed, base_member, packed_guard_proof) = self
                .compile_packed_call_arguments(
                    signature,
                    &terms,
                    &members,
                    &guard_proof,
                    position,
                )?;
            let output = self.compile_object_reference(&signature.ret_set, position)?;
            let packed_guard = self.compile_function_packed_guard_template(signature, position)?;
            let proof = format!("((Litex.FunctionSignature.withGuard_domain (Litex.denote {domain}) (Litex.denote {output}) (Litex.isSet {domain}) (Litex.isSet {output}) {packed_guard} (Litex.denote {packed})).mpr ⟨{base_member}, {packed_guard_proof}⟩)");
            return Ok((format!("(Litex.denote {packed})"), proof));
        }
        let (constructor_arguments, target) =
            self.compile_function_constructor_arguments(signature, position)?;
        let (packed, inputs, conjunction, law) = if terms.len() == 1 {
            (
                format!("(Litex.denote {})", terms[0]),
                format!("(Litex.denote {})", terms[0]),
                format!("⟨{}, {guard_proof}⟩", members[0]),
                if target {
                    "oneTarget_domain"
                } else {
                    "one_domain"
                },
            )
        } else {
            (
                format!(
                    "(Litex.FiniteFunction.pack2 (M := M) (Litex.denote {}) (Litex.denote {}))",
                    terms[0], terms[1]
                ),
                format!("(Litex.denote {}) (Litex.denote {})", terms[0], terms[1]),
                format!("⟨{}, {}, {guard_proof}⟩", members[0], members[1]),
                if target {
                    "twoTarget_domain"
                } else {
                    "two_domain"
                },
            )
        };
        Ok((
            packed,
            format!(
                "((Litex.FunctionSignature.{law} {} {guard} {inputs}).mpr {conjunction})",
                constructor_arguments
            ),
        ))
    }
}

fn fn_return_bridge(
    source: &StandardSet,
    target: &StandardSet,
) -> Result<Option<&'static str>, LeanCompileError> {
    if source == target {
        return Ok(None);
    }
    let bridge = match (source, target) {
        (StandardSet::N, StandardSet::Z) => "naturalToInteger",
        (StandardSet::N, StandardSet::Q) => "naturalToRational",
        (StandardSet::N, StandardSet::R) => "naturalToReal",
        (StandardSet::N, StandardSet::C) => "naturalToComplex",
        (StandardSet::Z, StandardSet::Q) => "integerToRational",
        (StandardSet::Z, StandardSet::R) => "integerToReal",
        (StandardSet::Z, StandardSet::C) => "integerToComplex",
        (StandardSet::Q, StandardSet::R) => "rationalToReal",
        (StandardSet::Q, StandardSet::C) => "rationalToComplex",
        (StandardSet::R, StandardSet::C) => "realToComplex",
        (StandardSet::RPos, StandardSet::R) => "inRPos_real",
        (StandardSet::RPos, StandardSet::C) => "positiveRealToComplex",
        _ => {
            return Err(LeanCompileError::unsupported(
                "FunctionReturn/StandardInclusion",
            ))
        }
    };
    Ok(Some(bridge))
}

fn lift_fn_return(
    call: &str,
    source: &StandardSet,
    target: &StandardSet,
    proof: &str,
) -> Result<String, LeanCompileError> {
    Ok(match fn_return_bridge(source, target)? {
        Some(bridge) => format!("(Litex.{bridge} {call} {proof})"),
        None => proof.into(),
    })
}
