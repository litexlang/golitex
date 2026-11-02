use super::compile_function_template::function_guard_fact;
use super::compile_have_fn_by_induc_result::recursive_signature;
use super::compile_recursive_case_tree::{
    recursive_guard_atoms, recursive_leaf_paths, recursive_path_guards,
};
use super::compile_template_function::validate_template_forall_shape;
use super::compile_template_stmt_result::{
    template_binding, template_output, template_substitution,
};
use super::helper::{
    conjunction_projection, instantiated_fact_matches, instantiated_object_matches, source_subject,
    standard_inclusion_term,
};
use super::source_position::{
    visit_complete_wd, visit_forall_constructor, SourceConstructor, SourceOwner, SourcePosition,
};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::{ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByInducStmtResult};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// A published template theorem retains two original headers. Replay them
    /// in their owning scopes, then abstract in the published forall's order.
    pub(super) fn compile_template_callee_constructor(
        &self,
        published: &ForallFact,
        then_index: usize,
        pattern: &Obj,
        application: &SearchProofByKnownForallFact,
        caller: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some((template, index, producer)) =
            caller.visible_template_publication(application.detailed_ref().cite.fact_id)
        else {
            return Ok(None);
        };
        let publication = &template.definition_facts[index];
        self.validate_store(
            &publication.store_and_infer.store,
            &Fact::ForallFact(published.clone()),
        )?;
        let (binding, _) = match pattern {
            Obj::InstantiatedTemplateObj(instance) => {
                template_output(template, instance.template_name.local_name())?
            }
            _ => template_binding(template)?,
        };
        let instance = Obj::InstantiatedTemplateObj(InstantiatedTemplateObj {
            template_name: AtomicName::Plain {
                name: binding.name.clone(),
            },
            args: template
                .statement
                .template_arg_def
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p)))
                .collect(),
        });
        let Obj::InstantiatedTemplateObj(original_instance) = &instance else {
            unreachable!()
        };
        let substitution = template_substitution(template, original_instance)?;
        let domains = template
            .statement
            .template_arg_dom
            .iter()
            .cloned()
            .map(crate::instantiate::quantifier_free_fact_to_fact)
            .collect::<Vec<_>>();
        // A direct publication's header is exactly the template constructor's
        // header. Its recorded application therefore already supplies the
        // argument WD and guards needed to reference that constructor.
        if pattern.ir() == instance.ir()
            && !observe_numeric
            && published.typed_parameters == template.statement.template_arg_def
            && published.dom_facts == domains
            && published.then_facts.len() == 1
            && then_index == 0
        {
            let complete = SourcePosition::new(
                Some(&producer),
                SourceOwner::Template(template),
                template
                    .statement
                    .template_arg_def
                    .ordered_param_ids()
                    .len()
                    + domains.len()
                    + 1,
            );
            let source = self.resolve_fact(publication.source_fact_id, &complete)?;
            if !instantiated_fact_matches(
                &source,
                &published.then_facts[0].clone().into(),
                &substitution,
            ) {
                return Err(LeanCompileError::unsupported(
                    "WD/TemplatePublicationSubject",
                ));
            }
            let scope =
                SourcePosition::new(Some(caller), SourceOwner::KnownApplication(application), 0);
            let (definitions, arguments) =
                self.compile_known_application_requirements(published, application, &scope)?;
            let reference =
                self.context_application(&format!("_template_i{}", binding.id.value()), &producer);
            let term = format!("({reference} {})", arguments.join(" "));
            return Ok(Some(if definitions.is_empty() {
                term
            } else {
                format!("({};\n{term})", definitions.join(";\n"))
            }));
        }
        let template_head =
            SourcePosition::new(Some(&producer), SourceOwner::Template(template), 0);
        let (template_binders, _, mut definitions) = self.compile_quantified_head(
            &template.statement.template_arg_def,
            &domains,
            &template.introduced_params,
            &template.assumed_dom_facts,
            &template_head,
        )?;
        let ready = SourcePosition {
            before: template
                .statement
                .template_arg_def
                .ordered_param_ids()
                .len()
                + domains.len(),
            ..template_head
        };
        if published.typed_parameters == template.statement.template_arg_def
            && published.dom_facts == domains
            && published.then_facts.len() == 1
            && then_index == 0
        {
            let body_site = SourcePosition::new(
                Some(&ready),
                SourceOwner::Statement(&template.body),
                usize::MAX,
            );
            let source = self.resolve_fact(publication.source_fact_id, &body_site)?;
            if !instantiated_fact_matches(
                &source,
                &published.then_facts[0].clone().into(),
                &substitution,
            ) {
                return Err(LeanCompileError::unsupported(
                    "WD/TemplatePublicationSubject",
                ));
            }
            if let Fact::AtomicFact(atomic) = &source {
                let original = atomic_fact_args_ref(atomic).into_iter().find_map(|root| {
                    super::compile_callee_constructor::exact_constructor_pattern(
                        root,
                        pattern,
                        &substitution,
                    )
                });
                if let Some(original) = original {
                    if let Some(term) = self.compile_obtain_expression_reference(
                        original,
                        &body_site,
                        observe_numeric,
                    )? {
                        definitions.push(self.compile_statement_in_scope(
                            &template.body,
                            &ready,
                            1,
                            true,
                        )?);
                        // This factory's result carrier can depend on its header.
                        // Term-level bindings retain the constructor's inferred
                        // type; an untyped tactic block under the lambda cannot.
                        let term = format!("({};\n{term})", definitions.join(";\n"));
                        return self
                            .apply_callee_body(
                                published,
                                application,
                                caller,
                                template_binders,
                                term,
                            )
                            .map(Some);
                    }
                    if let Some(term) = body_site.with_visible_wd(original, &mut |wd, site| {
                        self.apply_callee_constructor(
                            published,
                            wd,
                            site,
                            application,
                            caller,
                            observe_numeric,
                            template_binders.clone(),
                            definitions.clone(),
                        )
                    })? {
                        return Ok(Some(term));
                    }
                }
            }
        }
        if let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(body),
        )) = template.body.as_ref()
        {
            let case_index = body
                .store_and_infer_result
                .case_defining_fact_ids
                .iter()
                .position(|id| *id == publication.source_fact_id)
                .ok_or_else(|| LeanCompileError::unsupported("WD/TemplateRecursiveEquation"))?;
            let store = &body.store_and_infer_result.case_defining[case_index];
            let StoreFactResult::ForallFact(stored) = &store.store else {
                return Err(LeanCompileError::unsupported(
                    "WD/TemplateRecursiveEquation",
                ));
            };
            self.validate_store(&store.store, &Fact::ForallFact(stored.fact.clone()))?;
            let signature = recursive_signature(body);
            let parameters = signature
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
                .collect::<Vec<_>>();
            let source_parameters = stored
                .fact
                .typed_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
                .collect::<Vec<_>>();
            let expected_domains = signature
                .dom_facts
                .iter()
                .map(function_guard_fact)
                .collect::<Result<Vec<_>, _>>()?;
            let (merged_guard, original_domains) = stored
                .fact
                .dom_facts
                .split_last()
                .ok_or_else(|| LeanCompileError::unsupported("WD/TemplateRecursiveHeader"))?;
            if then_index != 0
                || stored.fact.then_facts.len() != 1
                || parameters.len() != source_parameters.len()
                || parameters
                    .iter()
                    .zip(source_parameters)
                    .any(|((p, c), (q, t))| {
                        p.id != q.id || !matches!(t, ParamType::Obj(d) if *c == d)
                    })
                || original_domains != expected_domains
            {
                return Err(LeanCompileError::unsupported("WD/TemplateRecursiveHeader"));
            }
            let paths = recursive_leaf_paths(&body.statement.cases);
            let path = paths
                .get(case_index)
                .ok_or_else(|| LeanCompileError::unsupported("WD/TemplateRecursivePath"))?;
            let guards = recursive_path_guards(&body.statement.cases, path)?;
            let actual_atoms = recursive_guard_atoms(merged_guard)?;
            let guard_atoms = guards
                .iter()
                .map(|g| recursive_guard_atoms(&and_chain_as_fact(g)))
                .collect::<Result<Vec<_>, _>>()?;
            if !guard_atoms
                .iter()
                .flatten()
                .map(|a| a.ir())
                .eq(actual_atoms.iter().map(|a| a.ir()))
            {
                return Err(LeanCompileError::unsupported("WD/TemplateRecursiveGuard"));
            }
            let substitution = HashMap::from([(binding.id, instance.clone())]);
            validate_template_forall_shape(template, &stored.fact, published, &substitution)?;
            let recursion =
                SourcePosition::new(Some(&ready), SourceOwner::RecursiveFunction(body), 0);
            let introduced = SourcePosition {
                before: 1,
                ..recursion
            };
            self.validate_parameter_store_capture(&body.binder_introduction.defined_params)?;
            if parameters.len()
                != body
                    .binder_introduction
                    .defined_params
                    .store_and_infer_results
                    .len()
                || signature.dom_facts.len() != body.binder_introduction.assumed_dom_facts.len()
            {
                return Err(LeanCompileError::unsupported("WD/TemplateRecursiveBinders"));
            }
            let mut body_binders = Vec::new();
            let mut body_definitions = Vec::new();
            for ((parameter, carrier), store) in parameters.iter().zip(
                &body
                    .binder_introduction
                    .defined_params
                    .store_and_infer_results,
            ) {
                body_binders.extend(
                    self.introduce_member_parameter(parameter, carrier, store, &introduced)?
                        .0,
                );
                let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
                let member = (
                    self.fact_proposition(&fact, &introduced)?,
                    format!("h_{}", fact.fact_id().value()),
                );
                body_definitions.extend(self.compile_parameter_inferences(
                    store,
                    &fact,
                    &member,
                    &introduced,
                )?);
            }
            let body_parameter_count = body_binders.len();
            for (fact, store) in expected_domains
                .iter()
                .zip(&body.binder_introduction.assumed_dom_facts)
            {
                self.validate_store(&store.store, fact)?;
                let name = format!("h_{}", store.primary_fact_id().value());
                let proposition = self.fact_proposition(fact, &introduced)?;
                body_binders.push(format!("({name} : {proposition})"));
                body_definitions.extend(self.compile_stored_inferences(
                    store,
                    fact,
                    &(proposition, name),
                    &introduced,
                )?);
            }
            body_definitions.extend(self.compile_recursive_formation_checks(body, &recursion)?);
            let formed = SourcePosition {
                before: 8,
                ..recursion
            };
            let merged_name = format!("h_{}", merged_guard.fact_id().value());
            let guard_prop =
                self.compile_function_raw_predicate(merged_guard, &formed, &HashMap::new())?;
            body_binders.push(format!("({merged_name} : {guard_prop})"));
            let guard_proofs = if guards.len() == 1 {
                vec![merged_name]
            } else {
                let mut offset = 0;
                guard_atoms
                    .iter()
                    .map(|atoms| {
                        let proof = super::compile_general_recursive_result::and_intro(
                            (offset..offset + atoms.len())
                                .map(|i| {
                                    conjunction_projection(&merged_name, i, actual_atoms.len())
                                })
                                .collect(),
                        );
                        offset += atoms.len();
                        proof
                    })
                    .collect()
            };
            let template_count = template_binders.len() - domains.len();
            let mut binders = template_binders[..template_count].to_vec();
            binders.extend_from_slice(&body_binders[..body_parameter_count]);
            binders.extend_from_slice(&template_binders[template_count..]);
            binders.extend_from_slice(&body_binders[body_parameter_count..]);
            definitions.extend(body_definitions);
            return self.visit_recursive_case_wd(&body.statement.cases, &body.case_checks, path,
                &guard_proofs, &formed, definitions, &mut |original_wd, in_ret_set, assumed, definitions| {
                if !matches!(source_subject(in_ret_set)?, Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == original_wd.obj().ir() && f.set == signature.ret_set.as_ref().clone()) {
                    return Err(LeanCompileError::unsupported("WD/TemplateRecursiveReturn"));
                }
                visit_complete_wd(original_wd, assumed, &mut |constructor, site| {
                    let SourceConstructor::Checked(wd) = constructor else { return Ok(None); };
                    if !instantiated_object_matches(wd.obj(), pattern, &substitution) { return Ok(None); }
                    if matches!(wd.obj(), Obj::FnObj(call)
                        if matches!(call.head.as_ref(), FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) if *id == binding.id)) {
                        let (arguments, requirements) = self.compile_recursive_call_arguments(wd.obj(), body, wd, site)?;
                        let Obj::InstantiatedTemplateObj(instance) = &instance else { unreachable!() };
                        let function = self.template_self_reference(instance, &ready)?
                            .ok_or_else(|| LeanCompileError::unsupported("WD/TemplateRecursiveSelf"))?;
                        let membership = if self.recursive_uses_nat_representation(body, &ready)? {
                            format!("(Litex.recursiveNatFnInFnSet {function})")
                        } else {
                            format!("(Litex.recursiveFnInFnSet {function})")
                        };
                        let (call, output_law) = self.compile_recursive_completed_call(
                            &signature, &function, &membership, &arguments,
                            &requirements[..arguments.len() + signature.dom_facts.len()], site)?;
                        let emitted = if observe_numeric {
                            let output = self.compile_numeric_carrier(&signature.ret_set, site)?;
                            let member = standard_inclusion_term(&output, &StandardSet::C,
                                "_callee_object", &format!("(Litex.{output_law} _callee_object)"))?;
                            format!("(let _callee_object := {call};\nshow {{ _z : ℂ // Litex.denote _callee_object = M.number _z ∧ Litex.In _callee_object Litex.C }} from ⟨Litex.NativeBridge.asComplex _callee_object {member}, Litex.NativeBridge.asComplex_spec _callee_object {member}, {member}⟩)")
                        } else { call };
                        let DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::FnObj(evidence), .. } = wd.detailed_ref() else { unreachable!() };
                        let mut local_definitions = definitions.clone();
                        let scope = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
                        for (index, verified) in evidence.requirement_fact_verified.iter().enumerate().skip(arguments.len()) {
                            let checked = SourcePosition { before: arguments.len() + index, ..scope };
                            let fact = source_subject(verified)?;
                            local_definitions.push(self.emit_internal_fact(&fact,
                                &(self.fact_proposition(&fact, &checked)?, requirements[index].clone()), &checked)?);
                        }
                        let emitted = self.scope_proposition(emitted, &local_definitions);
                        return self.apply_callee_body(published, application, caller, binders.clone(), emitted).map(Some);
                    }
                    if wd.obj().ir() != pattern.ir() { return Ok(None); }
                    self.apply_callee_constructor(published, wd, site, application, caller,
                        observe_numeric, binders.clone(), definitions.clone()).map(Some)
                }, &mut |_, _| Ok(None))
            });
        }
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            ExecHaveFnByForallExistUniqueStmtResult::Success(body),
        )) = template.body.as_ref()
        else {
            return Err(LeanCompileError::unsupported("WD/TemplateBodyFormation"));
        };
        if publication.source_fact_id != body.property_forall_fact_id {
            return Err(LeanCompileError::unsupported(
                "WD/TemplatePropertyFormation",
            ));
        }
        definitions.push(self.compile_statement_in_scope(&template.body, &ready, 1, true)?);
        let (StoreFactResult::ForallFact(stored), FactWellDefinedProof::ForallFact(formation)) =
            (&body.property.store, &body.property_well_defined)
        else {
            return Err(LeanCompileError::unsupported(
                "WD/TemplatePropertyFormation",
            ));
        };
        validate_template_forall_shape(
            template,
            &stored.fact,
            published,
            &HashMap::from([(binding.id, instance)]),
        )?;
        // Property formation can use the selected object and its membership,
        // but cannot assume the property theorem it is about to publish.
        let body_scope =
            SourcePosition::new(Some(&ready), SourceOwner::Statement(&template.body), 3);
        visit_forall_constructor(
            SourceOwner::ForallWD(&stored.fact, formation),
            then_index,
            pattern,
            &body_scope,
            &mut |source, introduced, assumed, wd, site, _| {
                let header = SourcePosition {
                    before: 0,
                    ..*site
                        .callee_header()
                        .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeHeader"))?
                };
                let (body_binders, _, body_definitions) =
                    self.compile_forall_head(source, introduced, assumed, &header)?;
                let template_count = template_binders.len() - domains.len();
                let body_count = body_binders.len() - assumed.len();
                let mut binders = template_binders[..template_count].to_vec();
                binders.extend_from_slice(&body_binders[..body_count]);
                binders.extend_from_slice(&template_binders[template_count..]);
                binders.extend_from_slice(&body_binders[body_count..]);
                let mut local_definitions = definitions.clone();
                local_definitions.extend(body_definitions);
                self.apply_callee_constructor(
                    published,
                    wd,
                    site,
                    application,
                    caller,
                    observe_numeric,
                    binders,
                    local_definitions,
                )
            },
        )
    }

    /// Use the original call's checked input/domain certificates for the
    /// completed graph. Smaller-input certificates were already replayed above.
    fn compile_recursive_completed_call(
        &self,
        signature: &FnSet,
        function: &str,
        membership: &str,
        arguments: &[String],
        requirements: &[String],
        site: &SourcePosition<'_>,
    ) -> Result<(String, &'static str), LeanCompileError> {
        let (members, guard_proof) =
            self.compile_function_domain_certificates(signature, arguments, requirements, site)?;
        if !Self::function_uses_numeric_interface(signature) {
            let (_, argument, member, guard) = self.compile_packed_call_arguments(
                signature,
                arguments,
                &members,
                &guard_proof,
                site,
            )?;
            return Ok((format!("(Litex.callOn ({function}).val.signature {function} {argument} {membership} ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨{member}, {guard}⟩))"), "callOnInOutput"));
        }
        let (types, target) = self.compile_function_constructor_arguments(signature, site)?;
        let guard = self.compile_function_guard_template(signature, site)?;
        let constructor = match (arguments.len() == 1, target) {
            (true, false) => "call",
            (false, false) => "call2",
            (true, true) => "callTarget",
            (false, true) => "call2Target",
        };
        Ok((
            format!(
                "(Litex.{constructor} {types} {guard} {function} {} {membership} {} {guard_proof})",
                arguments.join(" "),
                members.join(" ")
            ),
            if arguments.len() == 1 {
                "callInOutput"
            } else {
                "call2InOutput"
            },
        ))
    }
}
