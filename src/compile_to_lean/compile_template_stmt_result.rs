use super::helper::{
    ensure_object, instantiated_fact_matches, instantiated_object_matches, source_subject,
};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::InstantiatedTemplateObjObjWellDefinedProof;
use crate::execute::{ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult};
use crate::prelude::*;
use std::collections::HashMap;

fn alias_body(
    p: &ExecDefTemplateStmtSuccessResult,
) -> Result<&ExecHaveObjEqualStmtSuccessResult, LeanCompileError> {
    match p.body.as_ref() {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(body)),
        )) if body.statement.param_def.ordered_param_ids().len() == 1 => Ok(body),
        _ => Err(LeanCompileError::unsupported("Template/Body")),
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_template_equality(
        &self,
        fact: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_template::result::EqualitySearchProofByTemplateObjectDefinition,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_template::result::EqualitySearchProofByTemplateObjectDefinition;
        let EqualitySearchProofByTemplateObjectDefinition::HaveObjEqual(p) = proof else {
            return Err(LeanCompileError::unsupported("Template/FunctionUnfold"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) = source_subject(&p.residual_equal)?
        else {
            return Err(LeanCompileError::unsupported("Template/Residual"));
        };
        let (instance, reversed) = match (&fact.left, &fact.right) {
            (Obj::InstantiatedTemplateObj(i), other) if other.ir() == residual.right.ir() => {
                (i, false)
            }
            (other, Obj::InstantiatedTemplateObj(i)) if other.ir() == residual.right.ir() => {
                (i, true)
            }
            _ => return Err(LeanCompileError::unsupported("Template/UnfoldSubject")),
        };
        let (template, _, _) = position.visible_template(&instance.template_name)?;
        let body = alias_body(template)?;
        let ids = template.statement.template_arg_def.ordered_param_ids();
        if ids.len() != instance.args.len() || body.statement.objs_equal_to.len() != 1 {
            return Err(LeanCompileError::unsupported("Template/UnfoldArity"));
        }
        let subst = ids
            .into_iter()
            .zip(instance.args.iter().cloned())
            .collect::<HashMap<_, _>>();
        if p.expanded_rhs.ir() != residual.left.ir()
            || !instantiated_object_matches(
                &body.statement.objs_equal_to[0],
                &p.expanded_rhs,
                &subst,
            )
        {
            return Err(LeanCompileError::unsupported("Template/ExpandedSubject"));
        }
        let (_, residual) = self.compile_verify(&p.residual_equal, position)?;
        Ok(format!(
            "(show {} = {} from {})",
            self.compile_normalization_value(&fact.left, position)?,
            self.compile_normalization_value(&fact.right, position)?,
            if reversed {
                format!("({residual}).symm")
            } else {
                residual
            }
        ))
    }

    pub(super) fn compile_template_statement(
        &self,
        result: &ExecDefTemplateStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported("Template/LocalDeclaration"));
        }
        let ExecDefTemplateStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("Template/Failed"));
        };
        let body = alias_body(p)?;
        let crate::ast::stmt::TemplateDefEnum::HaveObjEqualStmt(source) =
            &p.statement.template_def_stmt
        else {
            return Err(LeanCompileError::unsupported("Template/BodyCapture"));
        };
        if source != &body.statement {
            return Err(LeanCompileError::unsupported("Template/BodyCapture"));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::Template(p), 0);
        let domains = p
            .statement
            .template_arg_dom
            .iter()
            .cloned()
            .map(crate::instantiate::quantifier_free_fact_to_fact)
            .collect::<Vec<_>>();
        let (binders, introductions, mut definitions) = self.compile_quantified_head(
            &p.statement.template_arg_def,
            &domains,
            &p.introduced_params,
            &p.assumed_dom_facts,
            &scope,
        )?;
        let head = p.statement.template_arg_def.ordered_param_ids().len() + domains.len();
        let prior = SourcePosition {
            before: head,
            ..scope
        };
        definitions.push(self.compile_statement_in_scope(&p.body, &prior, 1, true)?);
        let complete = SourcePosition {
            before: head + 1,
            ..scope
        };
        let binding = &body.statement.param_def.groups[0].params[0];
        let value = self.compile_object_reference(
            &Obj::Identifier(IdentifierObj::from_bound_name(binding)),
            &complete,
        )?;
        let object_name = format!("_template_i{}", binding.id.value());
        let context = self.context_header(position)?;
        let mut declarations = vec![format!("noncomputable def {object_name}{context} {} : Litex.Obj (M := M) M.Value := by\n  {}\n  exact Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value})", binders.join(" "), definitions.join("\n").replace('\n', "\n  "))];
        let source_ids = &body.store_and_infer_result.stored_fact_ids;
        if p.definition_facts.len() != source_ids.len()
            || p.definition_facts
                .iter()
                .zip(source_ids)
                .any(|(p, id)| p.source_fact_id != *id)
        {
            return Err(LeanCompileError::unsupported("Template/PublicationCapture"));
        }
        let instance = Obj::InstantiatedTemplateObj(InstantiatedTemplateObj {
            template_name: AtomicName::Plain {
                name: p.statement.template_name.clone(),
            },
            args: p
                .statement
                .template_arg_def
                .groups
                .iter()
                .flat_map(|g| &g.params)
                .map(|a| Obj::Identifier(IdentifierObj::from_bound_name(a)))
                .collect(),
        });
        let substitution = HashMap::from([(binding.id, instance)]);
        for published in &p.definition_facts {
            let source = self.resolve_fact(published.source_fact_id, &complete)?;
            let StoreFactResult::ForallFact(stored) = &published.store_and_infer.store else {
                return Err(LeanCompileError::unsupported("Template/PublicationShape"));
            };
            let fact = &stored.fact;
            if fact.typed_parameters != p.statement.template_arg_def
                || fact.dom_facts != domains
                || fact.then_facts.len() != 1
            {
                return Err(LeanCompileError::unsupported("Template/PublicationHeader"));
            }
            let conclusion = match &fact.then_facts[0] {
                ExistOrAndChainAtomicFact::AtomicFact(f) => Fact::AtomicFact(f.clone()),
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "Template/PublicationConclusion",
                    ))
                }
            };
            if !instantiated_fact_matches(&source, &conclusion, &substitution) {
                return Err(LeanCompileError::unsupported("Template/PublicationSubject"));
            }
            self.validate_store(
                &published.store_and_infer.store,
                &Fact::ForallFact(fact.clone()),
            )?;
            let proposition = self
                .scope_proposition(self.fact_proposition(&conclusion, &complete)?, &definitions);
            let proposition = if binders.is_empty() {
                proposition
            } else {
                format!("∀ {}, {proposition}", binders.join(" "))
            };
            let mut proof = Vec::new();
            if !introductions.is_empty() {
                proof.push(format!("intro {}", introductions.join(" ")));
            }
            proof.extend(definitions.clone());
            proof.push(format!(
                "exact {}",
                complete
                    .visible_fact(published.source_fact_id, &self.runtime)?
                    .1
            ));
            let name = format!("h_{}", fact.fact_id.value());
            declarations.push(format!(
                "theorem {name}{context} : {proposition} := by\n  {}",
                proof.join("\n").replace('\n', "\n  ")
            ));
            // Publication inference remains checked even when it emits no new facts.
            let published_position = SourcePosition {
                before: p.definition_facts.len(),
                ..*position
            };
            declarations.extend(self.compile_stored_inferences(
                &published.store_and_infer,
                &Fact::ForallFact(fact.clone()),
                &(proposition, self.context_application(&name, position)),
                &published_position,
            )?);
        }
        Ok(declarations.join("\n\n"))
    }

    pub(super) fn template_self_reference(
        &self,
        instance: &InstantiatedTemplateObj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let mut cursor = Some(position);
        while let Some(scope) = cursor {
            if let SourceOwner::Template(p) = scope.owner {
                let parameters = p
                    .statement
                    .template_arg_def
                    .groups
                    .iter()
                    .flat_map(|g| &g.params)
                    .collect::<Vec<_>>();
                if instance.template_name.local_name() == p.statement.template_name
                    && parameters.len() == instance.args.len()
                    && parameters.iter().zip(&instance.args).all(|(p, a)| {
                        a.ir() == Obj::Identifier(IdentifierObj::from_bound_name(p)).ir()
                    })
                {
                    let binding = alias_body(p)?.statement.param_def.ordered_param_ids()[0];
                    let base = self
                        .context_application(&format!("_template_i{}", binding.value()), position);
                    let mut args = parameters
                        .iter()
                        .zip(&p.introduced_params.defined_params.store_and_infer_results)
                        .flat_map(|(p, s)| {
                            [
                                format!("_value_i{}", p.id.value()),
                                format!("h_{}", s.primary_fact_id().value()),
                            ]
                        })
                        .collect::<Vec<_>>();
                    args.extend(
                        p.assumed_dom_facts
                            .iter()
                            .map(|d| format!("h_{}", d.store_and_infer.primary_fact_id().value())),
                    );
                    return Ok(Some(format!("({base} {})", args.join(" "))));
                }
            }
            cursor = scope.parent;
        }
        Ok(None)
    }

    pub(super) fn compile_template_wd(
        &self,
        instance: &InstantiatedTemplateObj,
        evidence: &InstantiatedTemplateObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (p, producer, _) = position.visible_template(&instance.template_name)?;
        let body = alias_body(p)?;
        let ids = p.statement.template_arg_def.ordered_param_ids();
        let n = ids.len();
        if instance.args.len() != n
            || evidence.child_obj_well_defined.len() != n
            || evidence.requirement_fact_verified.len() != n + p.assumed_dom_facts.len()
        {
            return Err(LeanCompileError::unsupported("Template/InstanceStages"));
        }
        let subst = ids
            .into_iter()
            .zip(instance.args.iter().cloned())
            .collect::<HashMap<_, _>>();
        let mut values = Vec::new();
        for (index, (arg, wd)) in instance
            .args
            .iter()
            .zip(&evidence.child_obj_well_defined)
            .enumerate()
        {
            ensure_object(arg, wd)?;
            values.push(self.compile_wd(
                wd,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let header_scope =
            SourcePosition::new(Some(&producer), SourceOwner::Template(p), usize::MAX);
        let source_ids = p
            .introduced_params
            .defined_params
            .store_and_infer_results
            .iter()
            .map(|s| s.primary_fact_id())
            .chain(
                p.assumed_dom_facts
                    .iter()
                    .map(|s| s.store_and_infer.primary_fact_id()),
            );
        let mut checks = Vec::new();
        for (index, (id, checked)) in source_ids
            .zip(&evidence.requirement_fact_verified)
            .enumerate()
        {
            let source = self.resolve_fact(id, &header_scope)?;
            if !instantiated_fact_matches(&source, &source_subject(checked)?, &subst) {
                return Err(LeanCompileError::unsupported("Template/RequirementSubject"));
            }
            checks.push(
                self.compile_verify(
                    checked,
                    &SourcePosition {
                        before: n + index,
                        ..*position
                    },
                )?
                .1,
            );
        }
        let mut args = values
            .iter()
            .zip(&checks)
            .flat_map(|(v, h)| [v.clone(), h.clone()])
            .collect::<Vec<_>>();
        args.extend(checks.into_iter().skip(n));
        let base = self.context_application(
            &format!(
                "_template_i{}",
                body.statement.param_def.ordered_param_ids()[0].value()
            ),
            &producer,
        );
        Ok(format!("({base} {})", args.join(" ")))
    }
}
