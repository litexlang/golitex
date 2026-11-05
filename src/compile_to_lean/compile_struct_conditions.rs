use super::helper::{conjunction_projection, conjunction_proposition, instantiated_fact_matches};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::DefStructStmt;
use crate::execute::ExecDefStructStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

/// Pure substitution for the declaration's original field binders. Its WD is
/// checked separately under the original ordered field/condition evidence.
pub(super) fn coordinate_bindings(
    definition: &DefStructStmt,
    receiver: &str,
) -> HashMap<IdentifierId, String> {
    definition
        .fields
        .iter()
        .enumerate()
        .map(|(index, field)| {
            (
                field.binding.id,
                format!(
                    "(Litex.FunctionSemantics.callValue (M := M) {receiver} (M.number ({} : ℂ)))",
                    index + 1
                ),
            )
        })
        .collect()
}

pub(super) fn field_substitution(
    definition: &DefStructStmt,
    receiver: &Obj,
) -> HashMap<IdentifierId, Obj> {
    definition
        .fields
        .iter()
        .map(|field| {
            (
                field.binding.id,
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(FieldAccess {
                    obj: Box::new(receiver.clone()),
                    fields: vec![field.binding.name.clone()],
                })),
            )
        })
        .collect()
}

impl LitexToLeanCompiler {
    pub(super) fn compile_struct_condition_formation(
        &self,
        proof: &ExecDefStructStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut clauses = Vec::new();
        let mut body = Vec::new();
        let mut introductions = Vec::new();
        for (index, (fact, stage)) in proof
            .statement
            .equivalent_facts
            .iter()
            .zip(&proof.field_scope.equivalent_facts)
            .enumerate()
        {
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::StructFields(proof),
                proof.statement.fields.len() + index,
            );
            self.compile_fact_wd(&stage.well_defined, fact, &prior)?;
            self.validate_store(&stage.store, fact)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&stage.well_defined),
                usize::MAX,
            );
            let proposition = self.fact_proposition(fact, &formed)?;
            let name = format!("h_{}", fact.fact_id().value());
            let published = SourcePosition {
                before: prior.before + 1,
                ..prior
            };
            let projections = self.compile_stored_projections(
                &stage.store,
                fact,
                &(proposition.clone(), name.clone()),
                &published,
            )?;
            introductions.push(name.clone());
            if !projections.is_empty() {
                body.push(format!("intro {}", introductions.join(" ")));
                introductions.clear();
                body.extend(projections.iter().cloned());
            }
            clauses.push((name, proposition, projections));
        }
        if clauses.is_empty() {
            return Ok(Vec::new());
        }
        if !introductions.is_empty() {
            body.push(format!("intro {}", introductions.join(" ")));
        }
        let mut proposition = "True".to_string();
        for (name, clause, projections) in clauses.into_iter().rev() {
            proposition = format!(
                "∀ ({name} : {clause}), {}",
                self.scope_proposition(proposition, &projections)
            );
        }
        body.push("exact True.intro".into());
        Ok(vec![format!(
            "have _struct_conditions_wd : {proposition} := by\n  {}",
            body.join("\n").replace('\n', "\n  ")
        )])
    }

    pub(super) fn compile_struct_condition_value(
        &self,
        definition: &DefStructStmt,
        receiver: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let bindings = coordinate_bindings(definition, receiver);
        conjunction_proposition(
            definition
                .equivalent_facts
                .iter()
                .map(|fact| self.compile_canonical_predicate_value(fact, position, &bindings))
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    pub(super) fn compile_constrained_struct_declarations(
        &self,
        proof: &ExecDefStructStmtSuccessResult,
        index: usize,
        checked_fields: &str,
        cart: &str,
        position: &SourcePosition<'_>,
        header_binders: &[String],
        base_host: &str,
    ) -> Result<String, LeanCompileError> {
        let context = format!(
            "{}{}",
            self.context_header(position)?,
            if header_binders.is_empty() {
                String::new()
            } else {
                format!(" {}", header_binders.join(" "))
            }
        );
        let base =
            self.struct_self_application(&format!("_struct_base_{index}"), proof, position)?;
        let condition =
            self.struct_self_application(&format!("_struct_condition_{index}"), proof, position)?;
        let structure =
            self.struct_self_application(&format!("struct_{index}"), proof, position)?;
        let header =
            SourcePosition::new(Some(position), SourceOwner::StructHeader(proof), usize::MAX);
        let raw = self.compile_struct_condition_value(&proof.statement, "_struct_raw", &header)?;
        let declarations = format!("{checked_fields}\n\nnoncomputable def _struct_base_{index}{context} : Litex.Obj (M := M) ({base_host}) :=\n  {cart}\n\nnoncomputable def _struct_condition_{index}{context} (_struct_raw : M.Value) : Prop :=\n  {raw}\n\nnoncomputable def struct_{index}{context} : Litex.Obj (M := M) (Litex.SetBuilderObj (M := M) ({base_host})) :=\n  Litex.setBuilder {base} (fun _struct_value _ => {condition} (Litex.denote _struct_value))\n\ntheorem _struct_members_{index}{context} {{_Host : Type _}} [_rep : Litex.Representation M _Host] (_struct_value : Litex.Obj (M := M) _Host) :\n    Litex.In _struct_value {structure} ↔ Litex.In _struct_value {base} ∧ {condition} (Litex.denote _struct_value) := by\n  change Litex.In _struct_value (Litex.setBuilder {base} _) ↔ _\n  rw [Litex.inSetBuilder_iff]\n  constructor\n  · rintro ⟨h, law⟩\n    exact ⟨h, law⟩\n  · rintro ⟨h, law⟩\n    exact ⟨h, law⟩");
        let laws = self.compile_struct_condition_publications(proof, index, position)?;
        Ok(format!("{declarations}\n\n{}", laws.join("\n\n")))
    }

    pub(super) fn compile_struct_base_reference(
        &self,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&carrier.name, &self.runtime)?;
        let family = if declaration.statement.equivalent_facts.is_empty() {
            "struct"
        } else {
            "_struct_base"
        };
        self.compile_struct_family_reference(carrier, family, position)
    }

    pub(super) fn compile_struct_members_reference(
        &self,
        carrier: &StructObj,
        receiver: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        Ok(format!(
            "({} {receiver})",
            self.compile_struct_family_reference(carrier, "_struct_members", position)?
        ))
    }

    pub(super) fn compile_struct_base_membership(
        &self,
        carrier: &StructObj,
        receiver: &str,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&carrier.name, &self.runtime)?;
        if declaration.statement.equivalent_facts.is_empty() {
            return Ok(member.into());
        }
        Ok(format!(
            "(({}.mp {member}).1)",
            self.compile_struct_members_reference(carrier, receiver, position)?
        ))
    }

    fn compile_struct_condition_publications(
        &self,
        proof: &ExecDefStructStmtSuccessResult,
        index: usize,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let header =
            SourcePosition::new(Some(position), SourceOwner::StructHeader(proof), usize::MAX);
        let (header_binders, header_intros, _) = self.compile_struct_header(proof, &header)?;
        let structure =
            self.struct_self_application(&format!("struct_{index}"), proof, position)?;
        let bridge =
            self.struct_self_application(&format!("_struct_members_{index}"), proof, position)?;
        let groups = proof
            .statement
            .param_def_with_dom
            .as_ref()
            .map(|(p, _)| p.groups.as_slice())
            .unwrap_or(&[]);
        let parameters = groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        let mut output = Vec::new();
        for (law_index, (source, published)) in proof
            .statement
            .equivalent_facts
            .iter()
            .zip(&proof.definition_facts)
            .enumerate()
        {
            if published.source_fact_id != source.fact_id() {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawIdentity"));
            }
            let StoreFactResult::ForallFact(stored) = &published.store_and_infer.store else {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawFamily"));
            };
            let target = &stored.fact;
            let universal = match source {
                Fact::ForallFact(f) => Some(f),
                _ => None,
            };
            let extra_groups = universal.map_or(0, |f| f.typed_parameters.groups.len());
            let domain_offset = universal.map_or(0, |f| f.dom_facts.len());
            let extra_parameters = universal.map_or(0, |f| {
                f.typed_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>()
            });
            if target.typed_parameters.groups.len() != groups.len() + 1 + extra_groups
                || target.typed_parameters.groups[..groups.len()] != *groups
            {
                return Err(LeanCompileError::unsupported(
                    "Struct/PublishedLawParameters",
                ));
            }
            let group = &target.typed_parameters.groups[groups.len()];
            let [parameter] = group.params.as_slice() else {
                return Err(LeanCompileError::unsupported(
                    "Struct/PublishedLawParameters",
                ));
            };
            let ParamType::Obj(Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(
                carrier,
            ))) = &group.param_type
            else {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawCarrier"));
            };
            if carrier.name != position.file_qualified_name(&proof.statement.name)
                || carrier.params.len() != parameters.len()
                || carrier.params.iter().zip(&parameters).any(|(a, (p, _))| {
                    a.ir() != Obj::Identifier(IdentifierObj::from_bound_name(p)).ir()
                })
            {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawCarrier"));
            }
            let instance = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            if target.dom_facts.len() != domain_offset + parameters.len() + 1 + extra_parameters {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawDomain"));
            }
            let mut premises = Vec::new();
            for ((parameter, kind), fact) in
                parameters.iter().zip(&target.dom_facts[domain_offset..])
            {
                let obj = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                let valid = match (kind, fact) {
                    (ParamType::Set(_), Fact::AtomicFact(AtomicFact::IsSetFact(f))) => {
                        f.set.ir() == obj.ir()
                    }
                    (
                        ParamType::NonemptySet(_),
                        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)),
                    ) => f.set.ir() == obj.ir(),
                    (ParamType::Obj(set), Fact::AtomicFact(AtomicFact::InFact(f))) => {
                        f.element.ir() == obj.ir() && f.set.ir() == set.ir()
                    }
                    _ => false,
                };
                if !valid {
                    return Err(LeanCompileError::unsupported("Struct/PublishedLawDomain"));
                }
                premises.push(self.fact_proposition(fact, &header)?);
            }
            let dom = &target.dom_facts[domain_offset + parameters.len()];
            if !matches!(dom, Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==instance.ir() && m.set.ir()==Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier.clone())).ir())
            {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawDomain"));
            }
            let instantiated_law = if universal.is_some() {
                // Publication flattens header, instance and law binders. Restore
                // only a view of that captured inner law for exact shape checking.
                let mut inner = target.clone();
                inner.typed_parameters.groups.drain(..groups.len() + 1);
                inner.dom_facts.truncate(domain_offset);
                for (group, facts) in inner
                    .typed_parameters
                    .groups
                    .iter()
                    .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
                    .zip(&target.dom_facts[domain_offset + parameters.len() + 1..])
                {
                    let object = Obj::Identifier(IdentifierObj::from_bound_name(group.0));
                    if !super::helper::parameter_type_fact_matches(
                        group.1,
                        &object,
                        facts,
                        &HashMap::new(),
                    ) {
                        return Err(LeanCompileError::unsupported("Struct/PublishedLawDomain"));
                    }
                }
                Fact::ForallFact(inner)
            } else {
                let [then] = target.then_facts.as_slice() else {
                    return Err(LeanCompileError::unsupported(
                        "Struct/PublishedLawConclusion",
                    ));
                };
                then.clone().into()
            };
            if !instantiated_fact_matches(
                source,
                &instantiated_law,
                &field_substitution(&proof.statement, &instance),
            ) {
                return Err(LeanCompileError::unsupported(
                    "Struct/PublishedLawConclusion",
                ));
            }
            let fact = Fact::ForallFact(target.clone());
            self.validate_store(&published.store_and_infer.store, &fact)?;
            let id = parameter.id.value();
            let value = format!("_value_i{id}");
            let member = format!("h_{}", dom.fact_id().value());
            let bindings =
                coordinate_bindings(&proof.statement, &format!("(Litex.denote {value})"));
            premises.push(format!("Litex.In {value} {structure}"));
            let mut inner_binders = Vec::new();
            let mut inner_intros = Vec::new();
            let mut law_arguments = Vec::new();
            let mut law_domains = Vec::new();
            let conclusion = if let Some(universal) = universal {
                let (law_parameters, bound) = self.compile_canonical_predicate_binders(
                    &universal.typed_parameters,
                    &header,
                    &bindings,
                )?;
                for ((name, carrier), type_fact) in law_parameters
                    .iter()
                    .zip(&target.dom_facts[domain_offset + parameters.len() + 1..])
                {
                    let member = format!("h_{}", type_fact.fact_id().value());
                    inner_binders.push(format!(
                        "({name} : Litex.Obj (M := M) M.Value) ({member} : {carrier})"
                    ));
                    inner_intros.extend([name.clone(), member.clone()]);
                    law_arguments.extend([name.clone(), member]);
                    premises.push(carrier.clone());
                }
                for domain in &universal.dom_facts {
                    let name = format!("h_{}", domain.fact_id().value());
                    law_domains
                        .push(self.compile_canonical_predicate_value(domain, &header, &bound)?);
                    inner_intros.push(name.clone());
                    law_arguments.push(name);
                }
                conjunction_proposition(
                    universal
                        .then_facts
                        .iter()
                        .map(|f| {
                            self.compile_canonical_predicate_value(
                                &f.clone().into(),
                                &header,
                                &bound,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                )?
            } else {
                self.compile_canonical_predicate_value(source, &header, &bindings)?
            };
            // The actual producer appends all type facts after the source domains.
            law_domains.extend(premises);
            law_domains.push(conclusion);
            let inner = if inner_binders.is_empty() {
                String::new()
            } else {
                format!("∀ {}, ", inner_binders.join(" "))
            };
            let proposition = format!("∀ {}{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}) ({member} : Litex.In {value} {structure}), {inner}{}", if header_binders.is_empty() { String::new() } else { format!("{} ", header_binders.join(" ")) }, law_domains.join(" → "));
            let selected = conjunction_projection(
                &format!("(({bridge} {value}).mp {member}).2"),
                law_index,
                proof.statement.equivalent_facts.len(),
            );
            let ignores = vec!["_"; parameters.len() + 1 + extra_parameters].join(" ");
            let inner_intros = if inner_intros.is_empty() {
                String::new()
            } else {
                format!("{} ", inner_intros.join(" "))
            };
            let law_arguments = if law_arguments.is_empty() {
                String::new()
            } else {
                format!(" {}", law_arguments.join(" "))
            };
            let evidence = format!("(by\n  intro {}_Host_i{id} _rep_i{id} {value} {member} {inner_intros}{ignores}\n  exact {selected}{law_arguments})", if header_intros.is_empty() { String::new() } else { format!("{} ", header_intros.join(" ")) });
            let compiled = (proposition, evidence);
            output.push(self.emit_internal_fact(&fact, &compiled, position)?);
            let completed = SourcePosition {
                before: law_index + 2,
                ..*position
            };
            output.extend(self.compile_stored_inferences(
                &published.store_and_infer,
                &fact,
                &(
                    compiled.0,
                    self.context_application(&format!("h_{}", fact.fact_id().value()), &completed),
                ),
                &completed,
            )?);
        }
        Ok(output)
    }
}
