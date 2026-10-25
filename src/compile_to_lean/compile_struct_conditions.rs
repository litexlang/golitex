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
                .map(|fact| self.compile_function_raw_predicate(fact, position, &bindings))
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
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
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
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
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
            if target.typed_parameters.groups.len() != groups.len() + 1
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
            if !matches!(&carrier.name, AtomicName::Plain { name } if name==&proof.statement.name)
                || carrier.params.len() != parameters.len()
                || carrier.params.iter().zip(&parameters).any(|(a, (p, _))| {
                    a.ir() != Obj::Identifier(IdentifierObj::from_bound_name(p)).ir()
                })
            {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawCarrier"));
            }
            let instance = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            if target.dom_facts.len() != parameters.len() + 1 {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawDomain"));
            }
            let mut premises = Vec::new();
            for ((parameter, kind), fact) in parameters.iter().zip(&target.dom_facts) {
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
            let dom = target.dom_facts.last().unwrap();
            if !matches!(dom, Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==instance.ir() && m.set.ir()==Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier.clone())).ir())
            {
                return Err(LeanCompileError::unsupported("Struct/PublishedLawDomain"));
            }
            let [then] = target.then_facts.as_slice() else {
                return Err(LeanCompileError::unsupported(
                    "Struct/PublishedLawConclusion",
                ));
            };
            if !instantiated_fact_matches(
                source,
                &then.clone().into(),
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
            let conclusion = self.compile_function_raw_predicate(source, &header, &bindings)?;
            premises.push(format!("Litex.In {value} {structure}"));
            premises.push(conclusion);
            let proposition = format!("∀ {}{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}) ({member} : Litex.In {value} {structure}), {}", if header_binders.is_empty() { String::new() } else { format!("{} ", header_binders.join(" ")) }, premises.join(" → "));
            let selected = conjunction_projection(
                &format!("(({bridge} {value}).mp {member}).2"),
                law_index,
                proof.statement.equivalent_facts.len(),
            );
            let ignores = vec!["_"; target.dom_facts.len()].join(" ");
            let evidence = format!("(by\n  intro {}_Host_i{id} _rep_i{id} {value} {member} {ignores}\n  exact {selected})", if header_intros.is_empty() { String::new() } else { format!("{} ", header_intros.join(" ")) });
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
