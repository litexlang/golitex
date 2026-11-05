use super::compile_def_struct_stmt_result::{has_dependent_fields, struct_declaration_name};
use super::compile_struct_conditions::field_substitution;
use super::compile_struct_header::header_substitution;
use super::helper::{ensure_object, instantiated_object_matches};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecDefStructStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_released_struct_carrier(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let mut cursor = Some(position);
        while let Some(current) = cursor {
            if let SourceOwner::StructLayer(layer) = current.owner {
                let (declaration, _, _) =
                    current.visible_struct(&layer.struct_obj.name, &self.runtime)?;
                if !has_dependent_fields(&declaration.statement) {
                    let mut substitution =
                        header_substitution(&declaration.statement, &layer.struct_obj)?;
                    substitution.extend(field_substitution(&declaration.statement, &layer.obj));
                    if let Some(index) = declaration.statement.fields.iter().position(|field| {
                        instantiated_object_matches(&field.field_type, object, &substitution)
                    }) {
                        let base =
                            self.compile_struct_base_reference(&layer.struct_obj, current)?;
                        let n = declaration.statement.fields.len();
                        return Ok(Some(format!("(let _field_carriers := {base}; Litex.semanticObject (_field_carriers.val.factors ({index} : Fin {n})) (_field_carriers.wd ({index} : Fin {n})))")));
                    }
                }
                if has_dependent_fields(&declaration.statement) {
                    let mut subst = header_substitution(&declaration.statement, &layer.struct_obj)?;
                    subst.extend(field_substitution(&declaration.statement, &layer.obj));
                    // Every field carrier comes from this dependent record,
                    // including a constant carrier before its dependent fields.
                    if let Some(index) = declaration.statement.fields.iter().position(|field| {
                        instantiated_object_matches(&field.field_type, object, &subst)
                    }) {
                        let (receiver_carrier, member) =
                            self.compile_struct_receiver(&layer.obj, current)?;
                        if receiver_carrier != layer.struct_obj {
                            return Err(LeanCompileError::unsupported(
                                "StructRelease/ReceiverView",
                            ));
                        }
                        let receiver = self.compile_object_reference(&layer.obj, current)?;
                        let base =
                            self.compile_struct_base_reference(&layer.struct_obj, current)?;
                        let indices =
                            self.compile_struct_coordinate_indices(&layer.struct_obj, current)?;
                        let member = self.compile_struct_base_membership(
                            &layer.struct_obj,
                            &receiver,
                            &member,
                            current,
                        )?;
                        return Ok(Some(format!("(Litex.dependentFieldCarrier {receiver} {base} {indices} {member} ({index} : Fin {}))", declaration.statement.fields.len())));
                    }
                }
            }
            cursor = current.parent;
        }
        Ok(None)
    }

    pub(super) fn compile_dependent_struct_statement(
        &self,
        proof: &ExecDefStructStmtSuccessResult,
        outer: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let header = SourcePosition::new(Some(outer), SourceOwner::StructHeader(proof), usize::MAX);
        let (header_binders, _, header_definitions) = self.compile_struct_header(proof, &header)?;
        let mut raw_bindings = HashMap::new();
        let mut fields = Vec::new();
        for (index, (field, stage)) in proof
            .statement
            .fields
            .iter()
            .zip(&proof.field_scope.fields)
            .enumerate()
        {
            let prior = SourcePosition::new(Some(&header), SourceOwner::StructFields(proof), index);
            ensure_object(&field.field_type, &stage.well_defined)?;
            let carrier = self.compile_wd(&stage.well_defined, &prior)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::WD(&stage.well_defined),
                usize::MAX,
            );
            let raw = self.compile_function_raw_expression_bound(
                &field.field_type,
                &formed,
                &raw_bindings,
            )?;
            self.validate_parameter_store_capture(&stage.defined)?;
            let [store] = stage.defined.store_and_infer_results.as_slice() else {
                return Err(LeanCompileError::unsupported("Struct/FieldStore"));
            };
            let introduced = SourcePosition {
                before: index + 1,
                ..prior
            };
            // Reuse the same exact binder/store validation as independent fields.
            self.introduce_member_parameter(&field.binding, &field.field_type, store, &introduced)?;
            let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
            let name = format!("h_{}", store.primary_fact_id().value());
            let member = (self.fact_proposition(&fact, &introduced)?, name.clone());
            let inferences =
                self.compile_parameter_inferences(store, &fact, &member, &introduced)?;
            let id = field.binding.id.value();
            let raw_name = format!("_raw_i{id}");
            raw_bindings.insert(field.binding.id, raw_name.clone());
            fields.push((id, raw_name, raw, carrier, name, inferences));
        }
        let mut raw = "Litex.DependentFields.nil".to_string();
        let mut body = self.compile_struct_condition_formation(proof, &header)?;
        body.push("exact True.intro".into());
        let mut body = body.join("\n");
        for (id, variable, carrier_raw, carrier, member, inferences) in fields.into_iter().rev() {
            raw = format!("(Litex.DependentFields.cons {carrier_raw} (fun {variable} => {raw}))");
            let mut tail = vec![format!("intro {variable} {member}"),
                format!("let _value_i{id} : Litex.Obj (M := M) M.Value := Litex.semanticObject {variable} (M.member_isSet {member})")];
            tail.extend(inferences);
            tail.push(body);
            body = format!(
                "refine ⟨?_, ?_⟩\n· exact Litex.isSet {carrier}\n· {}",
                tail.join("\n").replace('\n', "\n  ")
            );
        }
        let raw = self.scope_proposition(raw, &header_definitions);
        let mut checks = header_definitions;
        checks.push(body);
        let context = format!(
            "{}{}",
            if local { String::new() } else { self.context_header(outer)? },
            if header_binders.is_empty() {
                String::new()
            } else {
                format!(" {}", header_binders.join(" "))
            }
        );
        let n = proof.statement.fields.len();
        let indices = (1..=n)
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let definition = if local { "let" } else { "noncomputable def" };
        let lemma = if local { "have" } else { "theorem" };
        let indices_name = struct_declaration_name("_struct_indices", proof, index, local);
        let indices_spec = struct_declaration_name("_struct_indices_spec", proof, index, local);
        let fields_name = struct_declaration_name("_struct_fields", proof, index, local);
        let fields_wd = struct_declaration_name("_struct_fields_wd", proof, index, local);
        let structure = struct_declaration_name("struct", proof, index, local);
        let indices_kind = if local { "let" } else { "def" };
        let coordinate_declarations = format!("{indices_kind} {indices_name} : Fin {n} → ℂ :=\n  ![{indices}]\n\n{lemma} {indices_spec} : ∀ i, {indices_name} i = ((i.val + 1 : ℕ) : ℂ) := by\n  intro i\n  fin_cases i <;> norm_num [{indices_name}]");
        let fields =
            self.struct_self_application(&fields_name, proof, outer)?;
        let well_formed =
            self.struct_self_application(&fields_wd, proof, outer)?;
        let checked = format!("{coordinate_declarations}\n\n{definition} {fields_name}{context} : Litex.DependentFields M {n} :=\n  {raw}\n\n{lemma} {fields_wd}{context} : Litex.DependentFields.WellFormed {fields} := by\n  {}", checks.join("\n").replace('\n', "\n  "));
        let carrier = format!("Litex.dependentCart {fields} {well_formed}");
        let host = format!("Litex.DependentCartObj M {n}");
        if proof.statement.equivalent_facts.is_empty() {
            return Ok(format!("{checked}\n\n{definition} {structure}{context} : Litex.Obj (M := M) ({host}) :=\n  {carrier}"));
        }
        self.compile_constrained_struct_declarations(
            proof,
            index,
            &checked,
            &carrier,
            outer,
            &header_binders,
            &host,
            local,
        )
    }

    pub(super) fn compile_struct_coordinate_indices(
        &self,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, producer, index) = position.visible_struct(&carrier.name, &self.runtime)?;
        position.validate_declaration_context(&producer)?;
        let prefix = (!producer.is_local()).then(|| producer.module_file_number()).flatten()
            .map(|file| format!("source_{file}."))
            .unwrap_or_default();
        let indices = struct_declaration_name("_struct_indices", declaration, index + 1, producer.is_local());
        let specification = struct_declaration_name("_struct_indices_spec", declaration, index + 1, producer.is_local());
        Ok(format!("{prefix}{indices} {prefix}{specification}"))
    }

    pub(super) fn compile_struct_cart_reference(
        &self,
        carrier: &StructObj,
        receiver: &str,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&carrier.name, &self.runtime)?;
        let base = self.compile_struct_base_reference(carrier, position)?;
        if !has_dependent_fields(&declaration.statement) {
            return Ok(base);
        }
        let member = self.compile_struct_base_membership(carrier, receiver, member, position)?;
        let indices = self.compile_struct_coordinate_indices(carrier, position)?;
        Ok(format!(
            "(Litex.dependentCartAt {receiver} {base} {indices} {member})"
        ))
    }

    pub(super) fn compile_struct_cart_membership(
        &self,
        carrier: &StructObj,
        receiver: &str,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&carrier.name, &self.runtime)?;
        let member = self.compile_struct_base_membership(carrier, receiver, member, position)?;
        if !has_dependent_fields(&declaration.statement) {
            return Ok(member);
        }
        let base = self.compile_struct_base_reference(carrier, position)?;
        let indices = self.compile_struct_coordinate_indices(carrier, position)?;
        Ok(format!(
            "(Litex.inDependentCartAt {receiver} {base} {indices} {member})"
        ))
    }
}
