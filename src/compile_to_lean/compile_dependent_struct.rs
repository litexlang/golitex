use super::compile_def_struct_stmt_result::has_dependent_fields;
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
                let (declaration, _, _) = current.visible_struct(&layer.struct_obj.name)?;
                if has_dependent_fields(&declaration.statement) {
                    let mut subst = header_substitution(&declaration.statement, &layer.struct_obj)?;
                    subst.extend(field_substitution(&declaration.statement, &layer.obj));
                    if let Some(index) = declaration.statement.fields.iter().position(|field| {
                        let mut free = std::collections::HashSet::new();
                        crate::instantiate::collect_free_plain_ids(
                            &field.field_type,
                            &std::collections::HashSet::new(),
                            &mut free,
                        );
                        declaration
                            .statement
                            .fields
                            .iter()
                            .any(|f| free.contains(&f.binding.id))
                            && instantiated_object_matches(&field.field_type, object, &subst)
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
            let raw = self.compile_function_raw_expression_bound(
                &field.field_type,
                &prior,
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
            self.context_header(outer)?,
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
        let coordinate_declarations = format!("def _struct_indices_{index} : Fin {n} → ℂ :=\n  ![{indices}]\n\ntheorem _struct_indices_spec_{index} : ∀ i, _struct_indices_{index} i = ((i.val + 1 : ℕ) : ℂ) := by\n  intro i\n  fin_cases i <;> norm_num [_struct_indices_{index}]");
        let fields =
            self.struct_self_application(&format!("_struct_fields_{index}"), proof, outer)?;
        let well_formed =
            self.struct_self_application(&format!("_struct_fields_wd_{index}"), proof, outer)?;
        let checked = format!("{coordinate_declarations}\n\nnoncomputable def _struct_fields_{index}{context} : Litex.DependentFields M {n} :=\n  {raw}\n\ntheorem _struct_fields_wd_{index}{context} : Litex.DependentFields.WellFormed {fields} := by\n  {}", checks.join("\n").replace('\n', "\n  "));
        let carrier = format!("Litex.dependentCart {fields} {well_formed}");
        let host = format!("Litex.DependentCartObj M {n}");
        if proof.statement.equivalent_facts.is_empty() {
            return Ok(format!("{checked}\n\nnoncomputable def struct_{index}{context} : Litex.Obj (M := M) ({host}) :=\n  {carrier}"));
        }
        self.compile_constrained_struct_declarations(
            proof,
            index,
            &checked,
            &carrier,
            outer,
            &header_binders,
            &host,
        )
    }

    pub(super) fn compile_struct_coordinate_indices(
        &self,
        carrier: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (_, _, index) = position.visible_struct(&carrier.name)?;
        Ok(format!(
            "_struct_indices_{} _struct_indices_spec_{}",
            index + 1,
            index + 1
        ))
    }

    pub(super) fn compile_struct_cart_reference(
        &self,
        carrier: &StructObj,
        receiver: &str,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
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
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
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
