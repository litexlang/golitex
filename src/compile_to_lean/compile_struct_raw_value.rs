use super::compile_def_struct_stmt_result::{has_dependent_fields, validate_struct};
use super::compile_struct_conditions::coordinate_bindings;
use super::compile_struct_header::header_substitution;
use super::helper::{conjunction_proposition, ensure_object};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Denotation under raw function/field binders. Formation is still proved
    /// by the caller's original WD; this expression supplies no replacement WD.
    pub(super) fn compile_struct_raw_value(
        &self,
        object: &StructObj,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let (declaration, producer, _) = position.visible_struct(&object.name, &self.runtime)?;
        validate_struct(declaration)?;
        header_substitution(&declaration.statement, object)?;
        let mut bound = bindings.clone();
        let mut arguments = Vec::new();
        let parameters = declaration
            .statement
            .param_def_with_dom
            .as_ref()
            .map(|(p, _)| p.ordered_param_ids())
            .unwrap_or_default();
        for (id, argument) in parameters.into_iter().zip(&object.params) {
            let value = self.compile_function_raw_expression_bound(argument, position, bindings)?;
            let name = format!("_struct_raw_arg_i{}", id.value());
            arguments.push(format!("let {name} : M.Value := {value}"));
            bound.insert(id, name);
        }
        let header = SourcePosition::new(
            Some(&producer),
            SourceOwner::StructHeader(declaration),
            usize::MAX,
        );
        let dependent = has_dependent_fields(&declaration.statement);
        let mut field_bindings = bound.clone();
        let mut fields = Vec::new();
        for (index, (field, stage)) in declaration
            .statement
            .fields
            .iter()
            .zip(&declaration.field_scope.fields)
            .enumerate()
        {
            ensure_object(&field.field_type, &stage.well_defined)?;
            let prior =
                SourcePosition::new(Some(&header), SourceOwner::StructFields(declaration), index);
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::WD(&stage.well_defined),
                usize::MAX,
            );
            let value = self.compile_function_raw_expression_bound(
                &field.field_type,
                &formed,
                &field_bindings,
            )?;
            let variable = format!("_raw_i{}", field.binding.id.value());
            if dependent {
                field_bindings.insert(field.binding.id, variable.clone());
            }
            fields.push((variable, value));
        }
        let mut value = if dependent {
            let telescope = fields.into_iter().rev().fold(
                "Litex.DependentFields.nil".to_owned(),
                |tail, (variable, carrier)| {
                    format!("(Litex.DependentFields.cons {carrier} (fun {variable} => {tail}))")
                },
            );
            format!("(Litex.DependentFields.value {telescope})")
        } else {
            format!(
                "(Litex.FiniteFunction.cartValue (M := M) ![{}])",
                fields
                    .into_iter()
                    .map(|(_, v)| v)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        if !declaration.statement.equivalent_facts.is_empty() {
            bound.extend(coordinate_bindings(&declaration.statement, "_struct_raw"));
            let mut clauses = Vec::new();
            for (index, fact) in declaration.statement.equivalent_facts.iter().enumerate() {
                let prior = SourcePosition::new(
                    Some(&header),
                    SourceOwner::StructFields(declaration),
                    declaration.statement.fields.len() + index,
                );
                clauses.push(self.compile_canonical_predicate_value(fact, &prior, &bound)?);
            }
            let condition = conjunction_proposition(clauses)?;
            // Preserve SetBuilderObj.condition's certified bound member.
            value = format!("(let _struct_raw_bound := {value}; Litex.SetSemantics.sepValue _struct_raw_bound (fun (_struct_raw : M.Value) => ∃ (_ : M.mem _struct_raw _struct_raw_bound), {condition}))");
        }
        if arguments.is_empty() {
            Ok(value)
        } else {
            Ok(format!("({};\n{value})", arguments.join(";\n")))
        }
    }
}
