use super::helper::{ensure_object, finite_vector_proof};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_def_struct_stmt::{
    ExecDefStructStmtResult, ExecDefStructStmtSuccessResult,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructObjObjWellDefinedProof;
use crate::prelude::*;
use std::collections::HashSet;

pub(super) fn has_dependent_fields(source: &crate::ast::stmt::DefStructStmt) -> bool {
    let ids: HashSet<_> = source.fields.iter().map(|f| f.binding.id).collect();
    source.fields.iter().any(|field| {
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(&field.field_type, &HashSet::new(), &mut free);
        free.iter().any(|id| ids.contains(id))
    })
}

/// Field carriers may refer only to earlier fields; conditions retain the
/// existing atomic/conjunction/chain boundary and their original capture.
pub(super) fn validate_struct(
    proof: &ExecDefStructStmtSuccessResult,
) -> Result<(), LeanCompileError> {
    let source = &proof.statement;
    if source.param_def_with_dom.is_some() != proof.introduced_params.is_some() {
        return Err(LeanCompileError::unsupported("Struct/HeaderStages"));
    }
    if source
        .param_def_with_dom
        .as_ref()
        .is_some_and(|(parameters, _)| {
            parameters.groups.iter().any(|group| {
                !matches!(
                    group.param_type,
                    ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::Obj(_)
                )
            })
        })
    {
        return Err(LeanCompileError::unsupported("Struct/HeaderKind"));
    }
    if source
        .param_def_with_dom
        .as_ref()
        .is_some_and(|(_, domains)| !domains.is_empty())
        || !proof.structure_domains.is_empty()
    {
        return Err(LeanCompileError::unsupported("Struct/HeaderDomains"));
    }
    if source.equivalent_facts.len() != proof.field_scope.equivalent_facts.len()
        || source.equivalent_facts.len() != proof.definition_facts.len()
    {
        return Err(LeanCompileError::unsupported("Struct/ConditionStages"));
    }
    if source.equivalent_facts.iter().any(|f| {
        !matches!(
            f,
            Fact::AtomicFact(_) | Fact::AndFact(_) | Fact::ChainFact(_)
        )
    }) {
        return Err(LeanCompileError::unsupported("Struct/QuantifiedCondition"));
    }
    if source.fields.len() < 2 || source.fields.len() != proof.field_scope.fields.len() {
        return Err(LeanCompileError::unsupported("Struct/FieldStages"));
    }
    let mut ids = HashSet::new();
    let mut names = HashSet::new();
    for field in &source.fields {
        if !ids.insert(field.binding.id) || !names.insert(&field.binding.name) {
            return Err(LeanCompileError::unsupported("Struct/FieldIdentity"));
        }
    }
    for (index, field) in source.fields.iter().enumerate() {
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(&field.field_type, &HashSet::new(), &mut free);
        if source.fields[index..]
            .iter()
            .any(|field| free.contains(&field.binding.id))
        {
            return Err(LeanCompileError::unsupported("Struct/ForwardField"));
        }
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_struct_statement(
        &self,
        result: &ExecDefStructStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported("Struct/LocalDeclaration"));
        }
        let ExecDefStructStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Struct/Failed"));
        };
        validate_struct(proof)?;
        if has_dependent_fields(&proof.statement) {
            return self.compile_dependent_struct_statement(proof, position, index);
        }
        let outer = position;
        let header = SourcePosition::new(Some(outer), SourceOwner::StructHeader(proof), usize::MAX);
        let (header_binders, _, header_definitions) = self.compile_struct_header(proof, &header)?;
        let position = &header;
        let mut values = Vec::new();
        let mut sethood = Vec::new();
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut checks = header_definitions.clone();
        for (index, (field, stage)) in proof
            .statement
            .fields
            .iter()
            .zip(&proof.field_scope.fields)
            .enumerate()
        {
            let prior =
                SourcePosition::new(Some(position), SourceOwner::StructFields(proof), index);
            ensure_object(&field.field_type, &stage.well_defined)?;
            let carrier = self.compile_wd(&stage.well_defined, &prior)?;
            values.push(format!("Litex.denote {carrier}"));
            sethood.push(format!("Litex.isSet {carrier}"));
            self.validate_parameter_store_capture(&stage.defined)?;
            let [stored] = stage.defined.store_and_infer_results.as_slice() else {
                return Err(LeanCompileError::unsupported("Struct/FieldStore"));
            };
            let introduced = SourcePosition {
                before: index + 1,
                ..prior
            };
            let (field_binders, field_arguments) = self.introduce_member_parameter(
                &field.binding,
                &field.field_type,
                stored,
                &introduced,
            )?;
            binders.extend(field_binders);
            introductions.extend(field_arguments);
            let fact = self.resolve_fact(stored.primary_fact_id(), &introduced)?;
            let member = (
                self.fact_proposition(&fact, &introduced)?,
                format!("h_{}", stored.primary_fact_id().value()),
            );
            checks.extend(self.compile_parameter_inferences(
                stored,
                &fact,
                &member,
                &introduced,
            )?);
        }
        checks.extend(self.compile_struct_condition_formation(proof, position)?);
        checks.push("exact True.intro".into());
        let context = format!(
            "{}{}",
            self.context_header(outer)?,
            if header_binders.is_empty() {
                String::new()
            } else {
                format!(" {}", header_binders.join(" "))
            }
        );
        let checked_fields = format!(
            "theorem _struct_field_checks_{index}{context} : ∀ {}, True := by\n  intro {}\n  {}",
            binders.join(" "),
            introductions.join(" "),
            checks.join("\n").replace('\n', "\n  ")
        );
        let carrier = format!(
            "Litex.cart (M := M) ![{}] {}",
            values.join(", "),
            finite_vector_proof(&sethood)
        );
        let carrier = self.scope_proposition(carrier, &header_definitions);
        if proof.statement.equivalent_facts.is_empty() {
            return Ok(format!("{checked_fields}\n\nnoncomputable def struct_{index}{context} : Litex.Obj (M := M) (Litex.CartObj M {}) :=\n  {carrier}", values.len()));
        }
        self.compile_constrained_struct_declarations(
            proof,
            index,
            &checked_fields,
            &carrier,
            outer,
            &header_binders,
            &format!("Litex.CartObj M {}", values.len()),
        )
    }

    pub(super) fn compile_struct_reference(
        &self,
        object: &StructObj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_struct_family_reference(object, "struct", position)
    }

    pub(super) fn compile_struct_wd(
        &self,
        object: &StructObj,
        proof: &StructObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let arguments = self.compile_struct_arguments(object, proof, position)?;
        let (_, producer, index) = position.visible_struct(&object.name)?;
        let name = self.context_application(&format!("struct_{}", index + 1), &producer);
        Ok(if arguments.is_empty() {
            name
        } else {
            format!("({name} {})", arguments.join(" "))
        })
    }
}
