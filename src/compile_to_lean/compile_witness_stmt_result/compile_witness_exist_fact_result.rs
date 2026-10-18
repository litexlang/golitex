use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_witness_stmt::ExecWitnessExistFactStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_witness_exist_statement(
        &self,
        proof: &ExecWitnessExistFactStmtSuccessResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExistShapedFact::Exist(fact) = &proof.statement.exist_shaped_fact_in_witness else {
            return Err(LeanCompileError::unsupported("Witness/ExistUnique"));
        };
        let FactWellDefinedProof::ExistFact(formation) = &proof.ambient.exist_fact_well_defined
        else {
            return Err(LeanCompileError::new(
                "Witness/Formation",
                "The plain existential requires its original formation result.",
            ));
        };
        let parameters: Vec<_> = fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter())
            .collect();
        let count = parameters.len();
        let stores = &proof
            .introduced_params
            .defined_params
            .store_and_infer_results;
        if count == 0
            || proof.statement.equal_tos.len() != count
            || proof.ambient.witness_obj_well_defined.len() != count
            || proof.ambient.witness_type_checks.len() != count
            || stores.len() != count
            || proof.witness_equalities.len() != count
            || proof.proof_steps.len() != proof.statement.proof.len()
            || proof.obligations.body_checks.len() != fact.facts.len()
            || proof.obligations.uniqueness_check.is_some()
        {
            return Err(LeanCompileError::new("Witness/Stages", "The witness must retain every original ordered binder, equality, proof step, and body check."));
        }
        self.validate_parameter_store_capture(&proof.introduced_params.defined_params)?;
        let proposition = self.compile_exist_formation(fact, formation, position)?;
        let mut witnesses = Vec::new();
        for (i, (value, checked)) in proof
            .statement
            .equal_tos
            .iter()
            .zip(&proof.ambient.witness_obj_well_defined)
            .enumerate()
        {
            let prior = SourcePosition {
                before: 1 + i,
                ..*position
            };
            witnesses.push(self.compile_wd(success_object_wd(checked, value)?, &prior)?);
        }
        let mut members = Vec::new();
        for (i, check) in proof.ambient.witness_type_checks.iter().enumerate() {
            let prior = SourcePosition {
                before: 1 + count + i,
                ..*position
            };
            members.push(self.compile_verify(check, &prior)?);
        }
        let ambient_complete = SourcePosition {
            before: 1 + 2 * count,
            ..*position
        };
        let scope =
            SourcePosition::new(Some(&ambient_complete), SourceOwner::WitnessExist(proof), 0);
        let substitution: HashMap<_, _> = parameters
            .iter()
            .zip(&proof.statement.equal_tos)
            .map(|(p, v)| (p.id, v.clone()))
            .collect();
        if substitution.len() != count {
            return Err(LeanCompileError::new(
                "Witness/ParameterIdentity",
                "The witness binders repeat a source identity.",
            ));
        }
        let mut lines = vec!["by".to_string()];
        let mut tuple = Vec::new();
        for (i, parameter) in parameters.iter().enumerate() {
            let introduced = SourcePosition {
                before: i + 1,
                ..scope
            };
            let member = self.resolve_fact(stores[i].primary_fact_id(), &introduced)?;
            let expected = source_subject(&proof.ambient.witness_type_checks[i])?;
            if !instantiated_fact_matches(&member, &expected, &substitution) {
                return Err(LeanCompileError::new(
                    "Witness/MemberSubject",
                    "The witness type check does not instantiate this original binder membership.",
                ));
            }
            self.validate_store(&stores[i].store, &member)?;
            let object_name = format!("_value_i{}", parameter.id.value());
            lines.push(format!("let {object_name} : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote {}) (Litex.isSet {})", witnesses[i], witnesses[i]));
            let member_name = format!("h_{}", member.fact_id().value());
            let member_type = self.fact_proposition(&member, &introduced)?;
            lines.push(format!(
                "have {member_name} : {member_type} := {}",
                members[i].1
            ));
            lines.extend(self.compile_parameter_inferences(
                &stores[i],
                &member,
                &(member_type, member_name.clone()),
                &introduced,
            )?);
            tuple.extend([object_name, member_name]);
        }
        for (i, store) in proof.witness_equalities.iter().enumerate() {
            let completed = SourcePosition {
                before: count + i + 1,
                ..scope
            };
            let equal = self.resolve_fact(store.primary_fact_id(), &completed)?;
            alias_equality_subject(&equal, parameters[i], &proof.statement.equal_tos[i])?;
            self.validate_store(&store.store, &equal)?;
            let name = format!("h_{}", equal.fact_id().value());
            let proposition = self.fact_proposition(&equal, &completed)?;
            lines.push(format!("have {name} : {proposition} := rfl"));
            lines.extend(self.compile_stored_inferences(
                store,
                &equal,
                &(proposition, name),
                &completed,
            )?);
        }
        for (i, (source, result)) in proof
            .statement
            .proof
            .iter()
            .zip(&proof.proof_steps)
            .enumerate()
        {
            validate_statement_capture(source, result)?;
            let prior = SourcePosition {
                before: 2 * count + i,
                ..scope
            };
            lines.push(self.compile_statement_in_scope(result, &prior, i + 1, true)?);
        }
        for (i, (source, check)) in fact
            .facts
            .iter()
            .zip(&proof.obligations.body_checks)
            .enumerate()
        {
            let source = crate::instantiate::quantifier_free_fact_to_fact(source.clone());
            let actual = source_subject(check)?;
            if !instantiated_fact_matches(&source, &actual, &substitution) {
                return Err(LeanCompileError::new(
                    "Witness/BodySubject",
                    "The body check does not instantiate this original existential clause.",
                ));
            }
            let prior = SourcePosition {
                before: 2 * count + proof.proof_steps.len() + i,
                ..scope
            };
            let compiled = self.compile_verify(check, &prior)?;
            let name = format!("h_{}", actual.fact_id().value());
            lines.push(format!("have {name} : {} := {}", compiled.0, compiled.1));
            tuple.push(name);
        }
        if fact.facts.is_empty() {
            tuple.push("True.intro".into());
        }
        lines.push(format!("exact ⟨{}⟩", tuple.join(", ")));
        let body = lines
            .into_iter()
            .enumerate()
            .map(|(i, s)| {
                if i == 0 {
                    s
                } else {
                    format!("  {}", s.replace('\n', "\n  "))
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        self.compile_completed_fact_statement(
            &Fact::ExistFact(fact.clone()),
            (proposition, body),
            &proof.store_and_infer_result,
            &ambient_complete,
            index,
            local,
        )
    }
}
