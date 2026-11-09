use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_have_equal_result(
        &self,
        result: &ExecHaveObjEqualStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecHaveObjEqualStmtResult::Success(proof) => {
                self.compile_have_equal(proof, position, local)
            }
            ExecHaveObjEqualStmtResult::Failed(_) => Err(LeanCompileError::new(
                "Declaration/Failed",
                "Failed declaration is not compiler evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_have_equal(
        &self,
        proof: &ExecHaveObjEqualStmtSuccessResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let groups = &proof.statement.param_def.groups;
        let parameters: Vec<_> = groups
            .iter()
            .flat_map(|group| group.params.iter().map(|p| (p, &group.param_type)))
            .collect();
        let count = parameters.len();
        if count == 0
            || count != proof.statement.objs_equal_to.len()
            || count != proof.equal_to_well_defined.len()
            || count != proof.membership_checks.len()
            || proof.type_preflight.param_type_well_defined.len() != groups.len()
        {
            return Err(LeanCompileError::new(
                "HaveEqual/Stages",
                "Typed definition evidence has different parameter, value or membership stages.",
            ));
        }
        self.validate_parameter_store_capture(&proof.store_and_infer_result)?;
        let stores = &proof.store_and_infer_result.store_and_infer_results;
        if stores.len() != 2 * count {
            return Err(LeanCompileError::new(
                "HaveEqual/Stores",
                "Typed definitions need ordered membership and equality stores.",
            ));
        }
        let type_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::HaveEqualType(proof),
            before: 0,
        };
        let type_check = (|| {
            let position = &type_position;
            let mut introduced_count = 0;
            for (group, wd) in groups
                .iter()
                .zip(&proof.type_preflight.param_type_well_defined)
            {
                let prior = SourcePosition {
                    before: introduced_count,
                    ..*position
                };
                match (&group.param_type, wd) {
                    (ParamType::Obj(set), ParamTypeWellDefinedProof::Obj(proof)) => {
                        ensure_object(set, proof)?;
                        self.compile_wd(proof, &prior)?;
                    }
                    (ParamType::Set(_), ParamTypeWellDefinedProof::Set)
                    | (ParamType::NonemptySet(_), ParamTypeWellDefinedProof::NonemptySet)
                    | (ParamType::FiniteSet(_), ParamTypeWellDefinedProof::FiniteSet) => {}
                    _ => return Err(LeanCompileError::unsupported("HaveEqual/ParameterKind")),
                }
                introduced_count += group.params.len();
            }
            Ok(())
        })();
        type_check?;
        let mut values = Vec::new();
        for (index, (value, wd)) in proof
            .statement
            .objs_equal_to
            .iter()
            .zip(&proof.equal_to_well_defined)
            .enumerate()
        {
            values.push(self.compile_wd(
                success_object_wd(wd, value)?,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let mut members = Vec::new();
        let mut offset = 0;
        let mut substitution = std::collections::HashMap::new();
        for group in groups {
            let group_start = offset;
            for _ in &group.params {
                let member = self.compile_verify(
                    &proof.membership_checks[offset],
                    &SourcePosition {
                        before: count + offset,
                        ..*position
                    },
                )?;
                if !parameter_type_fact_matches(
                    &group.param_type,
                    &proof.statement.objs_equal_to[offset],
                    &source_subject(&proof.membership_checks[offset])?,
                    &substitution,
                ) {
                    return Err(LeanCompileError::new(
                        "HaveEqual/Membership",
                        "The value proof does not certify the declared value and carrier.",
                    ));
                }
                members.push(member);
                offset += 1;
            }
            // Execution instantiates each group's carrier using the values
            // of preceding groups, before publishing the new bindings.
            for (parameter, value) in group
                .params
                .iter()
                .zip(&proof.statement.objs_equal_to[group_start..offset])
            {
                substitution.insert(parameter.id, value.clone());
            }
        }
        let mut declarations = Vec::new();
        if proof.type_preflight.auto_opened_struct_layers.is_some()
            || proof.auto_opened_struct_layers.is_some()
        {
            let (binders, introductions, mut checks) = self.compile_quantified_head(
                &proof.statement.param_def,
                &[],
                &proof.type_preflight,
                &[],
                &type_position,
            )?;
            checks.push("exact True.intro".into());
            // Apply the original hypothetical preflight to the checked values.
            // This constrains its host universes even in a discarded local block;
            // none of its private binders or facts are exported as alias evidence.
            let arguments = values
                .iter()
                .zip(&members)
                .map(|(value, member)| format!("{value} {}", member.1))
                .collect::<Vec<_>>()
                .join(" ");
            let body = format!(
                "True :=\n  ((show ∀ {}, True from by\n    intro {}\n    {}\n  ) {arguments})",
                binders.join(" "),
                introductions.join(" "),
                checks.join("\n").replace('\n', "\n    ")
            );
            let name = format!("_have_type_checks_i{}", parameters[0].0.id.value());
            declarations.push(if local {
                format!("have {name} : {body}")
            } else {
                format!(
                    "include M in\ntheorem {name}{} : {body}",
                    self.context_header(position)?
                )
            });
        }
        for (index, (parameter, kind)) in parameters.iter().enumerate() {
            let alias_position = SourcePosition {
                before: 2 * count + index + 1,
                ..*position
            };
            let position = &alias_position;
            let equal = self.resolve_fact(stores[count + index].primary_fact_id(), position)?;
            self.validate_store(&stores[count + index].store, &equal)?;
            let left = alias_equality_subject(
                &equal,
                parameter,
                &proof.statement.objs_equal_to[index],
                position,
                &self.runtime,
            )?;
            for subject in &stores[count + index].formed_subjects {
                if subject.argument_index != 1
                    || self.resolve_wd(subject.wd_id, position)?.ir()
                        != proof.statement.objs_equal_to[index].ir()
                {
                    return Err(LeanCompileError::new(
                        "WD/HaveEqualRegistration",
                        "The equality store must register the original RHS value.",
                    ));
                }
            }
            declarations.push(self.bind_alias(
                parameter,
                left,
                &proof.statement.objs_equal_to[index],
                &values[index],
                local,
                position,
            )?);
            let member_fact = self.resolve_fact(stores[index].primary_fact_id(), position)?;
            let Obj::Identifier(identifier) = left else {
                return Err(LeanCompileError::unsupported("HaveEqual/StoredIdentifier"));
            };
            let published = crate::execute::parameter_substitution_for_surface(
                identifier,
                &proof.statement.param_def,
            );
            if !parameter_type_fact_matches(kind, left, &member_fact, &published) {
                return Err(LeanCompileError::new(
                    "HaveEqual/Store",
                    "The stored member does not belong to this declaration.",
                ));
            }
            self.validate_store(&stores[index].store, &member_fact)?;
            let member = (
                self.fact_proposition(&member_fact, position)?,
                members[index].1.clone(),
            );

            declarations.push(self.emit_internal_fact(&member_fact, &member, position)?);
            let name = format!("h_{}", member_fact.fact_id().value());
            let member_reference = if local {
                name
            } else {
                self.context_application(&name, position)
            };
            declarations.extend(self.compile_parameter_inferences(
                &stores[index],
                &member_fact,
                &(member.0, member_reference),
                position,
            )?);
            let equal_proof = (
                self.fact_proposition(&equal, position)?,
                format!("(Litex.sameRefl {})", values[index]),
            );
            declarations.push(self.emit_internal_fact(&equal, &equal_proof, position)?);
            declarations.extend(self.compile_stored_inferences(
                &stores[count + index],
                &equal,
                &equal_proof,
                position,
            )?);
        }
        let complete = SourcePosition {
            before: 3 * count,
            ..*position
        };
        declarations.extend(self.compile_auto_struct_layers(
            groups,
            &stores[..count],
            proof.auto_opened_struct_layers.as_deref(),
            &complete,
        )?);
        Ok(declarations.join("\n"))
    }
}
