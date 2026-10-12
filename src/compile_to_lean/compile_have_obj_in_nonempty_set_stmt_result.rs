use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_arbitrary_have_result(
        &self,
        result: &ExecHaveObjInNonemptySetStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecHaveObjInNonemptySetStmtResult::Success(proof) => {
                self.compile_arbitrary_have(proof, position, local)
            }
            ExecHaveObjInNonemptySetStmtResult::Failed(_) => Err(LeanCompileError::new(
                "Declaration/Failed",
                "Failed declaration is not compiler evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_arbitrary_have(
        &self,
        proof: &ExecHaveObjInNonemptySetStmtSuccessResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if proof.auto_opened_struct_layers.is_some()
            || proof.groups.len() != proof.statement.param_def.groups.len()
        {
            return Err(LeanCompileError::unsupported("Have/ContextProfile"));
        }
        let aggregate: Vec<_> = proof
            .groups
            .iter()
            .flat_map(|g| g.defined_params.stored_fact_ids.iter().copied())
            .collect();
        if aggregate != proof.store_and_infer_result.stored_fact_ids {
            return Err(LeanCompileError::new(
                "Have/Aggregate",
                "The group stores do not equal the ordered statement stores.",
            ));
        }
        let grouped: Vec<_> = proof
            .groups
            .iter()
            .flat_map(|g| &g.defined_params.store_and_infer_results)
            .collect();
        if grouped.len() != proof.store_and_infer_result.store_and_infer_results.len()
            || grouped
                .iter()
                .zip(&proof.store_and_infer_result.store_and_infer_results)
                .any(|(group, aggregate)| !std::rc::Rc::ptr_eq(group, aggregate))
        {
            return Err(LeanCompileError::new(
                "Have/SharedStores",
                "Group and aggregate capture do not refer to the same parameter-store executions.",
            ));
        }
        self.validate_parameter_store_capture(&proof.store_and_infer_result)?;
        let mut declarations = Vec::new();
        let mut introduced_count = 0;
        for (group, captured) in proof.statement.param_def.groups.iter().zip(&proof.groups) {
            let source_position = SourcePosition {
                before: introduced_count,
                ..*position
            };
            let group_position = SourcePosition {
                parent: Some(&source_position),
                owner: SourceOwner::HaveGroup(
                    &captured.param_type_well_defined,
                    &captured.nonempty_check,
                ),
                before: 0,
            };
            let position = &group_position;
            if matches!(&group.param_type, ParamType::Set(_)) {
                if !matches!(
                    &captured.param_type_well_defined,
                    ParamTypeWellDefinedProof::Set
                ) || !matches!(&captured.nonempty_check, ParamTypeFactCheckResult::Set)
                {
                    return Err(LeanCompileError::new(
                        "Have/SetStages",
                        "An arbitrary set has set-kind WD and no nonempty obligation.",
                    ));
                }
                self.validate_parameter_store_capture(&captured.defined_params)?;
                if captured.defined_params.store_and_infer_results.len() != group.params.len() {
                    return Err(LeanCompileError::new(
                        "Have/SetStores",
                        "Every arbitrary set needs its original sethood store.",
                    ));
                }
                for (parameter, store) in group
                    .params
                    .iter()
                    .zip(&captured.defined_params.store_and_infer_results)
                {
                    introduced_count += 1;
                    let introduced = SourcePosition {
                        before: introduced_count,
                        ..source_position
                    };
                    let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
                    let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                    match &fact {
                        Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir() == object.ir() => {
                        }
                        _ => {
                            return Err(LeanCompileError::new(
                                "Have/SetSubject",
                                "The captured sethood belongs to another source parameter.",
                            ))
                        }
                    }
                    self.validate_store(&store.store, &fact)?;
                    let id = parameter.id.value();
                    let fact_id = fact.fact_id().value();
                    if local {
                        declarations.push(format!("let _value_i{id} := Litex.semanticObject (M := M) (M.standard Litex.StandardSetValue.complex) (M.standard_isSet Litex.StandardSetValue.complex)"));
                        declarations.push(format!("have h_{fact_id} : Litex.IsSet _value_i{id} := Litex.isSet _value_i{id}"));
                    } else {
                        declarations.push(format!("variable {{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id}) (h_{fact_id} : Litex.IsSet _value_i{id})"));
                    }
                }
                continue;
            }
            let set = match &group.param_type {
                ParamType::Obj(Obj::StandardSet(set)) => set,
                _ => return Err(LeanCompileError::unsupported("Have/NumericCarrier")),
            };
            standard_term(set)?;
            let carrier = Obj::StandardSet(set.clone());
            match &captured.param_type_well_defined {
                ParamTypeWellDefinedProof::Obj(wd) => {
                    self.compile_wd(success_object_wd(wd, &carrier)?, position)?;
                }
                _ => return Err(LeanCompileError::unsupported("Have/CarrierWD")),
            }
            let group_formed = SourcePosition {
                before: 1,
                ..*position
            };
            let position = &group_formed;
            let nonempty = match &captured.nonempty_check {
                ParamTypeFactCheckResult::Obj(result) => self.compile_verify(result, position)?,
                _ => return Err(LeanCompileError::unsupported("Have/NonemptyCheck")),
            };
            let nonempty_subject = match &captured.nonempty_check {
                ParamTypeFactCheckResult::Obj(result) => source_subject(result)?,
                _ => unreachable!(),
            };
            match &nonempty_subject {
                Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact))
                    if fact.set.ir() == carrier.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "Have/NonemptySubject",
                        "The captured nonempty check proves another carrier.",
                    ))
                }
            }
            let check_name = format!("h_{}", nonempty_subject.fact_id().value());
            declarations.push(if local {
                format!("have {check_name} : {} := {}", nonempty.0, nonempty.1)
            } else {
                format!(
                    "theorem {check_name}{} : {} := {}",
                    self.context_header(position),
                    nonempty.0,
                    nonempty.1
                )
            });
            self.validate_parameter_store_capture(&captured.defined_params)?;
            if captured.defined_params.store_and_infer_results.len() != group.params.len() {
                return Err(LeanCompileError::new(
                    "Have/ParameterStores",
                    "Each declared parameter needs its own actual store.",
                ));
            }
            for (parameter, store) in group
                .params
                .iter()
                .zip(&captured.defined_params.store_and_infer_results)
            {
                introduced_count += 1;
                let parameter_position = SourcePosition {
                    before: introduced_count,
                    ..source_position
                };
                let carrier_position = SourcePosition {
                    parent: Some(&parameter_position),
                    owner: SourceOwner::ParamTypeWD(&captured.param_type_well_defined),
                    before: 1,
                };
                let fact = self.resolve_fact(store.primary_fact_id(), &parameter_position)?;
                if local {
                    let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                    if !matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(member))
                        if member.element.ir() == object.ir() && member.set.ir() == carrier.ir())
                    {
                        return Err(LeanCompileError::new(
                            "Have/ParameterSubject",
                            "The captured membership belongs to another local parameter or carrier.",
                        ));
                    }
                    self.validate_store(&store.store, &fact)?;
                    let id = parameter.id.value();
                    let member_id = store.primary_fact_id().value();
                    declarations.push(format!(
                        "obtain ⟨_witness_i{id}, _member_i{id}⟩ := {check_name}"
                    ));
                    declarations.push(format!(
                        "let _value_i{id} := Litex.semanticObject (M := M) _witness_i{id} (M.member_isSet _member_i{id})"
                    ));
                    declarations.push(format!(
                        "have h_{member_id} : Litex.In _value_i{id} {} := _member_i{id}",
                        standard_term(set)?,
                    ));
                } else {
                    let (binders, arguments) = self.introduce_numeric_parameter(
                        parameter,
                        &carrier,
                        store,
                        &carrier_position,
                    )?;
                    declarations.push(format!("variable {}", binders.join(" ")));
                    let _ = arguments;
                }
                let member = (
                    self.fact_proposition(&fact, &carrier_position)?,
                    format!("h_{}", store.primary_fact_id().value()),
                );
                declarations.extend(self.compile_parameter_inferences(
                    store,
                    &fact,
                    &member,
                    &carrier_position,
                )?);
            }
        }
        Ok(declarations.join("\n\n"))
    }
}
