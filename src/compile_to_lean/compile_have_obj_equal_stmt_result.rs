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
        let parameters: Vec<_> = groups.iter().flat_map(|group| &group.params).collect();
        let count = parameters.len();
        if count == 0
            || count != proof.statement.objs_equal_to.len()
            || count != proof.equal_to_well_defined.len()
            || count != proof.membership_checks.len()
            || proof.type_preflight.param_type_well_defined.len() != groups.len()
            || proof.type_preflight.auto_opened_struct_layers.is_some()
            || proof.auto_opened_struct_layers.is_some()
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
            for (group, wd) in groups
                .iter()
                .zip(&proof.type_preflight.param_type_well_defined)
            {
                match (&group.param_type, wd) {
                    (ParamType::Obj(set), ParamTypeWellDefinedProof::Obj(proof)) => {
                        ensure_object(set, proof)?;
                        self.compile_wd(proof, position)?;
                    }
                    (ParamType::Set(_), ParamTypeWellDefinedProof::Set) => {}
                    _ => return Err(LeanCompileError::unsupported("HaveEqual/ParameterKind")),
                }
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
        for group in groups {
            let set = match &group.param_type {
                ParamType::Obj(set) => Some(set),
                ParamType::Set(_) => None,
                _ => return Err(LeanCompileError::unsupported("HaveEqual/ParameterKind")),
            };
            for _ in &group.params {
                let member = self.compile_verify(
                    &proof.membership_checks[offset],
                    &SourcePosition {
                        before: count + offset,
                        ..*position
                    },
                )?;
                match (&source_subject(&proof.membership_checks[offset])?, set) {
                    (Fact::AtomicFact(AtomicFact::InFact(f)), Some(set))
                        if f.element.ir() == proof.statement.objs_equal_to[offset].ir()
                            && f.set.ir() == set.ir() => {}
                    (Fact::AtomicFact(AtomicFact::IsSetFact(f)), None)
                        if f.set.ir() == proof.statement.objs_equal_to[offset].ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "HaveEqual/Membership",
                            "The value proof does not certify the declared value and carrier.",
                        ))
                    }
                }
                members.push(member);
                offset += 1;
            }
        }
        let mut declarations = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            let alias_position = SourcePosition {
                before: 2 * count + index + 1,
                ..*position
            };
            let position = &alias_position;
            let equal = self.resolve_fact(stores[count + index].primary_fact_id(), position)?;
            self.validate_store(&stores[count + index].store, &equal)?;
            let left =
                alias_equality_subject(&equal, parameter, &proof.statement.objs_equal_to[index])?;
            declarations.push(self.bind_alias(
                parameter,
                left,
                &proof.statement.objs_equal_to[index],
                &values[index],
                local,
                position,
            )?);
            let member_fact = self.resolve_fact(stores[index].primary_fact_id(), position)?;
            match (
                &member_fact,
                &source_subject(&proof.membership_checks[index])?,
            ) {
                (
                    Fact::AtomicFact(AtomicFact::InFact(stored)),
                    Fact::AtomicFact(AtomicFact::InFact(checked)),
                ) if stored.element.ir() == left.ir() && stored.set.ir() == checked.set.ir() => {}
                (
                    Fact::AtomicFact(AtomicFact::IsSetFact(stored)),
                    Fact::AtomicFact(AtomicFact::IsSetFact(checked)),
                ) if stored.set.ir() == left.ir()
                    && checked.set.ir() == proof.statement.objs_equal_to[index].ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "HaveEqual/Store",
                        "The stored member does not belong to this declaration.",
                    ))
                }
            }
            self.validate_store(&stores[index].store, &member_fact)?;
            let member = (
                self.fact_proposition(&member_fact, position)?,
                members[index].1.clone(),
            );

            declarations.push(self.emit_internal_fact(&member_fact, &member, position)?);
            declarations.extend(self.compile_parameter_inferences(
                &stores[index],
                &member_fact,
                &member,
                position,
            )?);
            let equal_proof = (
                self.fact_proposition(&equal, position)?,
                format!("(Litex.sameRefl {})", values[index]),
            );
            declarations.push(self.emit_internal_fact(&equal, &equal_proof, position)?);
        }
        Ok(declarations.join("\n"))
    }
}
