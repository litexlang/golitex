use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_fact_stmt_result::validate_finite_signature;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::function_application;
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::execute::execute_release_tuple_def_stmt::{
    ExecReleaseTupleDefStmtResult, ExecReleaseTupleDefStmtSuccess,
};
use crate::prelude::*;

/// Function WD, target WD, return proofs, membership WD, coordinate proofs,
/// then all stores. Verification never sees the command's later publications.
pub(super) fn tuple_release_publication_start(proof: &ExecReleaseTupleDefStmtSuccess) -> usize {
    3 + proof.return_proofs.len() + proof.coordinate_proofs.len()
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_release_tuple_definition(
        &self,
        result: &ExecReleaseTupleDefStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseTupleDefStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("ReleaseTuple/Failed"));
        };
        validate_finite_signature(&proof.shape)?;
        let rule = &proof.membership_rule;
        let n = proof.shape.source.dimension();
        if proof.domain.target != proof.shape.signature
            || rule.theorem != BuiltinTheoremId::FunctionSetMember
            || rule.arguments.len() != 2
            || rule.conclusions.len() != 1
            || rule.requirements.len() != proof.return_proofs.len()
            || proof.coordinate_proofs.len() != n
            || proof.stored.len() != n + 1
        {
            return Err(LeanCompileError::unsupported("ReleaseTuple/Stages"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &rule.conclusions[0] else {
            return Err(LeanCompileError::unsupported("ReleaseTuple/Membership"));
        };
        let Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) = &member.set else {
            return Err(LeanCompileError::unsupported("ReleaseTuple/Carrier"));
        };
        if member.element.ir() != proof.statement.obj.ir()
            || rule.arguments[0].ir() != member.element.ir()
            || rule.arguments[1].ir() != member.set.ir()
            || sequence.set.ir() != proof.shape.signature.ret_set.ir()
            || !matches!(sequence.n.as_ref(), Obj::Literal(Literal::Number(k)) if k.normalized_value == n.to_string())
        {
            return Err(LeanCompileError::unsupported("ReleaseTuple/Subject"));
        }
        ensure_object(&proof.statement.obj, &proof.domain.function_wd)?;
        ensure_object(
            &Obj::FunctionSpace(FunctionSpace::FnSet(proof.domain.target.clone())),
            &proof.domain.target_wd,
        )?;
        let function = self.compile_wd(&proof.domain.function_wd, position)?;
        let target = self.compile_wd(
            &proof.domain.target_wd,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let shaped = SourcePosition {
            before: 2,
            ..*position
        };
        self.compile_cart_shape_member(&proof.statement.obj, &proof.shape.source, &shaped)?;
        let mut definitions = vec![
            format!("let _membership_function := {function}"),
            format!("let _membership_target := {target}"),
        ];
        let mut references = Vec::new();
        for (offset, (requirement, checked)) in rule
            .requirements
            .iter()
            .zip(&proof.return_proofs)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("ReleaseTuple/ReturnSubject"));
            }
            let prior = SourcePosition {
                before: 2 + offset,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            let name = format!("h_{}", requirement.fact_id().value());
            definitions.push(format!("have {name} : {} := {}", compiled.0, compiled.1));
            references.push(name);
        }
        let membership_stage = 2 + proof.return_proofs.len();
        let prior = SourcePosition {
            before: membership_stage,
            ..*position
        };
        self.compile_fact_wd(&proof.membership_wd, &rule.conclusions[0], &prior)?;
        let formed = SourcePosition::new(
            Some(&prior),
            SourceOwner::FactWD(&proof.membership_wd),
            usize::MAX,
        );
        let application = self.compile_builtin_function_membership(
            member,
            &proof.domain,
            &rule.requirements,
            &references,
            &formed,
        )?;
        let proposition = self.fact_proposition(&rule.conclusions[0], &formed)?;
        let mut conclusions = vec![(
            rule.conclusions[0].clone(),
            (
                proposition,
                format!(
                    "(by\n  {}\n  exact {application})",
                    definitions.join("\n").replace('\n', "\n  ")
                ),
            ),
        )];
        for (offset, checked) in proof.coordinate_proofs.iter().enumerate() {
            let fact = source_subject(checked)?;
            let number = Obj::Literal(Literal::Number(Number {
                normalized_value: (offset + 1).to_string(),
            }));
            let call = function_application(&proof.statement.obj, vec![Box::new(number)])
                .map_err(|e| LeanCompileError::new("ReleaseTuple/Coordinate", &e))?;
            let matches = match (&proof.shape.source, &fact) {
                (
                    KnownTupleShapeProof::TupleEquality(shape),
                    Fact::AtomicFact(AtomicFact::EqualFact(f)),
                ) => f.left.ir() == call.ir() && f.right.ir() == shape.value.args[offset].ir(),
                (shape, Fact::AtomicFact(AtomicFact::InFact(f))) => {
                    f.element.ir() == call.ir()
                        && shape
                            .cart()
                            .is_some_and(|cart| f.set.ir() == cart.args[offset].ir())
                }
                _ => false,
            };
            if !matches {
                return Err(LeanCompileError::unsupported(
                    "ReleaseTuple/CoordinateSubject",
                ));
            }
            let prior = SourcePosition {
                before: membership_stage + 1 + offset,
                ..*position
            };
            conclusions.push((fact, self.compile_verify(checked, &prior)?));
        }
        let head = tuple_release_publication_start(proof);
        let mut emitted = Vec::new();
        let mut ids = std::collections::HashSet::new();
        for (offset, ((fact, compiled), store)) in conclusions.iter().zip(&proof.stored).enumerate()
        {
            if !ids.insert(fact.fact_id()) {
                return Err(LeanCompileError::unsupported("ReleaseTuple/DuplicateFact"));
            }
            self.validate_store(&store.store, fact)?;
            let prior = SourcePosition {
                before: head + offset,
                ..*position
            };
            emitted.push(self.emit_fact(fact, compiled.clone(), index, local, &prior)?);
            let published = SourcePosition {
                before: head + offset + 1,
                ..*position
            };
            let name = format!("h_{}", fact.fact_id().value());
            let reference = if local {
                name
            } else {
                self.context_application(&name, &published)
            };
            emitted.extend(self.compile_stored_inferences(
                store,
                fact,
                &(compiled.0.clone(), reference),
                &published,
            )?);
        }
        Ok(emitted.join("\n\n"))
    }
}
