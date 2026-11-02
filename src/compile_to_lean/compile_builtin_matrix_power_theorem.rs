//! Replay original zero, successor and addition matrix-power applications.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::matrix_operations::{add, identity, matrix_multiply};
use crate::execute::execute_fact_stmt::native_matrix::{matrix_number, matrix_space};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_power_theorem(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported("MatrixPower/TheoremContract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("MatrixPower/Arguments"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = builtin
            .conclusions
            .first()
            .ok_or_else(|| LeanCompileError::unsupported("MatrixPower/Conclusion"))?
        else {
            return Err(LeanCompileError::unsupported("MatrixPower/Conclusion"));
        };
        let count = validate_matrix_power_law(
            builtin.theorem,
            arguments,
            &builtin.requirements,
            conclusion,
        )?;
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported("MatrixPower/TheoremStages"));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("MatrixPower/TheoremPremise"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let root = self.compile_object_reference(&conclusion.left, &scope)?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let guard = builtin
            .requirements
            .get(3)
            .map(|fact| format!("h_{}", fact.fact_id().value()));
        let proof = if builtin.theorem == BuiltinTheoremId::MatrixPowerAdd {
            matrix_power_add_law_term(
                &root,
                &statement,
                &format!("h_{}", builtin.requirements[3].fact_id().value()),
                &format!("h_{}", builtin.requirements[4].fact_id().value()),
            )
        } else {
            matrix_power_law_term(builtin.theorem, &root, &statement, guard.as_deref())?
        };
        Ok((definitions, proof, builtin.conclusions.clone()))
    }
}

pub(in crate::compile_to_lean) fn validate_matrix_power_law(
    theorem: BuiltinTheoremId,
    arguments: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let count = match theorem {
        BuiltinTheoremId::MatrixPowerZero => 3,
        BuiltinTheoremId::MatrixPowerSuccessor => 4,
        BuiltinTheoremId::MatrixPowerAdd => 5,
        _ => return Err(LeanCompileError::unsupported("MatrixPower/Theorem")),
    };
    if arguments.len() != count - 1 || requirements.len() != count {
        return Err(LeanCompileError::unsupported("MatrixPower/TheoremStages"));
    }
    let (a, n) = (&arguments[0], &arguments[1]);
    let power = |exponent: Obj| {
        Obj::MatrixOperator(MatrixOperator::Power(MatrixPower {
            matrix: Box::new(a.clone()),
            order: Box::new(n.clone()),
            exponent: Box::new(exponent),
        }))
    };
    let (left, right) = if theorem == BuiltinTheoremId::MatrixPowerAdd {
        (
            power(add(arguments[2].clone(), arguments[3].clone())),
            matrix_multiply(
                power(arguments[2].clone()),
                power(arguments[3].clone()),
                n.clone(),
                n.clone(),
                n.clone(),
            ),
        )
    } else if theorem == BuiltinTheoremId::MatrixPowerSuccessor {
        (
            power(add(arguments[2].clone(), matrix_number(1))),
            matrix_multiply(
                power(arguments[2].clone()),
                a.clone(),
                n.clone(),
                n.clone(),
                n.clone(),
            ),
        )
    } else {
        (power(matrix_number(0)), identity(n.clone()))
    };
    if conclusion.left.ir() != left.ir() || conclusion.right.ir() != right.ir() {
        return Err(LeanCompileError::unsupported(
            "MatrixPower/ConclusionSubject",
        ));
    }
    for (index, requirement) in requirements.iter().enumerate() {
        let (subject, set) = match index {
            0 | 1 => (n, Obj::StandardSet(StandardSet::N)),
            2 => (
                a,
                matrix_space(Obj::StandardSet(StandardSet::C), n.clone(), n.clone()),
            ),
            i => (&arguments[i - 1], Obj::StandardSet(StandardSet::N)),
        };
        if !matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==set.ir())
        {
            return Err(LeanCompileError::unsupported("MatrixPower/TheoremPremise"));
        }
    }
    Ok(count)
}

pub(in crate::compile_to_lean) fn matrix_power_add_law_term(
    root: &str,
    statement: &str,
    left_guard: &str,
    right_guard: &str,
) -> String {
    format!("(show {statement} from by\n  let _power := {root}\n  exact Litex.matrixPowerAdd _power.val.matrix _power.val.order _power.val.exponent.val.left _power.val.exponent.val.right _power.wd.1 {left_guard} {right_guard} _power.wd.2.2\n)")
}

pub(in crate::compile_to_lean) fn matrix_power_law_term(
    theorem: BuiltinTheoremId,
    root: &str,
    statement: &str,
    successor_guard: Option<&str>,
) -> Result<String, LeanCompileError> {
    let law = match theorem {
        BuiltinTheoremId::MatrixPowerZero if successor_guard.is_none() =>
            "Litex.matrixPowerZero _power.val.matrix _power.val.order".to_string(),
        BuiltinTheoremId::MatrixPowerSuccessor => format!(
            "Litex.matrixPowerSuccessor _power.val.matrix _power.val.order _power.val.exponent.val.left {}",
            successor_guard.ok_or_else(|| LeanCompileError::unsupported("MatrixPower/SuccessorGuard"))?),
        _ => return Err(LeanCompileError::unsupported("MatrixPower/Theorem")),
    };
    Ok(format!(
        "(show {statement} from by\n  let _power := {root}\n  exact {law}\n)"
    ))
}
