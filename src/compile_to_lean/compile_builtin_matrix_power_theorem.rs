//! Replay the source's zero and successor matrix-power theorem applications.
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
        let successor = match builtin.theorem {
            BuiltinTheoremId::MatrixPowerZero => false,
            BuiltinTheoremId::MatrixPowerSuccessor => true,
            _ => return Err(LeanCompileError::unsupported("MatrixPower/Theorem")),
        };
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
        let count = if successor { 4 } else { 3 };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != count - 1
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
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
        let (left, right) = if successor {
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
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("MatrixPower/Conclusion"));
        };
        if conclusion.left.ir() != left.ir() || conclusion.right.ir() != right.ir() {
            return Err(LeanCompileError::unsupported(
                "MatrixPower/ConclusionSubject",
            ));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            let (subject, set) = match index {
                0 | 1 => (n, Obj::StandardSet(StandardSet::N)),
                2 => (
                    a,
                    matrix_space(Obj::StandardSet(StandardSet::C), n.clone(), n.clone()),
                ),
                _ => (&arguments[2], Obj::StandardSet(StandardSet::N)),
            };
            if !matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==set.ir())
                || source_subject(checked)? != *requirement
            {
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
        let law = if successor {
            format!(
                "Litex.matrixPowerSuccessor _power.val.matrix _power.val.order _power.val.exponent.val.left h_{}",
                builtin.requirements[3].fact_id().value()
            )
        } else {
            "Litex.matrixPowerZero _power.val.matrix _power.val.order".to_string()
        };
        Ok((
            definitions,
            format!("(show {statement} from by\n  let _power := {root}\n  exact {law}\n)"),
            builtin.conclusions.clone(),
        ))
    }
}
