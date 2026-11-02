//! Replay distinct original inverse clauses and the actual combined theorem.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

#[derive(Clone, Copy)]
pub(super) enum MatrixInverseLaw {
    // Original producer names: inverse(A)*A is Left, A*inverse(A) is Right.
    Left,
    Right,
}

pub(super) fn validate_matrix_inverse_law(
    kind: MatrixInverseLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let [a, n] = args else {
        return Err(LeanCompileError::unsupported("MatrixInverse/Arguments"));
    };
    if requirements.len() != 4 {
        return Err(LeanCompileError::unsupported("MatrixInverse/Premises"));
    }
    for (index, requirement) in requirements.iter().take(3).enumerate() {
        let valid = if index < 2 {
            matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
        } else {
            matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir()==a.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(p))
                    if p.set.as_ref()==&Obj::StandardSet(StandardSet::C)
                        && p.rows.ir()==n.ir() && p.cols.ir()==n.ir()))
        };
        if !valid {
            return Err(LeanCompileError::unsupported("MatrixInverse/Premise"));
        }
    }
    let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = &requirements[3] else {
        return Err(LeanCompileError::unsupported(
            "MatrixInverse/NonzeroPremise",
        ));
    };
    if !matches!(&nonzero.left, Obj::MatrixOperator(MatrixOperator::Determinant(d))
        if d.matrix.ir()==a.ir() && d.order.ir()==n.ir())
        || !is_exact_zero(&nonzero.right)
    {
        return Err(LeanCompileError::unsupported(
            "MatrixInverse/NonzeroSubject",
        ));
    }
    let Obj::MatrixOperator(MatrixOperator::Multiply(product)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("MatrixInverse/Conclusion"));
    };
    let (inverse, operand) = match kind {
        MatrixInverseLaw::Left => (&product.left, &product.right),
        MatrixInverseLaw::Right => (&product.right, &product.left),
    };
    if operand.ir() != a.ir()
        || product.rows.ir() != n.ir()
        || product.inner.ir() != n.ir()
        || product.cols.ir() != n.ir()
        || !matches!(inverse.as_ref(), Obj::MatrixOperator(MatrixOperator::Inverse(p))
            if p.matrix.ir()==a.ir() && p.order.ir()==n.ir())
        || !matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p))
            if p.order.ir()==n.ir())
    {
        return Err(LeanCompileError::unsupported("MatrixInverse/Subjects"));
    }
    Ok(4)
}

pub(super) fn matrix_inverse_law_term(
    kind: MatrixInverseLaw,
    root: &str,
    statement: &str,
    guard: &str,
) -> String {
    let law = match kind {
        MatrixInverseLaw::Left => format!("Litex.matrixMultiplyInverseLeft _product.val.right _product.val.rows _product.wd.1 _product.wd.2.2.2.2 {guard}"),
        MatrixInverseLaw::Right => format!("Litex.matrixMultiplyInverseRight _product.val.left _product.val.rows _product.wd.1 _product.wd.2.2.2.1 {guard}"),
    };
    format!("(show {statement} from by\n  let _product := {root}\n  exact {law}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_inverse_theorem(
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
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("MatrixInverse/Arguments"));
        };
        if builtin.theorem != BuiltinTheoremId::MatrixInverseLaws
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || dom_proofs.len() != 4
            || dom_stores.len() != 4
            || builtin.conclusions.len() != 2
            || conclusions_wd.len() != 2
        {
            return Err(LeanCompileError::unsupported("MatrixInverse/TheoremStages"));
        }
        let kinds = [MatrixInverseLaw::Right, MatrixInverseLaw::Left];
        for (fact, kind) in builtin.conclusions.iter().zip(kinds) {
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                return Err(LeanCompileError::unsupported("MatrixInverse/Conclusion"));
            };
            validate_matrix_inverse_law(kind, args, &builtin.requirements, conclusion)?;
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
                return Err(LeanCompileError::unsupported(
                    "MatrixInverse/RequirementIdentity",
                ));
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
            before: 4,
            ..*position
        };
        let mut proofs = Vec::new();
        for ((fact, wd), kind) in builtin.conclusions.iter().zip(conclusions_wd).zip(kinds) {
            self.compile_fact_wd(wd, fact, &formed)?;
            let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                unreachable!()
            };
            let root = self.compile_object_reference(&conclusion.left, &scope)?;
            let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
            proofs.push(matrix_inverse_law_term(
                kind,
                &root,
                &statement,
                &format!("h_{}", builtin.requirements[3].fact_id().value()),
            ));
        }
        Ok((
            definitions,
            format!("(And.intro {} {})", proofs[0], proofs[1]),
            builtin.conclusions.clone(),
        ))
    }
}
