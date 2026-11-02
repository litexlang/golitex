//! Replay distinct original adjugate clauses and the actual combined theorem.
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
pub(super) enum MatrixAdjugateLaw {
    // Original producer names: adj(A)*A is Left, A*adj(A) is Right.
    Left,
    Right,
}

pub(super) fn validate_matrix_adjugate_law(
    kind: MatrixAdjugateLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let [a, n] = args else {
        return Err(LeanCompileError::unsupported("MatrixAdjugate/Arguments"));
    };
    if requirements.len() != 3 {
        return Err(LeanCompileError::unsupported("MatrixAdjugate/Premises"));
    }
    for (index, requirement) in requirements.iter().enumerate() {
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
            return Err(LeanCompileError::unsupported("MatrixAdjugate/Premise"));
        }
    }
    let Obj::MatrixOperator(MatrixOperator::Multiply(product)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("MatrixAdjugate/Conclusion"));
    };
    let (adjugate, operand) = match kind {
        MatrixAdjugateLaw::Left => (&product.left, &product.right),
        MatrixAdjugateLaw::Right => (&product.right, &product.left),
    };
    if operand.ir() != a.ir()
        || product.rows.ir() != n.ir()
        || product.inner.ir() != n.ir()
        || product.cols.ir() != n.ir()
        || !matches!(adjugate.as_ref(), Obj::MatrixOperator(MatrixOperator::Adjugate(p))
            if p.matrix.ir()==a.ir() && p.order.ir()==n.ir())
        || !matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Scale(p))
            if p.rows.ir()==n.ir() && p.cols.ir()==n.ir()
                && matches!(p.scalar.as_ref(),Obj::MatrixOperator(MatrixOperator::Determinant(d))
                    if d.matrix.ir()==a.ir() && d.order.ir()==n.ir())
                && matches!(p.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i))
                    if i.order.ir()==n.ir()))
    {
        return Err(LeanCompileError::unsupported("MatrixAdjugate/Subjects"));
    }
    Ok(3)
}

pub(super) fn matrix_adjugate_law_term(
    kind: MatrixAdjugateLaw,
    root: &str,
    statement: &str,
) -> String {
    let law = match kind {
        MatrixAdjugateLaw::Left => "Litex.matrixMultiplyAdjugateLeft _product.val.right _product.val.rows _product.wd.1 _product.wd.2.2.2.2",
        MatrixAdjugateLaw::Right => "Litex.matrixMultiplyAdjugateRight _product.val.left _product.val.rows _product.wd.1 _product.wd.2.2.2.1",
    };
    format!("(show {statement} from by\n  let _product := {root}\n  exact {law}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_adjugate_theorem(
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
            return Err(LeanCompileError::unsupported("MatrixAdjugate/Arguments"));
        };
        if builtin.theorem != BuiltinTheoremId::MatrixAdjugateIdentity
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || dom_proofs.len() != 3
            || dom_stores.len() != 3
            || builtin.conclusions.len() != 2
            || conclusions_wd.len() != 2
        {
            return Err(LeanCompileError::unsupported(
                "MatrixAdjugate/TheoremStages",
            ));
        }
        let kinds = [MatrixAdjugateLaw::Right, MatrixAdjugateLaw::Left];
        for (fact, kind) in builtin.conclusions.iter().zip(kinds) {
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                return Err(LeanCompileError::unsupported("MatrixAdjugate/Conclusion"));
            };
            validate_matrix_adjugate_law(kind, args, &builtin.requirements, conclusion)?;
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
                    "MatrixAdjugate/RequirementIdentity",
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
            before: 3,
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
            proofs.push(matrix_adjugate_law_term(kind, &root, &statement));
        }
        Ok((
            definitions,
            format!("(And.intro {} {})", proofs[0], proofs[1]),
            builtin.conclusions.clone(),
        ))
    }
}
