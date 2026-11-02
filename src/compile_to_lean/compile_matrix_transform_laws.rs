//! Original product transpose/adjoint schemas and their proved Core laws.
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
pub(super) enum MatrixTransformLaw {
    Transpose,
    Adjoint,
}

fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir() == n.ir() && f.set == Obj::StandardSet(StandardSet::N))
}
fn matrix(fact: &Fact, a: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == a.ir()
        && matches!(&f.set, Obj::SetFormer(SetFormer::MatrixSet(p))
            if p.set.as_ref() == &Obj::StandardSet(StandardSet::C)
                && p.rows.ir() == m.ir() && p.cols.ir() == n.ir()))
}
fn parts(object: &Obj, kind: MatrixTransformLaw) -> Option<(&Obj, &Obj, &Obj)> {
    match (kind, object) {
        (MatrixTransformLaw::Transpose, Obj::MatrixOperator(MatrixOperator::Transpose(p))) => {
            Some((&p.matrix, &p.rows, &p.cols))
        }
        (
            MatrixTransformLaw::Adjoint,
            Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(p)),
        ) => Some((&p.matrix, &p.rows, &p.cols)),
        _ => None,
    }
}
fn transformed(object: &Obj, kind: MatrixTransformLaw, a: &Obj, m: &Obj, n: &Obj) -> bool {
    parts(object, kind).is_some_and(|(value, rows, cols)| {
        value.ir() == a.ir() && rows.ir() == m.ir() && cols.ir() == n.ir()
    })
}

pub(super) fn validate_matrix_transform_law(
    kind: MatrixTransformLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let [a, b, m, k, n] = args else {
        return Err(LeanCompileError::unsupported(
            "MatrixTransformLaw/Arguments",
        ));
    };
    if requirements.len() != 6
        || !natural(&requirements[0], m)
        || !natural(&requirements[1], k)
        || !matrix(&requirements[2], a, m, k)
        || !natural(&requirements[3], k)
        || !natural(&requirements[4], n)
        || !matrix(&requirements[5], b, k, n)
    {
        return Err(LeanCompileError::unsupported("MatrixTransformLaw/Premises"));
    }
    let Some((subject, rows, cols)) = parts(&conclusion.left, kind) else {
        return Err(LeanCompileError::unsupported(
            "MatrixTransformLaw/Conclusion",
        ));
    };
    if rows.ir() != m.ir()
        || cols.ir() != n.ir()
        || !matches!(subject, Obj::MatrixOperator(MatrixOperator::Multiply(p))
            if p.left.ir() == a.ir() && p.right.ir() == b.ir()
                && p.rows.ir() == m.ir() && p.inner.ir() == k.ir() && p.cols.ir() == n.ir())
        || !matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Multiply(p))
            if transformed(&p.left, kind, b, k, n) && transformed(&p.right, kind, a, m, k)
                && p.rows.ir() == n.ir() && p.inner.ir() == k.ir() && p.cols.ir() == m.ir())
    {
        return Err(LeanCompileError::unsupported("MatrixTransformLaw/Subjects"));
    }
    Ok(6)
}

pub(super) fn matrix_transform_law_term(
    kind: MatrixTransformLaw,
    root: &str,
    statement: &str,
) -> String {
    let theorem = match kind {
        MatrixTransformLaw::Transpose => "Litex.matrixMultiplyTranspose",
        MatrixTransformLaw::Adjoint => "Litex.matrixMultiplyAdjoint",
    };
    format!("(show {statement} from by\n  let _outer := {root}\n  exact {theorem} _outer.val.matrix.val.left _outer.val.matrix.val.right _outer.val.rows _outer.val.matrix.val.inner _outer.val.cols _outer.wd.1 _outer.val.matrix.wd.2.1 _outer.wd.2.1 _outer.val.matrix.wd.2.2.2.1 _outer.val.matrix.wd.2.2.2.2\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_transform_theorem(
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
        let kind = match builtin.theorem {
            BuiltinTheoremId::MatrixTransposeMul => MatrixTransformLaw::Transpose,
            BuiltinTheoremId::MatrixAdjointMul => MatrixTransformLaw::Adjoint,
            _ => return Err(LeanCompileError::unsupported("MatrixTransformLaw/Theorem")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported(
                "MatrixTransformLaw/Arguments",
            ));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || dom_proofs.len() != 6
            || dom_stores.len() != 6
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "MatrixTransformLaw/TheoremStages",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported(
                "MatrixTransformLaw/Conclusion",
            ));
        };
        validate_matrix_transform_law(kind, args, &builtin.requirements, conclusion)?;
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
                    "MatrixTransformLaw/RequirementIdentity",
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
            before: 6,
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
        Ok((
            definitions,
            matrix_transform_law_term(kind, &root, &statement),
            builtin.conclusions.clone(),
        ))
    }
}
