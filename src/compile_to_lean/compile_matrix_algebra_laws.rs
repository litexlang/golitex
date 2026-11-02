//! Original associative/distributive matrix schemas and their checked Core laws.
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
pub(super) enum MatrixAlgebraLaw {
    Associative,
    DistributiveLeft,
    DistributiveRight,
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
fn product(object: &Obj, a: &Obj, b: &Obj, m: &Obj, k: &Obj, n: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::Multiply(p))
        if p.left.ir() == a.ir() && p.right.ir() == b.ir() && p.rows.ir() == m.ir()
            && p.inner.ir() == k.ir() && p.cols.ir() == n.ir())
}
fn sum(object: &Obj, a: &Obj, b: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::Add(p))
        if p.left.ir() == a.ir() && p.right.ir() == b.ir()
            && p.rows.ir() == m.ir() && p.cols.ir() == n.ir())
}

pub(super) fn validate_matrix_algebra_law(
    kind: MatrixAlgebraLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let associative = matches!(kind, MatrixAlgebraLaw::Associative);
    if args.len() != if associative { 7 } else { 6 } || requirements.len() != 9 {
        return Err(LeanCompileError::unsupported("MatrixAlgebra/Stages"));
    }
    let (a, b, c, m, k, n) = (
        &args[0],
        &args[1],
        &args[2],
        &args[3],
        &args[4],
        &args[if associative { 6 } else { 5 }],
    );
    let matrices = match kind {
        MatrixAlgebraLaw::Associative => [(a, m, k), (b, k, &args[5]), (c, &args[5], n)],
        MatrixAlgebraLaw::DistributiveLeft => [(a, m, k), (b, k, n), (c, k, n)],
        MatrixAlgebraLaw::DistributiveRight => [(a, m, k), (b, m, k), (c, k, n)],
    };
    for ((object, rows, cols), premise) in matrices.into_iter().zip(requirements.chunks_exact(3)) {
        if !natural(&premise[0], rows)
            || !natural(&premise[1], cols)
            || !matrix(&premise[2], object, rows, cols)
        {
            return Err(LeanCompileError::unsupported("MatrixAlgebra/Premise"));
        }
    }
    let Obj::MatrixOperator(MatrixOperator::Multiply(left)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("MatrixAlgebra/Conclusion"));
    };
    let valid = match kind {
        MatrixAlgebraLaw::Associative => {
            let p = &args[5];
            product(&left.left, a, b, m, k, p)
                && left.right.ir() == c.ir()
                && left.rows.ir() == m.ir()
                && left.inner.ir() == p.ir()
                && left.cols.ir() == n.ir()
                && matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Multiply(right))
                    if right.left.ir() == a.ir() && product(&right.right, b, c, k, p, n)
                        && right.rows.ir() == m.ir() && right.inner.ir() == k.ir() && right.cols.ir() == n.ir())
        }
        MatrixAlgebraLaw::DistributiveLeft => {
            left.left.ir() == a.ir()
                && sum(&left.right, b, c, k, n)
                && left.rows.ir() == m.ir()
                && left.inner.ir() == k.ir()
                && left.cols.ir() == n.ir()
                && matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Add(right))
                    if product(&right.left, a, b, m, k, n) && product(&right.right, a, c, m, k, n)
                        && right.rows.ir() == m.ir() && right.cols.ir() == n.ir())
        }
        MatrixAlgebraLaw::DistributiveRight => {
            sum(&left.left, a, b, m, k)
                && left.right.ir() == c.ir()
                && left.rows.ir() == m.ir()
                && left.inner.ir() == k.ir()
                && left.cols.ir() == n.ir()
                && matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Add(right))
                    if product(&right.left, a, c, m, k, n) && product(&right.right, b, c, m, k, n)
                        && right.rows.ir() == m.ir() && right.cols.ir() == n.ir())
        }
    };
    if !valid {
        return Err(LeanCompileError::unsupported("MatrixAlgebra/Subjects"));
    }
    Ok(9)
}

pub(super) fn matrix_algebra_law_term(
    kind: MatrixAlgebraLaw,
    root: &str,
    statement: &str,
) -> String {
    let law = match kind {
        MatrixAlgebraLaw::Associative => "Litex.matrixMultiplyAssociative _outer.val.left.val.left _outer.val.left.val.right _outer.val.right _outer.val.rows _outer.val.left.val.inner _outer.val.inner _outer.val.cols _outer.wd.1 _outer.val.left.wd.2.1 _outer.wd.2.1 _outer.wd.2.2.1 _outer.val.left.wd.2.2.2.1 _outer.val.left.wd.2.2.2.2 _outer.wd.2.2.2.2",
        MatrixAlgebraLaw::DistributiveLeft => "Litex.matrixMultiplyDistributiveLeft _outer.val.left _outer.val.right.val.left _outer.val.right.val.right _outer.val.rows _outer.val.inner _outer.val.cols _outer.wd.1 _outer.wd.2.1 _outer.wd.2.2.1 _outer.wd.2.2.2.1 _outer.val.right.wd.2.2.1 _outer.val.right.wd.2.2.2",
        MatrixAlgebraLaw::DistributiveRight => "Litex.matrixMultiplyDistributiveRight _outer.val.left.val.left _outer.val.left.val.right _outer.val.right _outer.val.rows _outer.val.inner _outer.val.cols _outer.wd.1 _outer.wd.2.1 _outer.wd.2.2.1 _outer.val.left.wd.2.2.1 _outer.val.left.wd.2.2.2 _outer.wd.2.2.2.2",
    };
    format!("(show {statement} from by\n  let _outer := {root}\n  exact {law}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_algebra_theorem(
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
            BuiltinTheoremId::MatrixMulAssociative => MatrixAlgebraLaw::Associative,
            BuiltinTheoremId::MatrixMulDistributiveLeft => MatrixAlgebraLaw::DistributiveLeft,
            BuiltinTheoremId::MatrixMulDistributiveRight => MatrixAlgebraLaw::DistributiveRight,
            _ => return Err(LeanCompileError::unsupported("MatrixAlgebra/Theorem")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("MatrixAlgebra/Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || dom_proofs.len() != 9
            || dom_stores.len() != 9
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported("MatrixAlgebra/TheoremStages"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("MatrixAlgebra/Conclusion"));
        };
        validate_matrix_algebra_law(kind, args, &builtin.requirements, conclusion)?;
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
                    "MatrixAlgebra/RequirementIdentity",
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
            before: 9,
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
            matrix_algebra_law_term(kind, &root, &statement),
            builtin.conclusions.clone(),
        ))
    }
}
