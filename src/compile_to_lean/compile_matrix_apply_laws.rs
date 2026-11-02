//! Replay the original matrix-action identity/composition contracts.
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
pub(super) enum MatrixApplyLaw {
    Identity,
    Compose,
}

fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir() == n.ir() && f.set == Obj::StandardSet(StandardSet::N))
}
fn vector(fact: &Fact, v: &Obj, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == v.ir()
        && matches!(&f.set, Obj::SetFormer(SetFormer::FiniteSeqSet(p))
            if p.set.as_ref() == &Obj::StandardSet(StandardSet::C) && p.n.ir() == n.ir()))
}
fn matrix(fact: &Fact, a: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == a.ir()
        && matches!(&f.set, Obj::SetFormer(SetFormer::MatrixSet(p))
            if p.set.as_ref() == &Obj::StandardSet(StandardSet::C)
                && p.rows.ir() == m.ir() && p.cols.ir() == n.ir()))
}
fn apply(object: &Obj, a: &Obj, v: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::Apply(p))
        if p.matrix.ir() == a.ir() && p.vector.ir() == v.ir()
            && p.rows.ir() == m.ir() && p.cols.ir() == n.ir())
}

pub(super) fn validate_matrix_apply_law(
    kind: MatrixApplyLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    match kind {
        MatrixApplyLaw::Identity => {
            let [v, n] = args else {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Arguments"));
            };
            if requirements.len() != 2
                || !natural(&requirements[0], n)
                || !vector(&requirements[1], v, n)
            {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Premises"));
            }
            let Obj::MatrixOperator(MatrixOperator::Apply(p)) = &conclusion.left else {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Conclusion"));
            };
            if p.vector.ir() != v.ir()
                || p.rows.ir() != n.ir()
                || p.cols.ir() != n.ir()
                || conclusion.right.ir() != v.ir()
                || !matches!(p.matrix.as_ref(), Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i))
                    if i.order.ir() == n.ir())
            {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Subjects"));
            }
            Ok(2)
        }
        MatrixApplyLaw::Compose => {
            let [a, b, v, m, k, n] = args else {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Arguments"));
            };
            if requirements.len() != 8
                || !natural(&requirements[0], m)
                || !natural(&requirements[1], k)
                || !matrix(&requirements[2], a, m, k)
                || !natural(&requirements[3], k)
                || !natural(&requirements[4], n)
                || !matrix(&requirements[5], b, k, n)
                || !natural(&requirements[6], n)
                || !vector(&requirements[7], v, n)
            {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Premises"));
            }
            let Obj::MatrixOperator(MatrixOperator::Apply(left)) = &conclusion.left else {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Conclusion"));
            };
            if left.vector.ir() != v.ir()
                || left.rows.ir() != m.ir()
                || left.cols.ir() != n.ir()
                || !matches!(left.matrix.as_ref(), Obj::MatrixOperator(MatrixOperator::Multiply(p))
                    if p.left.ir() == a.ir() && p.right.ir() == b.ir()
                        && p.rows.ir() == m.ir() && p.inner.ir() == k.ir() && p.cols.ir() == n.ir())
                || !matches!(&conclusion.right, Obj::MatrixOperator(MatrixOperator::Apply(right))
                    if right.matrix.ir() == a.ir() && right.rows.ir() == m.ir() && right.cols.ir() == k.ir()
                        && apply(&right.vector, b, v, k, n))
            {
                return Err(LeanCompileError::unsupported("MatrixApplyLaw/Subjects"));
            }
            Ok(8)
        }
    }
}

pub(super) fn matrix_apply_law_term(kind: MatrixApplyLaw, root: &str, statement: &str) -> String {
    let law = match kind {
        MatrixApplyLaw::Identity => "Litex.matrixApplyIdentity _outer.val.vector _outer.val.rows _outer.wd.1 _outer.wd.2.2.2",
        MatrixApplyLaw::Compose => "Litex.matrixApplyCompose _outer.val.matrix.val.left _outer.val.matrix.val.right _outer.val.vector _outer.val.rows _outer.val.matrix.val.inner _outer.val.cols _outer.wd.1 _outer.val.matrix.wd.2.1 _outer.wd.2.1 _outer.val.matrix.wd.2.2.2.1 _outer.val.matrix.wd.2.2.2.2 _outer.wd.2.2.2",
    };
    format!("(show {statement} from by\n  let _outer := {root}\n  exact {law}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_apply_theorem(
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
            BuiltinTheoremId::MatrixApplyIdentity => MatrixApplyLaw::Identity,
            BuiltinTheoremId::MatrixApplyCompose => MatrixApplyLaw::Compose,
            _ => return Err(LeanCompileError::unsupported("MatrixApplyLaw/Theorem")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("MatrixApplyLaw/Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "MatrixApplyLaw/TheoremStages",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("MatrixApplyLaw/Conclusion"));
        };
        let count = validate_matrix_apply_law(kind, args, &builtin.requirements, conclusion)?;
        if dom_proofs.len() != count || dom_stores.len() != count {
            return Err(LeanCompileError::unsupported(
                "MatrixApplyLaw/TheoremStages",
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
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "MatrixApplyLaw/RequirementIdentity",
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
        Ok((
            definitions,
            matrix_apply_law_term(kind, &root, &statement),
            builtin.conclusions.clone(),
        ))
    }
}
