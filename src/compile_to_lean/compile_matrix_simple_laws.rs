//! Original identity/zero multiplication clauses share validation and Core laws.
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
pub(super) enum SimpleMatrixLaw {
    IdentityLeft,
    IdentityRight,
    ZeroRight,
    ZeroLeft,
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
fn identity(object: &Obj, n: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p)) if p.order.ir() == n.ir())
}
fn zero(object: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(object, Obj::MatrixOperator(MatrixOperator::ZeroMatrix(p))
        if p.rows.ir() == m.ir() && p.cols.ir() == n.ir())
}

pub(super) fn validate_simple_matrix_law(
    kind: SimpleMatrixLaw,
    args: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let is_zero = matches!(kind, SimpleMatrixLaw::ZeroLeft | SimpleMatrixLaw::ZeroRight);
    let count = if is_zero { 4 } else { 3 };
    if args.len() != count || requirements.len() != count {
        return Err(LeanCompileError::unsupported("MatrixSimple/Stages"));
    }
    let (a, m, n) = (&args[0], &args[1], &args[2]);
    if !natural(&requirements[0], m)
        || !natural(&requirements[1], n)
        || !matrix(&requirements[2], a, m, n)
        || (is_zero && !natural(&requirements[3], &args[3]))
    {
        return Err(LeanCompileError::unsupported("MatrixSimple/Premise"));
    }
    let Obj::MatrixOperator(MatrixOperator::Multiply(p)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("MatrixSimple/Conclusion"));
    };
    let valid = match kind {
        SimpleMatrixLaw::IdentityLeft => {
            identity(&p.left, m)
                && p.right.ir() == a.ir()
                && p.rows.ir() == m.ir()
                && p.inner.ir() == m.ir()
                && p.cols.ir() == n.ir()
                && conclusion.right.ir() == a.ir()
        }
        SimpleMatrixLaw::IdentityRight => {
            p.left.ir() == a.ir()
                && identity(&p.right, n)
                && p.rows.ir() == m.ir()
                && p.inner.ir() == n.ir()
                && p.cols.ir() == n.ir()
                && conclusion.right.ir() == a.ir()
        }
        SimpleMatrixLaw::ZeroRight => {
            p.left.ir() == a.ir()
                && zero(&p.right, n, &args[3])
                && p.rows.ir() == m.ir()
                && p.inner.ir() == n.ir()
                && p.cols.ir() == args[3].ir()
                && zero(&conclusion.right, m, &args[3])
        }
        SimpleMatrixLaw::ZeroLeft => {
            zero(&p.left, &args[3], m)
                && p.right.ir() == a.ir()
                && p.rows.ir() == args[3].ir()
                && p.inner.ir() == m.ir()
                && p.cols.ir() == n.ir()
                && zero(&conclusion.right, &args[3], n)
        }
    };
    if !valid {
        return Err(LeanCompileError::unsupported("MatrixSimple/Subjects"));
    }
    Ok(count)
}

pub(super) fn simple_matrix_law_term(kind: SimpleMatrixLaw, root: &str, statement: &str) -> String {
    let law = match kind {
        SimpleMatrixLaw::IdentityLeft => "Litex.matrixMultiplyIdentityLeft _product.val.right _product.val.rows _product.val.cols _product.wd.1 _product.wd.2.2.1 _product.wd.2.2.2.2",
        SimpleMatrixLaw::IdentityRight => "Litex.matrixMultiplyIdentityRight _product.val.left _product.val.rows _product.val.cols _product.wd.1 _product.wd.2.2.1 _product.wd.2.2.2.1",
        SimpleMatrixLaw::ZeroRight => "Litex.matrixMultiplyZeroRight _product.val.left _product.val.rows _product.val.inner _product.val.cols _product.wd.1 _product.wd.2.1 _product.wd.2.2.1 _product.wd.2.2.2.1",
        SimpleMatrixLaw::ZeroLeft => "Litex.matrixMultiplyZeroLeft _product.val.right _product.val.inner _product.val.cols _product.val.rows _product.wd.2.1 _product.wd.2.2.1 _product.wd.1 _product.wd.2.2.2.2",
    };
    format!("(show {statement} from by\n  let _product := {root}\n  exact {law}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_simple_theorem(
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
        let kinds = match builtin.theorem {
            BuiltinTheoremId::MatrixMulIdentity => [
                SimpleMatrixLaw::IdentityLeft,
                SimpleMatrixLaw::IdentityRight,
            ],
            BuiltinTheoremId::MatrixMulZero => {
                [SimpleMatrixLaw::ZeroRight, SimpleMatrixLaw::ZeroLeft]
            }
            _ => return Err(LeanCompileError::unsupported("MatrixSimple/Theorem")),
        };
        let count = if builtin.theorem == BuiltinTheoremId::MatrixMulIdentity {
            3
        } else {
            4
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(LeanCompileError::unsupported("MatrixSimple/Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 2
            || conclusions_wd.len() != 2
        {
            return Err(LeanCompileError::unsupported("MatrixSimple/TheoremStages"));
        }
        for (fact, kind) in builtin.conclusions.iter().zip(kinds) {
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                return Err(LeanCompileError::unsupported("MatrixSimple/Conclusion"));
            };
            validate_simple_matrix_law(kind, args, &builtin.requirements, conclusion)?;
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
                    "MatrixSimple/RequirementIdentity",
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
        let mut proofs = Vec::new();
        for ((fact, wd), kind) in builtin.conclusions.iter().zip(conclusions_wd).zip(kinds) {
            self.compile_fact_wd(wd, fact, &formed)?;
            let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = fact else {
                unreachable!()
            };
            let root = self.compile_object_reference(&conclusion.left, &scope)?;
            let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
            proofs.push(simple_matrix_law_term(kind, &root, &statement));
        }
        Ok((
            definitions,
            format!("(And.intro {} {})", proofs[0], proofs[1]),
            builtin.conclusions.clone(),
        ))
    }
}
