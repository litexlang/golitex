//! Replay both candidate products and the original complex square contexts.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MatrixCandidate/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn square(fact: &Fact, a: &Obj, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==a.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(m))
            if m.set.as_ref()==&Obj::StandardSet(StandardSet::C)
                && m.rows.ir()==n.ir() && m.cols.ir()==n.ir()))
}
fn product_identity(fact: &Fact, left: &Obj, right: &Obj, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::EqualFact(f))
        if matches!(&f.left,Obj::MatrixOperator(MatrixOperator::Multiply(m))
            if m.left.ir()==left.ir() && m.right.ir()==right.ir()
                && m.rows.ir()==n.ir() && m.inner.ir()==n.ir() && m.cols.ir()==n.ir())
        && matches!(&f.right,Obj::MatrixOperator(MatrixOperator::IdentityMatrix(m))
            if m.order.ir()==n.ir()))
}
fn nonzero(fact: &Fact, a: &Obj, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::NotEqualFact(f))
        if matches!(&f.left,Obj::MatrixOperator(MatrixOperator::Determinant(d))
            if d.matrix.ir()==a.ir() && d.order.ir()==n.ir()) && is_exact_zero(&f.right))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_candidate(
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
        let inverse = match builtin.theorem {
            BuiltinTheoremId::MatrixInvertibleFromCandidate => false,
            BuiltinTheoremId::MatrixInverseFromCandidate => true,
            _ => return Err(invalid("Identity")),
        };
        let count = if inverse { 9 } else { 8 };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 3
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, b, n) = (&args[0], &args[1], &args[2]);
        let req = &builtin.requirements;
        for (offset, matrix) in [(0, a), (3, b)] {
            if !natural(&req[offset], n)
                || !natural(&req[offset + 1], n)
                || !square(&req[offset + 2], matrix, n)
            {
                return Err(invalid("ComplexSquareContext"));
            }
        }
        if !product_identity(&req[6], a, b, n) || !product_identity(&req[7], b, a, n) {
            return Err(invalid("OriginalBothProducts"));
        }
        let goal = &builtin.conclusions[0];
        if inverse {
            if !nonzero(&req[8], a, n)
                || !matches!(goal,Fact::AtomicFact(AtomicFact::EqualFact(f))
                    if matches!(&f.left,Obj::MatrixOperator(MatrixOperator::Inverse(m))
                        if m.matrix.ir()==a.ir() && m.order.ir()==n.ir()) && f.right.ir()==b.ir())
            {
                return Err(invalid("OriginalInverseAndGuard"));
            }
        } else if !nonzero(goal, a, n) {
            return Err(invalid("OriginalNonzeroConclusion"));
        }
        let mut definitions = Vec::new();
        let mut refs = Vec::new();
        for (index, ((requirement, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("PremiseIdentity"));
            }
            self.validate_store(&stored.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                stored,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            refs.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let objects = args
            .iter()
            .map(|arg| self.compile_object_reference(arg, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let law = if inverse {
            "matrixInverseOfCandidate"
        } else {
            "matrixCandidateDeterminantNonzero"
        };
        let guard = if inverse {
            format!(" {}", refs[8])
        } else {
            String::new()
        };
        let term = format!(
            "(Litex.{law} {} {} {} {} {} {}{guard})",
            objects.join(" "),
            refs[0],
            refs[2],
            refs[5],
            refs[6],
            refs[7]
        );
        Ok((
            definitions,
            format!("(show {statement} from {term})"),
            builtin.conclusions.clone(),
        ))
    }
}
