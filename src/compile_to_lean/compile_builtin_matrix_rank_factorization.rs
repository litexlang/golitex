//! Rank of the original supplied split factorization; no witness search.
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
    LeanCompileError::unsupported(&format!("RankFactorization/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn matrix(fact: &Fact, a: &Obj, rows: &Obj, cols: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir()
        && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(s))
            if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==rows.ir() && s.cols.ir()==cols.ir()))
}
fn product(obj: &Obj, a: &Obj, b: &Obj, m: &Obj, k: &Obj, n: &Obj) -> bool {
    matches!(obj,Obj::MatrixOperator(MatrixOperator::Multiply(p))
        if p.left.ir()==a.ir() && p.right.ir()==b.ir() && p.rows.ir()==m.ir()
            && p.inner.ir()==k.ir() && p.cols.ir()==n.ir())
}
fn split_identity(fact: &Fact, a: &Obj, b: &Obj, k: &Obj, inner: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::EqualFact(f))
        if product(&f.left,a,b,k,inner,k)
            && matches!(&f.right,Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i)) if i.order.ir()==k.ir()))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_rank_factorization(
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
            return Err(invalid("Arguments"));
        };
        if builtin.theorem != BuiltinTheoremId::MatrixRankFromFactorization
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 8
            || builtin.requirements.len() != 20
            || dom_proofs.len() != 20
            || dom_stores.len() != 20
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, b, c, left, right, m, k, n) = (
            &args[0], &args[1], &args[2], &args[3], &args[4], &args[5], &args[6], &args[7],
        );
        let req = &builtin.requirements;
        for (index, (obj, rows, cols)) in
            [(a, m, n), (b, m, k), (c, k, n), (left, k, m), (right, n, k)]
                .iter()
                .enumerate()
        {
            if !natural(&req[3 * index], rows)
                || !natural(&req[3 * index + 1], cols)
                || !matrix(&req[3 * index + 2], obj, rows, cols)
            {
                return Err(invalid("FiveOriginalMatrixContexts"));
            }
        }
        for (index, bound) in [(15, m), (16, n)] {
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==k.ir() && f.right.ir()==bound.ir())
            {
                return Err(invalid("OriginalInnerDimensionBounds"));
            }
        }
        if !matches!(&req[17],Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==a.ir() && product(&f.right,b,c,m,k,n))
            || !split_identity(&req[18], left, b, k, m)
            || !split_identity(&req[19], c, right, k, n)
        {
            return Err(invalid("OriginalFactorizationAndSplittings"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(goal)) = &builtin.conclusions[0] else {
            return Err(invalid("Conclusion"));
        };
        if goal.right.ir() != k.ir()
            || !matches!(&goal.left,Obj::MatrixOperator(MatrixOperator::Rank(r))
            if r.matrix.ir()==a.ir() && r.rows.ir()==m.ir() && r.cols.ir()==n.ir())
        {
            return Err(invalid("OriginalRankAndDimension"));
        }
        let mut definitions = Vec::new();
        let mut refs = Vec::new();
        for (index, ((requirement, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
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
            before: 20,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let arguments = [0, 4, 1, 5, 8, 11, 14, 17, 18, 19]
            .map(|i| refs[i].as_str())
            .join(" ");
        let term = format!(
            "Litex.matrixRankFromSplitFactorization {} {arguments}",
            objects.join(" ")
        );
        Ok((
            definitions,
            format!("(show {statement} from {term})"),
            builtin.conclusions.clone(),
        ))
    }
}
