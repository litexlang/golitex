//! Replay the two original rectangular product-rank bounds and all contexts.
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
    LeanCompileError::unsupported(&format!("MatrixRankProduct/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn matrix(fact: &Fact, a: &Obj, rows: &Obj, cols: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==a.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(m))
            if m.set.as_ref()==&Obj::StandardSet(StandardSet::C)
                && m.rows.ir()==rows.ir() && m.cols.ir()==cols.ir()))
}
fn rank(obj: &Obj, a: &Obj, rows: &Obj, cols: &Obj) -> bool {
    matches!(obj,Obj::MatrixOperator(MatrixOperator::Rank(r))
        if r.matrix.ir()==a.ir() && r.rows.ir()==rows.ir() && r.cols.ir()==cols.ir())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_rank_product(
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
        if builtin.theorem != BuiltinTheoremId::MatrixRankProduct
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 5
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != 6
            || dom_proofs.len() != 6
            || dom_stores.len() != 6
            || builtin.conclusions.len() != 2
            || conclusions_wd.len() != 2
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, b, m, k, n) = (&args[0], &args[1], &args[2], &args[3], &args[4]);
        let req = &builtin.requirements;
        if !natural(&req[0], m)
            || !natural(&req[1], k)
            || !matrix(&req[2], a, m, k)
            || !natural(&req[3], k)
            || !natural(&req[4], n)
            || !matrix(&req[5], b, k, n)
        {
            return Err(invalid("OriginalRectangularContexts"));
        }
        for (index, fact) in builtin.conclusions.iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::LessEqualFact(bound)) = fact else {
                return Err(invalid("OriginalBound"));
            };
            let Obj::MatrixOperator(MatrixOperator::Rank(product_rank)) = &bound.left else {
                return Err(invalid("ProductRank"));
            };
            let Obj::MatrixOperator(MatrixOperator::Multiply(product)) =
                product_rank.matrix.as_ref()
            else {
                return Err(invalid("Product"));
            };
            let (factor, rows, cols) = if index == 0 { (a, m, k) } else { (b, k, n) };
            if product_rank.rows.ir() != m.ir()
                || product_rank.cols.ir() != n.ir()
                || product.left.ir() != a.ir()
                || product.right.ir() != b.ir()
                || product.rows.ir() != m.ir()
                || product.inner.ir() != k.ir()
                || product.cols.ir() != n.ir()
                || !rank(&bound.right, factor, rows, cols)
            {
                return Err(invalid("ExactOrderedBounds"));
            }
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
            before: 6,
            ..*position
        };
        let mut statements = Vec::new();
        for (fact, wd) in builtin.conclusions.iter().zip(conclusions_wd) {
            self.compile_fact_wd(wd, fact, &formed)?;
            statements.push(self.compile_formed_fact_proposition(wd, fact, &formed)?);
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|arg| self.compile_object_reference(arg, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let term = format!(
            "Litex.matrixRankProductBounds {} {} {} {} {} {}",
            objects.join(" "),
            refs[0],
            refs[1],
            refs[4],
            refs[2],
            refs[5]
        );
        Ok((
            definitions,
            format!(
                "(show ({}) ∧ ({}) from ({term}))",
                statements[0], statements[1]
            ),
            builtin.conclusions.clone(),
        ))
    }
}
