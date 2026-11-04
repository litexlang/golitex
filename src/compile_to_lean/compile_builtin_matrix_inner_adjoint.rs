//! Original rectangular adjoint/inner-product schema and all seven contexts.
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
    LeanCompileError::unsupported(&format!("MatrixInnerAdjoint/{stage}"))
}
fn natural(fact: &Fact, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
}
fn vector(fact: &Fact, a: &Obj, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir()
        && matches!(&f.set,Obj::SetFormer(SetFormer::FiniteSeqSet(s))
            if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.n.ir()==n.ir()))
}
fn matrix(fact: &Fact, a: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir()
        && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(s))
            if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==m.ir() && s.cols.ir()==n.ir()))
}
fn applies(obj: &Obj, a: &Obj, u: &Obj, m: &Obj, n: &Obj) -> bool {
    matches!(obj,Obj::MatrixOperator(MatrixOperator::Apply(p))
        if p.matrix.ir()==a.ir() && p.vector.ir()==u.ir() && p.rows.ir()==m.ir() && p.cols.ir()==n.ir())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_inner_adjoint(
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
        if builtin.theorem != BuiltinTheoremId::MatrixInnerProductAdjoint
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 5
            || builtin.requirements.len() != 7
            || dom_proofs.len() != 7
            || dom_stores.len() != 7
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, u, v, m, n) = (&args[0], &args[1], &args[2], &args[3], &args[4]);
        let req = &builtin.requirements;
        if !natural(&req[0], m)
            || !natural(&req[1], n)
            || !matrix(&req[2], a, m, n)
            || !natural(&req[3], n)
            || !vector(&req[4], u, n)
            || !natural(&req[5], m)
            || !vector(&req[6], v, m)
        {
            return Err(invalid("OriginalRectangularContexts"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(goal)) = &builtin.conclusions[0] else {
            return Err(invalid("Conclusion"));
        };
        let FactWellDefinedProof::Equality(wd) = &conclusions_wd[0] else {
            return Err(invalid("ConclusionWD"));
        };
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(left)) = &goal.left else {
            return Err(invalid("LeftInnerProduct"));
        };
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(right)) = &goal.right else {
            return Err(invalid("RightInnerProduct"));
        };
        if left.dimension.ir() != m.ir()
            || left.right.ir() != v.ir()
            || !applies(&left.left, a, u, m, n)
            || right.dimension.ir() != n.ir()
            || right.left.ir() != u.ir()
        {
            return Err(invalid("OriginalOrderedInnerProducts"));
        }
        let Obj::MatrixOperator(MatrixOperator::Apply(action)) = right.right.as_ref() else {
            return Err(invalid("AdjointApplication"));
        };
        if action.vector.ir() != v.ir()
            || action.rows.ir() != n.ir()
            || action.cols.ir() != m.ir()
            || !matches!(action.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(p))
                if p.matrix.ir()==a.ir() && p.rows.ir()==m.ir() && p.cols.ir()==n.ir())
        {
            return Err(invalid("OriginalConjugateTransposeAndSwappedDimensions"));
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
            before: 7,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let bindings = self.compile_equal_wd_locals(goal, wd, &formed)?;
        let complete =
            SourcePosition::new(Some(&formed), SourceOwner::EqualWDLocals(wd, 2), usize::MAX);
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &complete))
            .collect::<Result<Vec<_>, _>>()?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let references = [0, 1, 2, 4, 6].map(|i| refs[i].as_str()).join(" ");
        let term = format!(
            "Litex.matrixInnerProductAdjoint {} {references}",
            objects.join(" ")
        );
        let proof = Self::scope_equal_wd_proof(statement.clone(), term, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
