//! Native triangles for the exact original vector formula or matrix sum.
use super::compile_real_set_bounds::contains_parameter;
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
    LeanCompileError::unsupported(&format!("NormTriangle/{stage}"))
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
fn norm(obj: &Obj, vector: bool, a: &Obj, m: &Obj, n: &Obj) -> bool {
    match obj {
        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p)) => {
            vector && p.vector.ir() == a.ir() && p.dimension.ir() == n.ir()
        }
        Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p)) => {
            !vector && p.matrix.ir() == a.ir() && p.rows.ir() == m.ir() && p.cols.ir() == n.ir()
        }
        _ => false,
    }
}
fn validate_vector_sum(obj: &Obj, a: &Obj, b: &Obj, n: &Obj) -> Result<(), LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = obj else {
        return Err(invalid("OriginalSumFormula"));
    };
    let [group] = literal.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("FormulaBinder"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("FormulaBinder"));
    };
    let Obj::SetFormer(SetFormer::ClosedRange(range)) = group.param_type.as_ref() else {
        return Err(invalid("FormulaDomain"));
    };
    if closed_integer(&range.start) != Some(1)
        || range.end.ir() != n.ir()
        || literal.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        || !literal.body.dom_facts.is_empty()
        || [a, b, n].iter().any(|o| contains_parameter(o, binder.id))
    {
        return Err(invalid("ExactFormulaDomain"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = literal.equal_to.as_ref() else {
        return Err(invalid("FormulaSum"));
    };
    for (term, original) in [(&sum.left, a), (&sum.right, b)] {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = term.as_ref() else {
            return Err(invalid("OriginalUnitCoefficient"));
        };
        let Obj::FnObj(call) = product.right.as_ref() else {
            return Err(invalid("OriginalVectorCall"));
        };
        let [args] = call.body.as_slice() else {
            return Err(invalid("OriginalVectorCall"));
        };
        let [arg] = args.as_slice() else {
            return Err(invalid("OriginalVectorCall"));
        };
        if closed_integer(&product.left) != Some(1)
            || *call.head != FnObjHead::from_obj(original.clone())
            || !matches!(arg.as_ref(),Obj::Identifier(IdentifierObj::Plain {id,..}) if *id==binder.id)
        {
            return Err(invalid("ExactUnitVectorSum"));
        }
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_norm_triangle(
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
        let is_vector = match builtin.theorem {
            BuiltinTheoremId::EuclideanNormTriangle => true,
            BuiltinTheoremId::FrobeniusNormTriangle => false,
            _ => return Err(invalid("Theorem")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let arity = if is_vector { 3 } else { 4 };
        let count = if is_vector { 4 } else { 6 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let (a, b, m, n) = (&args[0], &args[1], &args[2], &args[arity - 1]);
        let req = &builtin.requirements;
        let valid = if is_vector {
            natural(&req[0], n)
                && vector(&req[1], a, n)
                && natural(&req[2], n)
                && vector(&req[3], b, n)
        } else {
            natural(&req[0], m)
                && natural(&req[1], n)
                && matrix(&req[2], a, m, n)
                && natural(&req[3], m)
                && natural(&req[4], n)
                && matrix(&req[5], b, m, n)
        };
        if !valid {
            return Err(invalid("OriginalCarrierContexts"));
        }
        let Fact::AtomicFact(atomic @ AtomicFact::LessEqualFact(goal)) = &builtin.conclusions[0]
        else {
            return Err(invalid("OriginalInequality"));
        };
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalInequalityWD"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(right)) = &goal.right else {
            return Err(invalid("RightNormSum"));
        };
        if !norm(&right.left, is_vector, a, m, n) || !norm(&right.right, is_vector, b, m, n) {
            return Err(invalid("OrderedOriginalNorms"));
        }
        match &goal.left {
            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p))
                if is_vector && p.dimension.ir() == n.ir() =>
            {
                validate_vector_sum(&p.vector, a, b, n)?;
            }
            Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p))
                if !is_vector && p.rows.ir() == m.ir() && p.cols.ir() == n.ir() =>
            {
                if !matches!(p.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::Add(sum))
                    if sum.left.ir()==a.ir() && sum.right.ir()==b.ir() && sum.rows.ir()==m.ir() && sum.cols.ir()==n.ir())
                {
                    return Err(invalid("OriginalMatrixSum"));
                }
            }
            _ => return Err(invalid("OriginalSumNorm")),
        }
        let mut definitions = Vec::new();
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
            definitions.extend(self.compile_stored_inferences(
                stored,
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
        let bindings = self.compile_atomic_wd_locals(wd, atomic, &formed)?;
        let complete = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, 2),
            usize::MAX,
        );
        let root = self
            .compile_object_reference(&goal.left, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let term = if is_vector {
            let a = self.compile_object_reference(a, &complete)?;
            let b = self.compile_object_reference(b, &complete)?;
            let ha = format!("h_{}", req[1].fact_id().value());
            let hb = format!("h_{}", req[3].fact_id().value());
            format!("(by\n  let _triangle_norm := {root}\n  exact Litex.euclideanNormTriangleFormula _triangle_norm _triangle_norm.val.vector {a} {b} {ha} {hb} (by rfl) (by rfl) (by rfl)\n)")
        } else {
            format!("(by\n  let _triangle_norm := {root}\n  exact Litex.frobeniusNormTriangleEntrywise _triangle_norm.val.matrix (by rfl)\n)")
        };
        let proof = Self::scope_equal_wd_proof(statement.clone(), term, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
