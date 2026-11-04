//! Explicit rank laws from the original theorem result and ordered premises.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_rank_theorem(
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
        if builtin.theorem == BuiltinTheoremId::MatrixRankFromFactorization {
            return self.compile_builtin_matrix_rank_factorization(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if builtin.theorem == BuiltinTheoremId::MatrixRankProduct {
            return self.compile_builtin_matrix_rank_product(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if builtin.theorem == BuiltinTheoremId::MatrixRankInvertible {
            return self.compile_builtin_rank_invertible_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        use BuiltinTheoremId::{
            MatrixRankAdjoint, MatrixRankBounds, MatrixRankIdentity, MatrixRankTranspose,
            MatrixRankZero,
        };
        let transform = matches!(builtin.theorem, MatrixRankTranspose | MatrixRankAdjoint);
        let (arity, count) = match builtin.theorem {
            MatrixRankBounds => (3, 3),
            MatrixRankZero => (2, 1),
            MatrixRankIdentity => (1, 1),
            MatrixRankTranspose | MatrixRankAdjoint => (3, 1),
            _ => return Err(LeanCompileError::unsupported("Rank/Theorem")),
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported("Rank/TheoremContract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("Rank/Arguments"));
        };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != arity
            || builtin.requirements.len() != arity
            || dom_proofs.len() != arity
            || dom_stores.len() != arity
            || builtin.conclusions.len() != count
            || conclusions_wd.len() != count
        {
            return Err(LeanCompileError::unsupported("Rank/TheoremStages"));
        }
        let (rows, cols) = match builtin.theorem {
            MatrixRankBounds | MatrixRankTranspose | MatrixRankAdjoint => {
                (&arguments[1], &arguments[2])
            }
            MatrixRankZero => (&arguments[0], &arguments[1]),
            _ => (&arguments[0], &arguments[0]),
        };
        let native = match &builtin.conclusions[0] {
            Fact::AtomicFact(AtomicFact::InFact(f))
                if builtin.theorem == MatrixRankBounds
                    && f.set == Obj::StandardSet(StandardSet::N) =>
            {
                &f.element
            }
            Fact::AtomicFact(AtomicFact::EqualFact(f))
                if builtin.theorem == MatrixRankZero && closed_integer(&f.right) == Some(0) =>
            {
                &f.left
            }
            Fact::AtomicFact(AtomicFact::EqualFact(f))
                if builtin.theorem == MatrixRankIdentity && f.right.ir() == rows.ir() =>
            {
                &f.left
            }
            Fact::AtomicFact(AtomicFact::EqualFact(f)) if transform => &f.left,
            _ => return Err(LeanCompileError::unsupported("Rank/FirstConclusion")),
        };
        if matches!(builtin.theorem, MatrixRankZero | MatrixRankIdentity) {
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0]
            else {
                return Err(LeanCompileError::unsupported("Rank/FirstConclusion"));
            };
            validate_simple_rank_law(
                builtin.theorem,
                arguments,
                &builtin.requirements,
                conclusion,
            )?;
        }
        if transform {
            let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0]
            else {
                unreachable!()
            };
            validate_rank_transform_law(
                builtin.theorem,
                arguments,
                &builtin.requirements,
                conclusion,
            )?;
        }
        let Obj::MatrixOperator(MatrixOperator::Rank(rank)) = native else {
            return Err(LeanCompileError::unsupported("Rank/ConclusionObject"));
        };
        let matrix_matches = match builtin.theorem {
            MatrixRankBounds => rank.matrix.ir() == arguments[0].ir(),
            MatrixRankZero => {
                matches!(rank.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::ZeroMatrix(p)) if p.rows.ir()==rows.ir() && p.cols.ir()==cols.ir())
            }
            MatrixRankTranspose | MatrixRankAdjoint => true,
            _ => {
                matches!(rank.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p)) if p.order.ir()==rows.ir())
            }
        };
        let (output_rows, output_cols) = if transform {
            (cols, rows)
        } else {
            (rows, cols)
        };
        if !matrix_matches
            || rank.rows.ir() != output_rows.ir()
            || rank.cols.ir() != output_cols.ir()
        {
            return Err(LeanCompileError::unsupported("Rank/ConclusionDimensions"));
        }
        if builtin.theorem == MatrixRankBounds {
            for (index, dimension) in [rows, cols].iter().enumerate() {
                if !matches!(&builtin.conclusions[index+1],Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==native.ir() && f.right.ir()==dimension.ir())
                {
                    return Err(LeanCompileError::unsupported("Rank/BoundConclusion"));
                }
            }
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            let expected = if index < 2 {
                let subject = if index == 0 { rows } else { cols };
                matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set==Obj::StandardSet(StandardSet::N))
            } else {
                matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==(if transform { &arguments[0] } else { rank.matrix.as_ref() }).ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(m)) if m.set.as_ref()==&Obj::StandardSet(StandardSet::C) && m.rows.ir()==rows.ir() && m.cols.ir()==cols.ir()))
            };
            if !expected || source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("Rank/TheoremPremise"));
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
            before: arity,
            ..*position
        };
        let mut proofs = Vec::new();
        for (index, (fact, wd)) in builtin.conclusions.iter().zip(conclusions_wd).enumerate() {
            self.compile_fact_wd(wd, fact, &formed)?;
            let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let root = self.compile_object_reference(native, &scope)?;
            let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
            if transform {
                proofs.push(rank_transform_law_term(builtin.theorem, &root, &statement)?);
                continue;
            }
            if matches!(builtin.theorem, MatrixRankZero | MatrixRankIdentity) {
                proofs.push(simple_rank_law_term(builtin.theorem, &root, &statement)?);
                continue;
            }
            let law = match index {
                0 => "Litex.matrixRankInN _rank",
                1 => "Litex.matrixRankLeRows _rank",
                _ => "Litex.matrixRankLeCols _rank",
            };
            proofs.push(format!(
                "(show {statement} from by\n  let _rank := {root}\n  exact {law}\n)"
            ));
        }
        Ok((
            definitions,
            proofs
                .into_iter()
                .rev()
                .reduce(|right, left| format!("(And.intro {left} {right})"))
                .expect("rank conclusions"),
            builtin.conclusions.clone(),
        ))
    }
}

pub(in crate::compile_to_lean) fn validate_simple_rank_law(
    theorem: BuiltinTheoremId,
    arguments: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let identity = match theorem {
        BuiltinTheoremId::MatrixRankZero => false,
        BuiltinTheoremId::MatrixRankIdentity => true,
        _ => return Err(LeanCompileError::unsupported("Rank/Theorem")),
    };
    let count = if identity { 1 } else { 2 };
    if arguments.len() != count || requirements.len() != count {
        return Err(LeanCompileError::unsupported("Rank/TheoremStages"));
    }
    let rows = &arguments[0];
    let cols = &arguments[usize::from(!identity)];
    let Obj::MatrixOperator(MatrixOperator::Rank(rank)) = &conclusion.left else {
        return Err(LeanCompileError::unsupported("Rank/ConclusionObject"));
    };
    let matrix_matches = if identity {
        matches!(rank.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::IdentityMatrix(p)) if p.order.ir()==rows.ir())
    } else {
        matches!(rank.matrix.as_ref(),Obj::MatrixOperator(MatrixOperator::ZeroMatrix(p)) if p.rows.ir()==rows.ir() && p.cols.ir()==cols.ir())
    };
    if !matrix_matches
        || rank.rows.ir() != rows.ir()
        || rank.cols.ir() != cols.ir()
        || if identity {
            conclusion.right.ir() != rows.ir()
        } else {
            closed_integer(&conclusion.right) != Some(0)
        }
    {
        return Err(LeanCompileError::unsupported("Rank/ConclusionDimensions"));
    }
    for (argument, requirement) in arguments.iter().zip(requirements) {
        if !matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==argument.ir() && f.set==Obj::StandardSet(StandardSet::N))
        {
            return Err(LeanCompileError::unsupported("Rank/TheoremPremise"));
        }
    }
    Ok(count)
}

pub(in crate::compile_to_lean) fn simple_rank_law_term(
    theorem: BuiltinTheoremId,
    root: &str,
    statement: &str,
) -> Result<String, LeanCompileError> {
    let law = match theorem {
        BuiltinTheoremId::MatrixRankZero => {
            "Litex.matrixRankZero _rank.val.rows _rank.val.cols _rank.wd.1 _rank.wd.2.1"
        }
        BuiltinTheoremId::MatrixRankIdentity => {
            "Litex.matrixRankIdentity _rank.val.rows _rank.wd.1"
        }
        _ => return Err(LeanCompileError::unsupported("Rank/Theorem")),
    };
    Ok(format!(
        "(show {statement} from by\n  let _rank := {root}\n  exact {law}\n)"
    ))
}

pub(in crate::compile_to_lean) fn validate_rank_transform_law(
    theorem: BuiltinTheoremId,
    arguments: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    let adjoint = match theorem {
        BuiltinTheoremId::MatrixRankTranspose => false,
        BuiltinTheoremId::MatrixRankAdjoint => true,
        _ => return Err(LeanCompileError::unsupported("RankTransform/Theorem")),
    };
    let [a, m, n] = arguments else {
        return Err(LeanCompileError::unsupported("RankTransform/Arguments"));
    };
    if requirements.len() != 3 {
        return Err(LeanCompileError::unsupported("RankTransform/Requirements"));
    }
    let (
        Obj::MatrixOperator(MatrixOperator::Rank(left)),
        Obj::MatrixOperator(MatrixOperator::Rank(right)),
    ) = (&conclusion.left, &conclusion.right)
    else {
        return Err(LeanCompileError::unsupported("RankTransform/Conclusion"));
    };
    let transformed = match left.matrix.as_ref() {
        Obj::MatrixOperator(MatrixOperator::Transpose(p)) if !adjoint => {
            p.matrix.ir() == a.ir() && p.rows.ir() == m.ir() && p.cols.ir() == n.ir()
        }
        Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(p)) if adjoint => {
            p.matrix.ir() == a.ir() && p.rows.ir() == m.ir() && p.cols.ir() == n.ir()
        }
        _ => false,
    };
    if !transformed
        || left.rows.ir() != n.ir()
        || left.cols.ir() != m.ir()
        || right.matrix.ir() != a.ir()
        || right.rows.ir() != m.ir()
        || right.cols.ir() != n.ir()
    {
        return Err(LeanCompileError::unsupported("RankTransform/Dimensions"));
    }
    for (index, requirement) in requirements.iter().enumerate() {
        let expected = match index {
            0 | 1 => {
                matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==arguments[index+1].ir() && f.set==Obj::StandardSet(StandardSet::N))
            }
            _ => {
                matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir() && matches!(&f.set, Obj::SetFormer(SetFormer::MatrixSet(s)) if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==m.ir() && s.cols.ir()==n.ir()))
            }
        };
        if !expected {
            return Err(LeanCompileError::unsupported("RankTransform/Premise"));
        }
    }
    Ok(3)
}

pub(in crate::compile_to_lean) fn rank_transform_law_term(
    theorem: BuiltinTheoremId,
    root: &str,
    statement: &str,
) -> Result<String, LeanCompileError> {
    let name = match theorem {
        BuiltinTheoremId::MatrixRankTranspose => "matrixRankTranspose",
        BuiltinTheoremId::MatrixRankAdjoint => "matrixRankAdjoint",
        _ => return Err(LeanCompileError::unsupported("RankTransform/Theorem")),
    };
    Ok(format!("(show {statement} from by\n  let _rank := {root}\n  exact Litex.{name} _rank.val.matrix\n)"))
}

// Original guarded full-rank clause; no inverse construction or new search.
pub(in crate::compile_to_lean) fn validate_rank_invertible_law(
    theorem: BuiltinTheoremId,
    arguments: &[Obj],
    requirements: &[Fact],
    conclusion: &EqualFact,
) -> Result<usize, LeanCompileError> {
    if theorem != BuiltinTheoremId::MatrixRankInvertible {
        return Err(LeanCompileError::unsupported("RankInvertible/Theorem"));
    }
    let [a, n] = arguments else {
        return Err(LeanCompileError::unsupported("RankInvertible/Arguments"));
    };
    if requirements.len() != 4 {
        return Err(LeanCompileError::unsupported("RankInvertible/Premises"));
    }
    for requirement in &requirements[..2] {
        if !matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
        {
            return Err(LeanCompileError::unsupported("RankInvertible/NaturalOrder"));
        }
    }
    if !matches!(&requirements[2], Fact::AtomicFact(AtomicFact::InFact(f))
        if f.element.ir()==a.ir() && matches!(&f.set, Obj::SetFormer(SetFormer::MatrixSet(p))
            if p.set.as_ref()==&Obj::StandardSet(StandardSet::C)
                && p.rows.ir()==n.ir() && p.cols.ir()==n.ir()))
        || !matches!(&requirements[3], Fact::AtomicFact(AtomicFact::NotEqualFact(f))
            if is_exact_zero(&f.right) && matches!(&f.left,Obj::MatrixOperator(MatrixOperator::Determinant(d))
                if d.matrix.ir()==a.ir() && d.order.ir()==n.ir()))
    {
        return Err(LeanCompileError::unsupported(
            "RankInvertible/CarrierOrGuard",
        ));
    }
    if conclusion.right.ir() != n.ir()
        || !matches!(&conclusion.left, Obj::MatrixOperator(MatrixOperator::Rank(p))
            if p.matrix.ir()==a.ir() && p.rows.ir()==n.ir() && p.cols.ir()==n.ir())
    {
        return Err(LeanCompileError::unsupported("RankInvertible/Subjects"));
    }
    Ok(4)
}

pub(in crate::compile_to_lean) fn rank_invertible_law_term(
    root: &str,
    statement: &str,
    guard: &str,
) -> String {
    format!("(show {statement} from by\n  let _rank := {root}\n  exact Litex.matrixRankInvertible _rank.val.matrix _rank.val.rows _rank.wd.1 {guard}\n)")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_rank_invertible_theorem(
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
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("RankInvertible/Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || dom_proofs.len() != 4
            || dom_stores.len() != 4
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "RankInvertible/TheoremStages",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("RankInvertible/Conclusion"));
        };
        validate_rank_invertible_law(
            builtin.theorem,
            arguments,
            &builtin.requirements,
            conclusion,
        )?;
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
                    "RankInvertible/RequirementIdentity",
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
            before: 4,
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
            rank_invertible_law_term(
                &root,
                &statement,
                &format!("h_{}", builtin.requirements[3].fact_id().value()),
            ),
            builtin.conclusions.clone(),
        ))
    }
}
