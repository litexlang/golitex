//! Natural-valued matrix rank with the original rectangular-matrix WD.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_rank_congruence(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::MatrixOperator(MatrixOperator::Rank(left)),
            Obj::MatrixOperator(MatrixOperator::Rank(right)),
        ) = (&fact.left, &fact.right)
        else {
            return Err(LeanCompileError::unsupported(
                "Matrix/RankCongruenceSubject",
            ));
        };
        if children.len() != 3 {
            return Err(LeanCompileError::unsupported(
                "Matrix/RankCongruenceChildren",
            ));
        }
        let mut proofs = Vec::new();
        for (index, ((a, b), child)) in [
            (&left.matrix, &right.matrix),
            (&left.rows, &right.rows),
            (&left.cols, &right.cols),
        ]
        .into_iter()
        .zip(children)
        .enumerate()
        {
            if !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==a.ir() && f.right.ir()==b.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/RankCongruenceChildSubject",
                ));
            }
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let proof = self.compile_verify(child, &prior)?.1;
            let formed = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
            let a = self.compile_object_reference(a, &formed)?;
            let b = self.compile_object_reference(b, &formed)?;
            proofs.push(format!(
                "(show Litex.denote {a} = Litex.denote {b} from {proof})"
            ));
        }
        Ok(format!(
            "(@congr M.Value M.Value _ _ _ _ (congrArg₂ (fun a m => Litex.matrixRankValue (M := M) a m) {} {}) {})",
            proofs[0], proofs[1], proofs[2]
        ))
    }

    pub(in crate::compile_to_lean) fn compile_matrix_rank_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Rank(m), MatrixOperatorObjWellDefinedProofByDef::Rank(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/RankWD"));
        };
        if p.child_obj_well_defined.len() != 3 || p.requirement_fact_verified.len() != 3 {
            return Err(LeanCompileError::unsupported("Matrix/RankWDStages"));
        }
        for (index, subject) in [&m.rows, &m.cols, &m.matrix].iter().enumerate() {
            let target = if index < 2 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: m.rows.clone(),
                    cols: m.cols.clone(),
                }))
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==target.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/RankWDPremise"));
            }
        }
        let mut arguments = Vec::new();
        for (index, subject) in [&m.matrix, &m.rows, &m.cols].iter().enumerate() {
            ensure_object(subject, &p.child_obj_well_defined[index])?;
            arguments.push(self.compile_wd(
                &p.child_obj_well_defined[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, requirement) in p.requirement_fact_verified.iter().enumerate() {
            arguments.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: 3 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixRank {})", arguments.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_matrix_rank_member(
        &self,
        fact: &InFact,
        target: &StandardSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(fact.element, Obj::MatrixOperator(MatrixOperator::Rank(_)))
            || fact.set != Obj::StandardSet(target.clone())
        {
            return Err(LeanCompileError::unsupported("Matrix/RankMemberSubject"));
        }
        let root = self.compile_object_reference(&fact.element, position)?;
        standard_inclusion_term(
            &StandardSet::N,
            target,
            &root,
            &format!("(Litex.matrixRankInN {root})"),
        )
    }
}
