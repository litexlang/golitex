use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_closed_equality_substitution(
        &self,
        goal: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::ClosedNumericEqualSubstitutionBuiltinRewriteProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.cited_equal_fact_ids.is_empty() {
            return Err(LeanCompileError::new(
                "EqualityRewrite/Citations",
                "The selected substitution must cite a source equality.",
            ));
        }
        let mut equalities = Vec::new();
        for (index, id) in proof.cited_equal_fact_ids.iter().enumerate() {
            if proof.cited_equal_fact_ids[..index].contains(id) {
                return Err(LeanCompileError::new(
                    "EqualityRewrite/Citations",
                    "Substitution citations are unique in source order.",
                ));
            }
            let resolved = self.resolve_fact(*id, position)?;
            let equality = match &resolved {
                Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.fact_id == *id => eq,
                _ => {
                    return Err(LeanCompileError::new(
                        "EqualityRewrite/CitationFamily",
                        "Substitution cites another fact family or identity.",
                    ))
                }
            };
            if *self.cited_fact_reference(*id, position)?.0 != resolved {
                return Err(LeanCompileError::new(
                    "EqualityRewrite/Producer",
                    "The equality citation differs from its compiled producer.",
                ));
            }
            equalities.push((*id, equality.clone()));
        }
        let residual = self.compile_verify(&proof.residual_equal, position)?;
        match &source_subject(&proof.residual_equal)? {
            Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir() == proof.rewritten_left.ir()
                    && eq.right.ir() == proof.rewritten_right.ir() => {}
            _ => {
                return Err(LeanCompileError::new(
                    "EqualityRewrite/Residual",
                    "The actual residual proof has different ordered endpoints.",
                ))
            }
        }
        // The actual residual verification has completed its own constructors.
        // Borrow that source child while comparing the recorded replacement
        // endpoints; it supplies WD only, never a newly stored source fact.
        let after_residual = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Verify(&proof.residual_equal),
            before: usize::MAX,
        };
        let position = &after_residual;
        let mut used = Vec::new();
        let left = self.compile_cited_closed_substitution(
            &goal.left,
            &proof.rewritten_left,
            &equalities,
            &mut used,
            position,
        )?;
        let right = self.compile_cited_closed_substitution(
            &goal.right,
            &proof.rewritten_right,
            &equalities,
            &mut used,
            position,
        )?;
        if used != proof.cited_equal_fact_ids {
            return Err(LeanCompileError::new(
                "EqualityRewrite/CitationOrder",
                "Every source equality must be used in the recorded substitution order.",
            ));
        }
        Ok(format!(
            "(({left}).trans (({}).trans ({right}).symm))",
            residual.1
        ))
    }

    pub(in crate::compile_to_lean) fn compile_cited_closed_substitution(
        &self,
        original: &Obj,
        residual: &Obj,
        equalities: &[(FactId, EqualFact)],
        used: &mut Vec<FactId>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_object_reference(original, position)?;
        self.compile_object_reference(residual, position)?;
        if original.ir() == residual.ir() {
            return Ok(format!(
                "(Litex.sameRefl {})",
                self.compile_object_reference(original, position)?
            ));
        }
        let direct: Vec<_> = equalities
            .iter()
            .filter(|(_, eq)| {
                (eq.left.ir() == original.ir()
                    && eq.right.ir() == residual.ir()
                    && ClosedNumericExpr::try_from_obj(&eq.right).is_some())
                    || (eq.right.ir() == original.ir()
                        && eq.left.ir() == residual.ir()
                        && ClosedNumericExpr::try_from_obj(&eq.left).is_some())
            })
            .collect();
        if direct.len() > 1 {
            return Err(LeanCompileError::new(
                "EqualityRewrite/AmbiguousEndpoint",
                "A changed subtree has multiple recorded source substitutions.",
            ));
        }
        if let Some((id, _)) = direct.first() {
            if !used.contains(id) {
                used.push(*id);
            }
            return self.compile_registered_equality(*id, original, residual, position);
        }
        let (operation, pairs) = arithmetic_constructor_pairs(original, residual).ok_or_else(|| LeanCompileError::new("EqualityRewrite/Subterm", "The changed subtree has no exact recorded closed endpoint or matching owned arithmetic constructor."))?;
        let mut children = Vec::new();
        for (a, b) in pairs {
            children
                .push(self.compile_cited_closed_substitution(a, b, equalities, used, position)?);
        }
        Ok(if children.len() == 1 {
            format!("(congrArg M.{operation} {})", children[0])
        } else {
            format!("(congrArg₂ M.{operation} {} {})", children[0], children[1])
        })
    }
}
