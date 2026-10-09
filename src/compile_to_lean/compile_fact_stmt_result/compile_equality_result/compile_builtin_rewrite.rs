use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_equality_builtin_rewrite(
        &self,
        goal: &EqualFact,
        proof: &EqualitySearchProofByBuiltinRewrite,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (rewritten_left, rewritten_right, cited_equal_fact_ids, residual_equal) = match proof {
            EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(p) => (
                &p.rewritten_left,
                &p.rewritten_right,
                &p.cited_equal_fact_ids,
                &p.residual_equal,
            ),
            EqualitySearchProofByBuiltinRewrite::KnownFnValueSubstitution(p) => (
                &p.rewritten_left,
                &p.rewritten_right,
                &p.cited_equal_fact_ids,
                &p.residual_equal,
            ),
        };
        if cited_equal_fact_ids.is_empty() {
            return Err(LeanCompileError::new(
                "EqualityRewrite/Citations",
                "The selected substitution must cite a source equality.",
            ));
        }
        let mut equalities = Vec::new();
        for (index, id) in cited_equal_fact_ids.iter().enumerate() {
            if cited_equal_fact_ids[..index].contains(id) {
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
        let residual = self.compile_verify(residual_equal, position)?;
        match &source_subject(residual_equal)? {
            Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir() == rewritten_left.ir() && eq.right.ir() == rewritten_right.ir() => {
            }
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
            owner: SourceOwner::Verify(residual_equal),
            before: usize::MAX,
        };
        let position = &after_residual;
        let mut used = Vec::new();
        let left = self.compile_cited_equality_substitution(
            &goal.left,
            rewritten_left,
            &equalities,
            &mut used,
            proof,
            position,
        )?;
        let right = self.compile_cited_equality_substitution(
            &goal.right,
            rewritten_right,
            &equalities,
            &mut used,
            proof,
            position,
        )?;
        if &used != cited_equal_fact_ids {
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

    pub(in crate::compile_to_lean) fn compile_cited_equality_substitution(
        &self,
        original: &Obj,
        residual: &Obj,
        equalities: &[(FactId, EqualFact)],
        used: &mut Vec<FactId>,
        proof: &EqualitySearchProofByBuiltinRewrite,
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
                let exact = (eq.left.ir() == original.ir() && eq.right.ir() == residual.ir())
                    || (eq.right.ir() == original.ir() && eq.left.ir() == residual.ir());
                let eligible = match proof {
                    EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(_) => {
                        ClosedNumericExpr::try_from_obj(residual).is_some()
                    }
                    EqualitySearchProofByBuiltinRewrite::KnownFnValueSubstitution(_) => {
                        matches!(original, Obj::FnObj(_))
                    }
                };
                exact && eligible
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
        let (operation, pairs) = arithmetic_constructor_pairs(original, residual).ok_or_else(|| LeanCompileError::new("EqualityRewrite/Subterm", "The changed subtree has no eligible exact recorded endpoint or matching owned arithmetic constructor."))?;
        let mut children = Vec::new();
        for (a, b) in pairs {
            children.push(
                self.compile_cited_equality_substitution(a, b, equalities, used, proof, position)?,
            );
        }
        Ok(if children.len() == 1 {
            format!("(congrArg M.{operation} {})", children[0])
        } else {
            format!("(congrArg₂ M.{operation} {} {})", children[0], children[1])
        })
    }
}
