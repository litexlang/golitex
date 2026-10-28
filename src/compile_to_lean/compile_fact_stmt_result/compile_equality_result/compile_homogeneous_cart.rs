use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_homogeneous_cart::HomogeneousCartesianEqualsFiniteSequenceBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_homogeneous_cart(
        &self,
        fact: &EqualFact,
        proof: &HomogeneousCartesianEqualsFiniteSequenceBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::ProductShape(ProductShape::Cart(cart)),
                Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)),
            ) = (left, right)
            else {
                continue;
            };
            let n = cart.args.len();
            if n != proof.dimension || n != proof.factor_equalities.len() {
                return Err(LeanCompileError::new(
                    "HomogeneousCart/Dimension",
                    "The recorded dimension and factor evidence must match the flat product.",
                ));
            }
            let length = Obj::Literal(Literal::Number(Number {
                normalized_value: n.to_string(),
            }));
            let length_fact = EqualFact {
                fact_id: FactId::new(0),
                left: *sequence.n.clone(),
                right: length,
                line_file: None,
            };
            let length_equal =
                self.compile_equality_search(&length_fact, &proof.length_equal, position)?;
            let cart_term = self.compile_object_reference(left, position)?;
            let seq_term = self.compile_object_reference(right, position)?;
            let mut lines = vec![format!("let _cart := {cart_term}"), format!("let _seq := {seq_term}"),
                format!("have _source_length : Litex.Same _seq.val.length (Litex.number ({n} : ℂ)) := {length_equal}"),
                format!("have _length : Litex.Same _seq.val.length (Litex.number (({n} : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))"),
                "have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by".into(),
                "  intro i".into(), "  fin_cases i".into()];
            for (factor, child) in cart.args.iter().zip(&proof.factor_equalities) {
                let equal = EqualFact {
                    fact_id: FactId::new(0),
                    left: *factor.clone(),
                    right: *sequence.set.clone(),
                    line_file: None,
                };
                let term = self.compile_equality_search(&equal, child, position)?;
                lines.push(format!("  · exact {term}"));
            }
            lines.extend([
                "change Litex.denote _cart = Litex.denote _seq".into(),
                format!("rw [Litex.denoteFiniteSeq _seq {n} _length]"),
                "apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))".into(),
                "intro p".into(),
                "change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _".into(),
                "rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]".into(),
                "constructor".into(), "· exact And.left".into(),
                "· intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)".into(),
            ]);
            let term = format!(
                "((by\n  {}\n) : Litex.Same {cart_term} {seq_term})",
                lines.join("\n").replace('\n', "\n  ")
            );
            return Ok(if reversed {
                format!("({term}).symm")
            } else {
                term
            });
        }
        Err(LeanCompileError::new(
            "HomogeneousCart/Constructors",
            "Expected a flat Cartesian product and a finite sequence carrier.",
        ))
    }
}
