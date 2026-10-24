use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::cart_definition::CartesianDefinitionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::{
    helper::set_builders_alpha_equal, SameFreeParamShapeProof,
};
use crate::prelude::*;

/// Validate the complete recorded definition without allocating source IDs or
/// asking Runtime to regenerate a binder, a requirement, or a proof.
pub(in crate::compile_to_lean) fn validate_cart_definition(
    cart: &Cart,
    definition: &Obj,
) -> Result<(), LeanCompileError> {
    let n = cart.args.len();
    let carrier = if n == 0 {
        definition
    } else {
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = definition else {
            return Err(LeanCompileError::unsupported("CartDefinition/Builder"));
        };
        if builder.facts.len() != n {
            return Err(LeanCompileError::unsupported(
                "CartDefinition/CoordinateCount",
            ));
        }
        let parameter = Obj::Identifier(IdentifierObj::from_bound_name(&builder.param_binding));
        for (index, (condition, factor)) in builder.facts.iter().zip(&cart.args).enumerate() {
            let coordinate = finite_function_coordinate(&parameter, index)
                .map_err(|e| LeanCompileError::new("CartDefinition/Coordinate", &e))?;
            if !matches!(condition, QuantifierFreeFact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == coordinate.ir() && f.set.ir() == factor.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "CartDefinition/CoordinateSubject",
                ));
            }
        }
        &builder.param_set
    };
    let Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) = carrier else {
        return Err(LeanCompileError::unsupported("CartDefinition/ExactDomain"));
    };
    if !matches!(sequence.n.as_ref(), Obj::Literal(Literal::Number(k)) if k.normalized_value == n.to_string())
    {
        return Err(LeanCompileError::unsupported("CartDefinition/Length"));
    }
    // The source producer associates unions to the left, with no extra empty
    // operand. Preserve that exact bound, including the zero/one-factor cases.
    let mut factors = cart.args.iter();
    let mut expected = factors
        .next()
        .map(|x| x.as_ref().clone())
        .unwrap_or_else(|| Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })));
    for factor in factors {
        expected = Obj::SetOperator(SetOperator::Union(Union {
            left: Box::new(expected),
            right: factor.clone(),
        }));
    }
    if sequence.set.ir() != expected.ir() {
        return Err(LeanCompileError::unsupported("CartDefinition/ReturnBound"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_cartesian_definition(
        &self,
        fact: &EqualFact,
        proof: &CartesianDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (cart, cart_obj, definition, reversed) = match (&fact.left, &fact.right) {
            (left @ Obj::ProductShape(ProductShape::Cart(cart)), right) => {
                (cart, left, right, false)
            }
            (left, right @ Obj::ProductShape(ProductShape::Cart(cart))) => {
                (cart, right, left, true)
            }
            _ => return Err(LeanCompileError::unsupported("CartDefinition/Endpoints")),
        };
        validate_cart_definition(cart, &proof.expanded_definition)?;
        validate_cart_definition(cart, definition)?;
        let matched = match &proof.definition_match {
            TheyAreTheSameProof::SameIr(_) => proof.expanded_definition.ir() == definition.ir(),
            TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::SetBuilder(_)) => {
                match (&proof.expanded_definition, definition) {
                    (
                        Obj::SetFormer(SetFormer::SetBuilder(a)),
                        Obj::SetFormer(SetFormer::SetBuilder(b)),
                    ) => set_builders_alpha_equal(a, b),
                    _ => false,
                }
            }
            _ => false,
        };
        if !matched {
            return Err(LeanCompileError::unsupported("CartDefinition/AlphaMatch"));
        }
        let c = self.compile_object_reference(cart_obj, position)?;
        let d = self.compile_object_reference(definition, position)?;
        let n = cart.args.len();
        let numeral =
            format!("(by change M.number ({n} : ℂ) = M.number (({n} : ℕ) : ℂ); norm_num)");
        let body = if n == 0 {
            format!("exact Litex.cartZeroSame _cart _definition (Litex.denoteFiniteSeq _definition 0 {numeral})")
        } else {
            let covers: Vec<_> = (0..n).map(|index| {
                let mut member = "_hx".to_string();
                for branch in 1..n {
                    if index <= branch {
                        let side = if index == branch { "Or.inr" } else { "Or.inl" };
                        member = format!("(Litex.SetSemantics.union_members (M := M) _ _ _).mpr ({side} ({member}))");
                    }
                }
                format!("(show ∀ x, M.mem x (_cart.val.factors ({index} : Fin {n})) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => {member})")
            }).collect();
            let cover = finite_vector_proof(&covers);
            let mut clauses = Vec::new();
            let mut forward = Vec::new();
            let mut backward = Vec::new();
            for index in 0..n {
                let j = index + 1;
                clauses.push(format!("M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number ({j} : ℂ))) (_cart.val.factors ({index} : Fin {n}))"));
                let hindex = format!("have _index : Litex.FiniteFunction.index (M := M) ({index} : Fin {n}) = M.number ({j} : ℂ) := by norm_num [Litex.FiniteFunction.index]");
                forward.push(format!("(show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index ({index} : Fin {n}))) (_cart.val.factors ({index} : Fin {n})) from by\n  {hindex}\n  rw [_index]\n  exact _coord_{index})"));
                backward.push(format!(
                    "(by\n  {hindex}\n  rw [← _index]\n  exact _all ({index} : Fin {n}))"
                ));
            }
            let mut predicate = clauses.pop().unwrap();
            for clause in clauses.into_iter().rev() {
                predicate = format!("∃ _ : ({clause}), {predicate}");
            }
            let names = (0..n).map(|i| format!("_coord_{i}")).collect::<Vec<_>>();
            let unpack = if n == 1 {
                format!("intro {}", names[0])
            } else {
                format!("rintro ⟨{}⟩", names.join(", "))
            };
            let back = if n == 1 {
                backward.remove(0)
            } else {
                format!("⟨{}⟩", backward.join(", "))
            };
            let forward = finite_vector_proof(&forward);
            format!("let _bound := _definition.val.bound\n  apply Litex.cartSameSetBuilder _cart _bound _definition.val.predicate (Litex.denote _bound.val.carrier)\n  · exact Litex.denoteFiniteSeq _bound {n} {numeral}\n  · exact {cover}\n  · intro _point _hin\n    change ({predicate}) ↔ _\n    constructor\n    · {unpack}\n      exact {forward}\n    · intro _all\n      exact {back}")
        };
        let proof = format!("(show Litex.Same {c} {d} from by\n  let _cart := {c}\n  let _definition := {d}\n  {body})");
        Ok(if reversed {
            format!("({proof}).symm")
        } else {
            proof
        })
    }
}
