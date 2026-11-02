//! Replay the original singleton-space certificate without inventing a member.
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_empty_function_graph::EmptyDomainFunctionSpaceSingletonBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_space_singleton(
        &self,
        goal: &EqualFact,
        proof: &EmptyDomainFunctionSpaceSingletonBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (singleton, reverse) = if goal.left == proof.source_space {
            (&goal.right, false)
        } else if goal.right == proof.source_space {
            (&goal.left, true)
        } else {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceSingleton/SourceSubject",
            ));
        };
        let Obj::SetFormer(SetFormer::ListSet(list)) = singleton else {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceSingleton/Singleton",
            ));
        };
        let [element] = list.list.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceSingleton/SingletonArity",
            ));
        };
        let tuple = match element.as_ref() {
            Obj::SetFormer(SetFormer::ListSet(empty)) if empty.list.is_empty() => false,
            Obj::ProductShape(ProductShape::Tuple(empty)) if empty.args.is_empty() => true,
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FunctionSpaceSingleton/EmptyGraphLiteral",
                ))
            }
        };
        let signature = match &proof.domain_empty {
            FunctionDomainEmptyProof::ParameterCarrier(p) => &p.signature,
            FunctionDomainEmptyProof::GuardExclusion(p) => &p.signature,
        };
        if signature != &proof.signature {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceSingleton/OriginalSignature",
            ));
        }
        let source = &proof.source_space;
        let cart_zero = matches!(source, Obj::ProductShape(ProductShape::Cart(_)));
        let (object, compiled, same, base, guard) = if cart_zero {
            validate_empty_cart_signature(source, signature)?;
            let object = self.compile_object_reference(source, position)?;
            let compiled = format!("(Litex.cartCompleteSignature {object})");
            let same = format!("(Litex.cartZeroEqFnSet {object})");
            let base = "(Litex.SetSemantics.sepValue (M.standard .integer) (Litex.ClosedRangeObj.condition ⟨Litex.number 1, Litex.number 0⟩))".into();
            (object, compiled, same, base, "(fun _ => True)".into())
        } else {
            let (object, compiled, equality) =
                self.checked_space_signature(source, signature, position)?;
            let same = equality
                .map(|law| format!("(Litex.{law} {object})"))
                .unwrap_or_else(|| "rfl".into());
            let (base, _, guard) = self.space_domain_components(source, signature, position)?;
            (object, compiled, same, base, guard)
        };
        // The cart0 source owns a Nat-cast arity in its canonical signature.
        // Its source absence still refers to the exact integer interval 1..0.
        let input = if cart_zero {
            "(by simpa only [Litex.cartCompleteSignature, Litex.FunctionSignature.ofDomain, Litex.finiteSeqDomain, Nat.cast_zero] using _space_domain)"
        } else {
            "_space_domain"
        };
        let empty = self.compile_empty_signature_domain(
            &proof.domain_empty,
            &compiled,
            &base,
            &guard,
            input,
            position,
        )?;
        let element = self.compile_object_reference(element, position)?;
        let singleton = self.compile_object_reference(singleton, position)?;
        let element_same = if tuple {
            format!("(Litex.emptyTupleDenote {element})")
        } else {
            "rfl".into()
        };
        let value = "(Litex.SetSemantics.emptyValue (M := M))";
        let term = format!("(show Litex.Same {object} {singleton} from by\n  have _space_same : Litex.denote {object} = Litex.denote (Litex.fnSet {compiled}) := {same}\n  have _space_empty : ∀ a, ¬ M.mem a ({compiled}).domain := {empty}\n  have _space_element : Litex.denote {element} = {value} := {element_same}\n  change Litex.denote {object} = Litex.SetSemantics.insertValue (Litex.denote {element}) {value}\n  exact _space_same.trans ((Litex.functionSpaceSingletonOfEmptyDomain {compiled} _space_empty).trans (congrArg (fun e => Litex.SetSemantics.insertValue e {value}) _space_element.symm))\n)");
        Ok(if reverse {
            format!("({term}).symm")
        } else {
            term
        })
    }
}

/// The original cart0 producer has a canonical one-based finite signature.
/// It retains no function membership, so validate that shape directly.
fn validate_empty_cart_signature(source: &Obj, signature: &FnSet) -> Result<(), LeanCompileError> {
    let Obj::ProductShape(ProductShape::Cart(cart)) = source else {
        unreachable!()
    };
    let groups = &signature.set_bound_parameters.groups;
    let valid = cart.args.is_empty()
        && groups.len() == 1
        && groups[0].params.len() == 1
        && signature.dom_facts.is_empty()
        && matches!(groups[0].param_type.as_ref(), Obj::SetFormer(SetFormer::ClosedRange(r))
            if matches!(r.start.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
            && matches!(r.end.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "0"))
        && matches!(signature.ret_set.as_ref(), Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty());
    if valid {
        Ok(())
    } else {
        Err(LeanCompileError::unsupported(
            "FunctionSpaceSingleton/CartesianSignature",
        ))
    }
}
