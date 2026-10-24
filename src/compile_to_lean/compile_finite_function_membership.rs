use crate::compile_to_lean::compile_fact_stmt_result::validate_finite_signature;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof;
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_function_membership(
        &self,
        member: &InFact,
        domain: &FunctionDomainMatchProof,
        finite: &FiniteFunctionSignatureProof,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_finite_signature(finite)?;
        if finite.signature != domain.source.signature || requirements.len() != references.len() {
            return Err(LeanCompileError::unsupported(
                "FiniteMembership/SourceSignature",
            ));
        }
        let n = finite.source.dimension();
        let (cart, cart_member) =
            self.compile_cart_shape_member(&member.element, &finite.source, position)?;
        let returns = if let KnownTupleShapeProof::TupleEquality(source) = &finite.source {
            if requirements.len() != n {
                return Err(LeanCompileError::unsupported(
                    "FiniteMembership/ReturnCount",
                ));
            }
            for (fact, value) in requirements.iter().zip(&source.value.args) {
                if !matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == value.ir() && f.set.ir() == domain.target.ret_set.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FiniteMembership/ReturnSubject",
                    ));
                }
            }
            let tuple_obj = Obj::ProductShape(ProductShape::Tuple(source.value.clone()));
            let tuple = self.compile_object_reference(&tuple_obj, position)?;
            let same = self.compile_equality_path(
                &member.element,
                &tuple_obj,
                &source.tuple_equal,
                position,
            )?;
            let values = finite_vector_proof(references);
            format!("let _tuple := {tuple}\n  have _same : Litex.Same _membership_function _tuple := {same}\n  have _values : ∀ i : Fin {n}, M.mem (_tuple.val.values i) _membership_target.val.output := {values}\n  intro _input _hin\n  rw [_domain] at _hin\n  obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := {n}) _input).mp _hin\n  have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)\n  change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output\n  rw [_coordinate]\n  exact _values _index")
        } else {
            self.compile_function_return_forall(
                &member.element,
                &domain.target,
                requirements,
                references,
                position,
            )?
            .replace('\n', "\n  ")
        };
        Ok(format!("(by\n  let _source_cart := {cart}\n  have _source_member : Litex.In _membership_function _source_cart := {cart_member}\n  have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) {n} := by\n    change Litex.finiteSeqDomain (Litex.number (M := M) ({n} : ℂ)) = _\n    exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) ({n} : ℂ)) {n} (by change M.number ({n} : ℂ) = M.number (({n} : ℕ) : ℂ); norm_num)\n  apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain\n  {returns})"))
    }
}
