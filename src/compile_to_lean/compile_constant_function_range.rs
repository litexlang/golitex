//! Replay the selected complete source and inhabited domain of a constant range.
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave13::FnRangeOfConstantAnonymousFnBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_constant_function_range(
        &self,
        goal: &EqualFact,
        proof: &FnRangeOfConstantAnonymousFnBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (range_object, range, singleton, reverse) = match (&goal.left, &goal.right) {
            (left @ Obj::FunctionSpace(FunctionSpace::FnRange(range)), right) => {
                (left, range, right, false)
            }
            (left, right @ Obj::FunctionSpace(FunctionSpace::FnRange(range))) => {
                (right, range, left, true)
            }
            _ => return Err(invalid("RangeEndpoints")),
        };
        let Obj::SetFormer(SetFormer::ListSet(list)) = singleton else {
            return Err(invalid("Singleton"));
        };
        let [element] = list.list.as_slice() else {
            return Err(invalid("SingletonArity"));
        };
        let CompleteFunctionDomainSourceProof::AnonymousFunction {
            function,
            subject_equal,
        } = &proof.source.source
        else {
            return Err(invalid("OriginalAnonymousSource"));
        };
        if !matches!(
            function.equal_to.as_ref(),
            Obj::Literal(_) | Obj::StandardSet(_)
        ) {
            return Err(invalid("ClosedLiteralBody"));
        }
        if function.equal_to.as_ref() != element.as_ref() {
            return Err(invalid("OriginalBodyEncoding"));
        }
        if proof.source.signature != proof.domain_nonempty.signature
            || proof.source.signature != function.body
        {
            return Err(invalid("OriginalSignature"));
        }
        let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
        if subject_equal.path.is_empty() {
            if range.function.as_ref() != &literal {
                return Err(invalid("OriginalLiteralSubject"));
            }
        } else if subject_equal.path.first().map(|p| &p.0) != Some(range.function.as_ref())
            || subject_equal.path.last().map(|p| &p.1) != Some(&literal)
        {
            return Err(invalid("OriginalSubjectPath"));
        }
        let member =
            self.compile_complete_domain_member(&range.function, &proof.source, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::CompleteDomainSource(&proof.source),
            usize::MAX,
        );
        let signature = self.compile_complete_domain_signature(&proof.source, &formed)?;
        let literal_term = self.compile_object_reference(&literal, &formed)?;
        let target = self.compile_object_reference(&range.function, &formed)?;
        let same = self.compile_equality_path(&range.function, &literal, subject_equal, &formed)?;
        let inhabited =
            self.compile_function_domain_nonempty(&proof.domain_nonempty, position, &formed)?;
        let element = self.compile_object_reference(element, position)?;
        let range = self.compile_object_reference(range_object, position)?;
        let singleton = self.compile_object_reference(singleton, position)?;
        let value = "(Litex.SetSemantics.emptyValue (M := M))";
        let term = format!("(show Litex.Same {range} {singleton} from by\n  let _constant_target := {target}\n  let _constant_function := {literal_term}\n  let _constant_signature := {signature}\n  let _constant_value := {element}\n  have _constant_member : Litex.In _constant_target (Litex.fnSet _constant_signature) := {member}\n  have _constant_source : Litex.Same _constant_target _constant_function := {same}\n  have _constant_inhabited : ∃ a, M.mem a _constant_signature.domain := {inhabited}\n  have _constant_calls : ∀ a, M.mem a _constant_signature.domain → Litex.FunctionSemantics.callValue (Litex.denote _constant_target) a = Litex.denote _constant_value := by\n    intro a ha\n    have _literal_call : Litex.FunctionSemantics.callValue (Litex.denote _constant_function) a = Litex.denote _constant_value := (Litex.FunctionSemantics.call_graphValue _constant_function.val.signature.domain _constant_function.val.signature.target _constant_function.val.bodyValue _constant_function.wd a ha).trans (by rfl)\n    exact (congrArg (fun v => Litex.FunctionSemantics.callValue v a) _constant_source).trans _literal_call\n  change Litex.FunctionSemantics.rangeValue (Litex.denote _constant_target) = Litex.SetSemantics.insertValue (Litex.denote _constant_value) {value}\n  exact Litex.fnRangeSingletonOfConstantCalls _constant_target _constant_value _constant_signature _constant_member _constant_inhabited _constant_calls\n)");
        Ok(if reverse {
            format!("({term}).symm")
        } else {
            term
        })
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ConstantFnRange/{part}"))
}
