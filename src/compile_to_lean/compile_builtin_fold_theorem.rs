use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_fold_theorem(
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
        if builtin.theorem != BuiltinTheoremId::FiniteSetReduceSingleton
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported("FoldSingleton/Contract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("FoldSingleton/Arguments"));
        };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != 2
            || builtin.requirements.len() != 1
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
            || dom_proofs.len() != 1
            || dom_stores.len() != 1
        {
            return Err(LeanCompileError::unsupported("FoldSingleton/Stages"));
        }
        let Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(fold)) = &arguments[0] else {
            return Err(LeanCompileError::unsupported("FoldSingleton/Subject"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(set_equal)) = &builtin.requirements[0] else {
            return Err(LeanCompileError::unsupported("FoldSingleton/SetEquality"));
        };
        if set_equal.left.ir() != fold.set.ir()
            || !matches!(&set_equal.right, Obj::SetFormer(SetFormer::ListSet(s)) if s.list.len() == 1 && s.list[0].ir() == arguments[1].ir())
            || source_subject(&dom_proofs[0])? != builtin.requirements[0]
        {
            return Err(LeanCompileError::unsupported("FoldSingleton/SetEquality"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(conclusion)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported("FoldSingleton/Conclusion"));
        };
        let application = fold_application(&fold.func, &[arguments[1].clone()])?;
        let expected = fold_application(&fold.op, &[fold.seed.as_ref().clone(), application])?;
        if conclusion.left.ir() != arguments[0].ir() || conclusion.right.ir() != expected.ir() {
            return Err(LeanCompileError::unsupported("FoldSingleton/Conclusion"));
        }
        let prior = SourcePosition {
            before: 0,
            ..*position
        };
        let compiled = self.compile_verify(&dom_proofs[0], &prior)?;
        self.validate_store(&dom_stores[0].store, &builtin.requirements[0])?;
        let mut definitions =
            vec![self.emit_internal_fact(&builtin.requirements[0], &compiled, &prior)?];
        let reference = format!("h_{}", set_equal.fact_id.value());
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        definitions.extend(self.compile_stored_inferences(
            &dom_stores[0],
            &builtin.requirements[0],
            &(compiled.0, reference.clone()),
            &formed,
        )?);
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let formation = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let fold = self.compile_object_reference(&arguments[0], &formation)?;
        let element = self.compile_object_reference(&arguments[1], &formation)?;
        let singleton = self.compile_object_reference(&set_equal.right, &formed)?;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let application = format!("(show {statement} from by\n  let _fold := {fold}\n  let _element := {element}\n  let _singleton := {singleton}\n  have _set_same : Litex.denote _fold.val.set = Litex.denote _singleton := {reference}\n  apply Litex.finiteFoldSingleton _fold (Litex.denote _element)\n  intro y\n  rw [_set_same]\n  exact (Litex.finiteMembersInsert _singleton (Litex.denote _element) [] rfl Litex.finiteMembersEmpty y).trans (by simp only [List.mem_singleton]))");
        Ok((definitions, application, builtin.conclusions.clone()))
    }
}
