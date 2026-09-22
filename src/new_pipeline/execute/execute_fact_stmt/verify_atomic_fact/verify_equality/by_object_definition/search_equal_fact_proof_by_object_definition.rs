//! Equality by object definition: first match the def-side object shape, then
//! only consult definitions that belong to that shape.
//!
//! - `Identifier` → have/let object definitions for that name
//! - `FnObj` with identifier head → have-fn definitions (`=`, `by cases`, `by induc`)
//! - Instantiated template (obj or fn head) → template body unfolds

use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{FnObjHead, Obj, Structish};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition;
use super::by_identifier::EqualitySearchProofByIdentifierObjectDefinition;
use super::by_template::EqualitySearchProofByTemplateObjectDefinition;
use super::EqualitySearchProofByObjectDefinition;

impl Runtime {
    // When: goal is `L = R`, and at least one side is an identifier / named fn
    // application / instantiated template whose definition is stored.
    // After: prove by unfolding that definition into a residual equality
    // (rewrite off on the residual). Tries left-as-def-side, then right.
    // Example: `have a R = 1 + 1` then goal `a = 2` → residual `1 + 1 = 2`.
    pub fn search_equal_fact_proof_by_object_definition(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByObjectDefinition>> {
        if let Some(proof) = self.search_object_definition_on_def_side(
            &fact.left,
            &fact.right,
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.search_object_definition_on_def_side(
            &fact.right,
            &fact.left,
            fact,
            verify_state,
        )? {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    // When: `def_side` is the candidate unfold side of `def_side = other_side`.
    // Dispatch by shape only (no unrelated definition kinds):
    //   Identifier → have/let obj
    //   FnObj (identifier / anonymous head) → have-fn (= / by cases / by induc)
    //   InstantiatedTemplateObj / template-headed FnObj → template unfolds
    // After: first matching unfold proof, or None if shape has no applicable def.
    // Example: def_side `f(2)`, other_side `3`, with `have fn f(x N) = x + 1`
    // → residual `(2 + 1) = 3`.
    fn search_object_definition_on_def_side(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByObjectDefinition>> {
        match def_side {
            Obj::Identifier(_) => self.search_object_definition_for_identifier(
                def_side,
                other_side,
                parent_fact,
                verify_state,
            ),
            Obj::FnObj(fn_obj) => match fn_obj.head.as_ref() {
                FnObjHead::Identifier(_) | FnObjHead::AnonymousFnLiteral(_) => self
                    .search_object_definition_for_fn_application(
                        def_side,
                        other_side,
                        parent_fact,
                        verify_state,
                    ),
                FnObjHead::InstantiatedTemplateObj(_) => self
                    .search_object_definition_for_template_fn_application(
                        def_side,
                        other_side,
                        parent_fact,
                        verify_state,
                    ),
                _ => Ok(None),
            },
            Obj::Structish(Structish::InstantiatedTemplateObj(_)) => self.search_object_definition_for_template_obj(
                def_side,
                other_side,
                parent_fact,
                verify_state,
            ),
            _ => Ok(None),
        }
    }

    fn search_object_definition_for_identifier(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByObjectDefinition>> {
        if let Some(proof) = self.try_have_obj_equal_object_definition(
            def_side,
            other_side,
            parent_fact,
            verify_state.clone(),
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByIdentifier(
                EqualitySearchProofByIdentifierObjectDefinition::HaveObjEqual(proof),
            )));
        }
        if let Some(proof) = self.try_let_obj_object_definition(
            def_side,
            other_side,
            parent_fact,
            verify_state,
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByIdentifier(
                EqualitySearchProofByIdentifierObjectDefinition::LetObj(proof),
            )));
        }
        Ok(None)
    }

    fn search_object_definition_for_fn_application(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByObjectDefinition>> {
        if let Some(proof) = self.try_unfold_named_have_fn_equal_application(
            def_side,
            other_side,
            parent_fact,
            verify_state.clone(),
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof),
            )));
        }
        if let Some(proof) = self.try_unfold_have_fn_equal_case_by_case_application(
            def_side,
            other_side,
            parent_fact,
            verify_state.clone(),
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqualCaseByCase(proof),
            )));
        }
        if let Some(proof) = self.try_unfold_have_fn_by_induc_application(
            def_side,
            other_side,
            parent_fact,
            verify_state,
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::HaveFnByInduc(proof),
            )));
        }
        Ok(None)
    }

    fn search_object_definition_for_template_obj(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByObjectDefinition>> {
        if let Some(proof) = self.try_unfold_instantiated_template_have_obj_equal(
            def_side,
            other_side,
            parent_fact,
            verify_state,
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveObjEqual(proof),
            )));
        }
        Ok(None)
    }

    fn search_object_definition_for_template_fn_application(
        &mut self,
        def_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByObjectDefinition>> {
        // Match on template body kind (not a flat try-chain across unrelated shapes).
        if let Some(proof) = self.try_unfold_instantiated_template_have_fn_equal_application(
            def_side,
            other_side,
            parent_fact,
            verify_state.clone(),
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualApplication(proof),
            )));
        }
        if let Some(proof) = self
            .try_unfold_instantiated_template_have_fn_equal_case_by_case_application(
                def_side,
                other_side,
                parent_fact,
                verify_state.clone(),
            )?
        {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualCaseByCaseApplication(
                    proof,
                ),
            )));
        }
        if let Some(proof) = self.try_unfold_instantiated_template_have_fn_by_induc_application(
            def_side,
            other_side,
            parent_fact,
            verify_state,
        )? {
            return Ok(Some(EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(proof),
            )));
        }
        Ok(None)
    }
}
