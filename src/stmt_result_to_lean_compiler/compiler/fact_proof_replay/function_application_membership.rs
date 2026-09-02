//! Function-application return membership.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: validate the verifier-selected head-membership child and use
    /// the exact WD application layer to construct membership in the
    /// instantiated declared return carrier. No function search or return-set
    /// inference is repeated here.
    pub(in super::super) fn construct_lean_function_application_return_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &FunctionApplicationReturnMembershipBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("function-application return evidence changed its target".into());
        }
        let [head_membership_result] = subgoals else {
            return Err(
                "function-application return evidence requires one head-membership child".into(),
            );
        };
        let head_membership_result = head_membership_result
            .verified()
            .ok_or_else(|| "function head-membership child is not factual".to_string())?;
        if head_membership_result.fact().to_string()
            != evidence.expected_head_membership.to_string()
        {
            return Err(
                "function head-membership child changed its proposition"
                    .into(),
            );
        }
        let Some(_head_membership_proof) =
            self.construct_lean_proof_from_direct_fact_result(head_membership_result)?
        else {
            return Ok(None);
        };

        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = target else {
            return Err("function-application return evidence targets a non-membership".into());
        };
        let Obj::FnObj(application) = &target_membership.element else {
            return Err("function-application return evidence targets a non-application".into());
        };
        let Fact::AtomicFact(AtomicFact::InFact(head_membership)) =
            &evidence.expected_head_membership
        else {
            return Err("function head contract is not a membership fact".into());
        };
        if !matches!(&head_membership.set, Obj::FnSet(_)) {
            return Err("function head contract retained a non-function carrier".into());
        }
        let application_head: Obj = application.head.as_ref().clone().into();
        if !objs_equal_with_nested_binder_alpha_equivalence(
            &head_membership.element,
            &application_head,
        ) || !objs_equal_with_nested_binder_alpha_equivalence(
            &target_membership.set,
            &evidence.typed_return_set,
        ) {
            return Err("function-application return evidence changed its head or carrier".into());
        }

        let rendered_application = render_obj(&target_membership.element, &self.environment_stack)?;
        let rendered_return_set = render_obj(&target_membership.set, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_target = format!("Litex.In {rendered_application} {rendered_return_set}");
        if rendered_target != expected_target {
            return Err("function-application return evidence changed its rendered target".into());
        }
        Ok(Some(format!(
            "Litex.In.own {rendered_return_set} {rendered_application}"
        )))
    }
}
