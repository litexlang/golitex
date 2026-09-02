//! Standard-set nonemptiness proof compilation.

use super::super::*;

pub(in super::super) fn compile_standard_set_nonempty_fact_proof_from_result(
    result: &VerifyFactResult,
    expected_carrier: &Obj,
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let success = result
        .verified()
        .ok_or_else(|| "object choice nonemptiness child is not a successful fact".to_string())?;
    let target = success.fact();
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = &target else {
        return Err("object choice nonemptiness child changed fact family".into());
    };
    if obj_equality_key(&nonempty.set) != obj_equality_key(expected_carrier) {
        return Err(
            "object choice nonemptiness child changed its target".into(),
        );
    }
    let SuccessFactProofResult::BuiltinRule(builtin) = success.proof() else {
        return Err("object choice nonemptiness child is not a builtin leaf".into());
    };
    let Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) = builtin.evidence.typed() else {
        return Err("object choice nonemptiness child has no typed standard-set evidence".into());
    };
    let Obj::StandardSet(target_set) = expected_carrier else {
        return Err("object choice direct compiler currently requires a standard carrier".into());
    };
    if !builtin.subgoals.is_empty()
        || evidence.expected_target.to_string() != target.to_string()
        || evidence.target_set != *target_set
    {
        return Err("standard-set nonempty evidence changed its target or children".into());
    }
    let theorem = match target_set {
        StandardSet::N => "Litex.Rules.naturalNonempty",
        StandardSet::Z => "Litex.Rules.integerNonempty",
        StandardSet::Q => "Litex.Rules.rationalNonempty",
        StandardSet::R => "Litex.Rules.realNonempty",
        StandardSet::C => "Litex.Rules.complexNonempty",
        unsupported => {
            return Err(format!(
                "unsupported direct standard-set nonempty carrier `{unsupported}`"
            ));
        }
    };
    let rendered_target = render_fact(&target, environment_stack)?;
    let rendered_carrier = render_obj(expected_carrier, environment_stack)?;
    if rendered_target != format!("Litex.Set.Nonempty {rendered_carrier}") {
        return Err("standard-set nonempty evidence changed its rendered target".into());
    }
    Ok(theorem.into())
}
