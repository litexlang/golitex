use super::compile_real_set_bounds::contains_parameter;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

pub(super) fn validate_unary_sequence_limit(
    id: BuiltinTheoremId,
    args: &[Obj],
    requirements: &[Fact],
    goal: &Fact,
) -> Result<(), LeanCompileError> {
    use BuiltinTheoremId::*;
    let extra = matches!(id, SequenceLimitScale | SequenceLimitPower);
    if args.len() != 2 + usize::from(extra) || requirements.len() != 2 + usize::from(extra) {
        return Err(invalid("Stages"));
    }
    let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(goal)) = goal else {
        return Err(invalid("Conclusion"));
    };
    if extra {
        let carrier = if id == SequenceLimitPower {
            StandardSet::N
        } else {
            StandardSet::R
        };
        if !matches!(&requirements[2],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir() && f.set==Obj::StandardSet(carrier))
        {
            return Err(invalid("ScalarDomain"));
        }
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(g)) = &goal.sequence else {
        return Err(invalid("Function"));
    };
    let [group] = g.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("Binder"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("Binder"));
    };
    if group.param_type.as_ref() != &Obj::StandardSet(StandardSet::NPos)
        || g.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
        || !g.body.dom_facts.is_empty()
        || args.iter().any(|a| contains_parameter(a, binder.id))
    {
        return Err(invalid("FunctionDomain"));
    }
    let input = Obj::Identifier(IdentifierObj::from_bound_name(binder));
    let body = unary_operand(id, &g.equal_to, args).ok_or_else(|| invalid("BodyOperation"))?;
    let limit = unary_operand(id, &goal.value, args).ok_or_else(|| invalid("LimitOperation"))?;
    if !super::compile_sequence_analysis::call_matches(body, &args[0], &input)
        || limit.ir() != args[1].ir()
    {
        return Err(invalid("OriginalOperands"));
    }
    Ok(())
}
fn unary_operand<'a>(id: BuiltinTheoremId, object: &'a Obj, args: &[Obj]) -> Option<&'a Obj> {
    use BuiltinTheoremId::*;
    match (id, object) {
        (SequenceLimitNeg, Obj::ArithmeticOperator(ArithmeticOperator::Neg(p))) => Some(&p.arg),
        (SequenceLimitAbs, Obj::ArithmeticOperator(ArithmeticOperator::Abs(p))) => Some(&p.arg),
        (SequenceLimitScale, Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)))
            if p.left.ir() == args.get(2)?.ir() =>
        {
            Some(&p.right)
        }
        (SequenceLimitPower, Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)))
            if p.exponent.ir() == args.get(2)?.ir() =>
        {
            Some(&p.base)
        }
        _ => None,
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_unary_sequence_limit_law(
        &self,
        id: BuiltinTheoremId,
        args: &[Obj],
        goal: &Fact,
        objects: &[String],
        references: &[String],
        domain: &str,
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use BuiltinTheoremId::*;
        let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(goal)) = goal else {
            return Err(invalid("Conclusion"));
        };
        let g = self
            .compile_object_reference(&goal.sequence, scope)?
            .replace('\n', "\n  ");
        let real = self.compile_real_membership_certificate(&args[1], scope)?;
        let (operation, native, continuous, certificate) = match id {
            SequenceLimitNeg => (
                "M.negValue".to_owned(),
                "(fun _r : ℝ => -_r)".to_owned(),
                "continuous_neg".to_owned(),
                "(by intro _r; rw [M.neg_numbers, Complex.ofReal_neg])".to_owned(),
            ),
            SequenceLimitAbs => (
                "Litex.absValue".to_owned(),
                "(fun _r : ℝ => |_r|)".to_owned(),
                "continuous_abs".to_owned(),
                "(by intro _r; exact Litex.absValue_number _r)".to_owned(),
            ),
            SequenceLimitScale => {
                let c = &objects[2];
                let h = &references[2];
                let value = format!("Litex.NativeBridge.asReal {c} {h}");
                (format!("(fun _x => M.mulValue (Litex.denote {c}) _x)"),format!("(fun _r : ℝ => ({value}) * _r)"),"(continuous_const.mul continuous_id)".to_owned(),format!("(by\n    intro _r\n    have _scalar : Litex.denote {c} = M.number (({value} : ℝ) : ℂ) := Litex.NativeBridge.asReal_spec {c} {h}\n    rw [_scalar, M.mul_numbers, Complex.ofReal_mul]\n  )"))
            }
            SequenceLimitPower => {
                let c = &objects[2];
                let h = &references[2];
                let value = format!("Litex.NativeBridge.asNat {c} {h}");
                (format!("(fun _x => M.powValue _x (Litex.denote {c}))"),format!("(fun _r : ℝ => _r ^ ({value}))"),format!("(continuous_id.pow ({value}))"),format!("(by\n    intro _r\n    have _power : Litex.denote {c} = M.number ({value} : ℂ) := Litex.NativeBridge.asNat_spec {c} {h}\n    rw [_power, M.pow_numbers_nat, Complex.ofReal_pow]\n  )"))
            }
            _ => return Err(invalid("Id")),
        };
        let domain_equal = "(Litex.FunctionSignature.withGuard_true_domain (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))))";
        Ok(format!("(by\n  let _sequence_map := {g}\n  exact Litex.sequenceLimitMap {} {} _sequence_map {domain} {real} {} {operation} {native} {continuous} {certificate} {domain_equal} (by rfl) (by rfl)\n)",objects[0],objects[1],references[1]))
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("SequenceMap/{stage}"),"A unary sequence-limit law must retain its original operation, sequence/value, positive-index binder, real output, scalar domain and checked stages.")
}
