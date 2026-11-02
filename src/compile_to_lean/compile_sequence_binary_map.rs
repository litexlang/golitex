use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

pub(super) fn validate_binary_sequence_limit(
    id: BuiltinTheoremId,
    args: &[Obj],
    requirements: &[Fact],
    goal: &Fact,
) -> Result<(), LeanCompileError> {
    use BuiltinTheoremId::*;
    let division = id == SequenceLimitDivide;
    if args.len() != 4 || requirements.len() != if division { 6 } else { 4 } {
        return Err(invalid("Stages"));
    }
    if !matches!(&requirements[1],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir()
        && matches!(&f.set,Obj::FunctionSpace(FunctionSpace::FnSet(s)) if s.dom_facts.is_empty()
            && s.ret_set.as_ref()==&Obj::StandardSet(StandardSet::R)
            && matches!(s.set_bound_parameters.groups.as_slice(),[g] if g.params.len()==1 && g.param_type.as_ref()==&Obj::StandardSet(StandardSet::NPos))))
    {
        return Err(invalid("SecondSequence"));
    }
    for (index, (sequence, value)) in [(&args[0], &args[2]), (&args[1], &args[3])]
        .into_iter()
        .enumerate()
    {
        if !matches!(&requirements[index+2],Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) if f.sequence.ir()==sequence.ir() && f.value.ir()==value.ir())
        {
            return Err(invalid("OriginalCandidate"));
        }
    }
    if division {
        if !matches!(&requirements[4],Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir()==args[3].ir() && closed_integer(&f.right)==Some(0))
        {
            return Err(invalid("DenominatorLimitNonzero"));
        }
        let Fact::ForallFact(f) = &requirements[5] else {
            return Err(invalid("DenominatorTermsNonzero"));
        };
        let binder = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
        let input = Obj::Identifier(IdentifierObj::from_bound_name(binder));
        if !f.dom_facts.is_empty()
            || args.iter().any(|a| contains_parameter(a, binder.id))
            || !matches!(f.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(eq))] if super::compile_sequence_analysis::call_matches(&eq.left,&args[1],&input) && closed_integer(&eq.right)==Some(0))
        {
            return Err(invalid("DenominatorTermsNonzero"));
        }
    }
    let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(goal)) = goal else {
        return Err(invalid("Conclusion"));
    };
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
    let (a, b) = binary_operands(id, &g.equal_to).ok_or_else(|| invalid("BodyOperation"))?;
    let (l, r) = binary_operands(id, &goal.value).ok_or_else(|| invalid("LimitOperation"))?;
    if !super::compile_sequence_analysis::call_matches(a, &args[0], &input)
        || !super::compile_sequence_analysis::call_matches(b, &args[1], &input)
        || l.ir() != args[2].ir()
        || r.ir() != args[3].ir()
    {
        return Err(invalid("OriginalOperands"));
    }
    Ok(())
}
fn binary_operands(id: BuiltinTheoremId, object: &Obj) -> Option<(&Obj, &Obj)> {
    use BuiltinTheoremId::*;
    match (id, object) {
        (SequenceLimitAdd, Obj::ArithmeticOperator(ArithmeticOperator::Add(p))) => {
            Some((&p.left, &p.right))
        }
        (SequenceLimitSubtract, Obj::ArithmeticOperator(ArithmeticOperator::Sub(p))) => {
            Some((&p.left, &p.right))
        }
        (SequenceLimitMultiply, Obj::ArithmeticOperator(ArithmeticOperator::Mul(p))) => {
            Some((&p.left, &p.right))
        }
        (SequenceLimitDivide, Obj::ArithmeticOperator(ArithmeticOperator::Div(p))) => {
            Some((&p.left, &p.right))
        }
        _ => None,
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_binary_sequence_limit_law(
        &self,
        id: BuiltinTheoremId,
        args: &[Obj],
        goal: &Fact,
        objects: &[String],
        references: &[String],
        left_domain: &str,
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use BuiltinTheoremId::*;
        let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(goal)) = goal else {
            return Err(invalid("Conclusion"));
        };
        let g = self
            .compile_object_reference(&goal.sequence, scope)?
            .replace('\n', "\n  ");
        let left_real = self.compile_real_membership_certificate(&args[2], scope)?;
        let right_real = self.compile_real_membership_certificate(&args[3], scope)?;
        let right_domain=format!("(Litex.unguardedFunctionDomain {} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {})",objects[1],references[1]);
        let domain_equal="(Litex.FunctionSignature.withGuard_true_domain (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))))";
        let inputs = format!(
            "{} {} {} {} _sequence_map {left_domain} {right_domain} {left_real} {right_real} {} {}",
            objects[0], objects[1], objects[2], objects[3], references[2], references[3]
        );
        if id == SequenceLimitDivide {
            return Ok(format!("(by\n  let _sequence_map := {g}\n  exact Litex.sequenceLimitDivide {inputs} {} (by\n    intro _k _hk\n    exact {} (Litex.semanticObject _k (M.member_isSet _hk)) _hk\n  ) {domain_equal} (by rfl) (by rfl)\n)",references[4],references[5]));
        }
        let (op, symbol, law, cast) = match id {
            SequenceLimitAdd => ("add", "+", "M.add_numbers", "Complex.ofReal_add"),
            SequenceLimitSubtract => ("sub", "-", "M.sub_numbers", "Complex.ofReal_sub"),
            SequenceLimitMultiply => ("mul", "*", "M.mul_numbers", "Complex.ofReal_mul"),
            _ => return Err(invalid("Id")),
        };
        let continuous = format!("((continuous_fst.{op} continuous_snd).continuousAt)");
        let certificate = format!("(by intro _r _s; rw [{law}, {cast}])");
        Ok(format!("(by\n  let _sequence_map := {g}\n  exact Litex.sequenceLimitMapTwo {inputs} M.{op}Value (fun _p : ℝ × ℝ => _p.1 {symbol} _p.2) {continuous} {certificate} {domain_equal} (by rfl) (by rfl)\n)"))
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("SequenceBinaryMap/{stage}"),"Binary sequence-limit laws retain the original ordered sequence/value operands, exact positive-index function and original candidate/nonzero premises and formation stages.")
}
