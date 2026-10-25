use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::NativeConstantMembershipKind;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_native_constant_member(
        &self,
        fact: &InFact,
        kind: &NativeConstantMembershipKind,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use NativeConstantMembershipKind as K;
        let (euler, carrier) = match kind {
            K::EulerNumberInPositiveReal => (true, StandardSet::RPos),
            K::EulerNumberInReal => (true, StandardSet::R),
            K::EulerNumberInComplex => (true, StandardSet::C),
            K::PiInPositiveReal => (false, StandardSet::RPos),
            K::PiInReal => (false, StandardSet::R),
            K::PiInComplex => (false, StandardSet::C),
            _ => return Err(LeanCompileError::unsupported("NativeConstant/Kind")),
        };
        if fact.set != Obj::StandardSet(carrier.clone())
            || !matches!(
                (&fact.element, euler),
                (Obj::Literal(Literal::EulerNumber(_)), true)
                    | (Obj::Literal(Literal::Pi(_)), false)
            )
        {
            return Err(LeanCompileError::unsupported("NativeConstant/Subject"));
        }
        self.compile_real_constant_member(&fact.element, &carrier, position)
    }

    pub(in crate::compile_to_lean) fn compile_real_constant_member(
        &self,
        object: &Obj,
        carrier: &StandardSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let value = native_real_constant(object)
            .ok_or_else(|| LeanCompileError::unsupported("NativeConstant/Subject"))?;
        let positive = match object {
            Obj::Literal(Literal::EulerNumber(_)) => "(Real.exp_pos 1)",
            Obj::Literal(Literal::Pi(_)) => "Real.pi_pos",
            _ => unreachable!(),
        };
        let proof = match carrier {
            StandardSet::RPos => format!("Litex.numberInRPos {value} {positive}"),
            StandardSet::R => format!("Litex.NativeBridge.numberInR {value}"),
            StandardSet::C => format!("Litex.numberInC ({value} : ℂ)"),
            _ => return Err(LeanCompileError::unsupported("NativeConstant/Carrier")),
        };
        Ok(format!(
            "(show Litex.In {} {} from {proof})",
            self.compile_object_reference(object, position)?,
            standard_term(carrier)?
        ))
    }
}
