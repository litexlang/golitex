//! Replay primitive derivatives from the original interior and formula.
use super::compile_function_derivative_definition::validate_derivative_interior;
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DerivativeFormulaBuiltin/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_derivative_formula(
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
        use BuiltinTheoremId::*;
        let (constant, elementary) = match builtin.theorem {
            FnDerivativeAtConstant => (true, None),
            FnDerivativeAtIdentity => (false, None),
            FnDerivativeAtExp => (false, Some(K::Exp)),
            FnDerivativeAtSin => (false, Some(K::Sin)),
            FnDerivativeAtCos => (false, Some(K::Cos)),
            FnDerivativeAtLn => (false, Some(K::Ln)),
            FnDerivativeAtSqrt => (false, Some(K::Sqrt)),
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = if constant || elementary.is_some() {
            7
        } else {
            6
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let (signature, _) = real_limit_signature(&req[..3], &args[0])?;
        let Fact::AtomicFact(AtomicFact::InFact(point)) = &req[3] else {
            return Err(invalid("PointMember"));
        };
        if point.element.ir() != args[1].ir() || !signature_domain_matches(&point.set, signature) {
            return Err(invalid("ActualPointDomain"));
        }
        validate_derivative_interior(&args[0], &args[1], &point.set, &req[4])?;
        if constant
            && !matches!(&req[5],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir()&&f.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("ConstantMember"));
        }
        if let Some(kind) = elementary {
            let carrier = Obj::StandardSet(if matches!(kind, K::Ln | K::Sqrt) {
                StandardSet::RPos
            } else {
                StandardSet::R
            });
            if !matches!(&req[5],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir()&&f.set==carrier)
            {
                return Err(invalid("ElementaryPointCondition"));
            }
        }
        let Fact::ForallFact(formula) = &req[count - 1] else {
            return Err(invalid("Formula"));
        };
        let x = parameter(&formula.typed_parameters, &point.set)?;
        let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
        let rhs = if constant {
            args[2].clone()
        } else if let Some(kind) = elementary {
            kind.apply(input.clone())
        } else {
            input.clone()
        };
        if !formula.dom_facts.is_empty()
            || args.iter().any(|a| contains_parameter(a, x.id))
            || contains_parameter(&point.set, x.id)
            || !matches!(formula.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] if call_matches(&eq.left,&args[0],&input)&&eq.right.ir()==rhs.ir())
        {
            return Err(invalid("OriginalFormula"));
        }
        let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(goal)) = &builtin.conclusions[0]
        else {
            return Err(invalid("Conclusion"));
        };
        if goal.function.ir() != args[0].ir()
            || goal.point.ir() != args[1].ir()
            || if let Some(kind) = elementary {
                goal.value.ir() != kind.derivative_factor(args[1].clone()).ir()
            } else {
                !matches!(&goal.value,Obj::Literal(Literal::Number(n)) if n.normalized_value==if constant {"0"} else {"1"})
            }
        {
            return Err(invalid("ConclusionSubject"));
        }
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((fact, checked), store)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            let reference = format!("h_{}", fact.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                store,
                fact,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|a| self.compile_object_reference(a, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let f = &objects[0];
        let p = &objects[1];
        let real = self.compile_real_membership_certificate(&args[1], &scope)?;
        let mut steps = self.compile_function_limit_context(
            0,
            &args[0],
            &point.set,
            &req[..3],
            &references[..3],
            &scope,
        )?;
        steps.push(format!("have _point_real : Litex.In {p} Litex.R := {real}"));
        steps.push(format!(
            "let _real_point := Litex.NativeBridge.asReal {p} _point_real"
        ));
        steps.push(format!("have _point_value : Litex.denote {p}=M.number (_real_point : ℂ) := Litex.NativeBridge.asReal_spec {p} _point_real"));
        steps.push(format!("have _interior : Litex.DerivativeInteriorClauseValue M (Litex.denote {f}) (Litex.denote {p}) := by\n  unfold Litex.DerivativeInteriorClauseValue\n  rw [← _law_domain_0]\n  exact {}",references[4]));
        let coefficient = if elementary.is_some() {
            self.compile_function_raw_expression_bound(&goal.value, &scope, &HashMap::new())?
        } else {
            format!("(M.number {})", if constant { "0" } else { "1" })
        };
        let (raw, native) = if let Some(kind) = elementary {
            let (operation, law) = match kind {
                K::Exp => ("(Litex.realUnaryValue (M := M) Real.exp)", "Exp"),
                K::Sin => ("(Litex.realUnaryValue (M := M) Real.sin)", "Sin"),
                K::Cos => ("(Litex.realUnaryValue (M := M) Real.cos)", "Cos"),
                K::Ln => ("(Litex.realUnaryValue (M := M) Real.log)", "Ln"),
                K::Sqrt => ("(Litex.sqrtValue (M := M))", "Sqrt"),
            };
            let raw = format!("(fun (x : ℝ) => {operation} (M.number (x : ℂ)))");
            let positive = matches!(kind, K::Ln | K::Sqrt);
            let condition = if positive {
                format!(" (by rw [← _point_value]; exact {})", references[5])
            } else {
                String::new()
            };
            let finish = if positive {
                "exact _elementary".into()
            } else {
                let real = self.compile_real_membership_certificate(&goal.value, &scope)?;
                format!("exact Litex.semanticDerivativeDropUnit {raw} _real_point {coefficient} {real} _elementary")
            };
            let native = format!("(by\n  have _elementary := Litex.semanticDerivative{law} (fun (x : ℝ) => M.number (x : ℂ)) _real_point (M.number 1){condition} (Litex.semanticDerivativeVariable _real_point)\n  rw [← _point_value] at _elementary\n  {finish}\n)");
            (raw, native)
        } else if constant {
            (
                format!("(fun (_ : ℝ) => Litex.denote {})", objects[2]),
                format!(
                    "(Litex.semanticDerivativeConstant (Litex.denote {}) _real_point {})",
                    objects[2], references[5]
                ),
            )
        } else {
            (
                "(fun (x : ℝ) => M.number (x : ℂ))".into(),
                "(Litex.semanticDerivativeVariable _real_point)".into(),
            )
        };
        let formula = format!("(by\n  intro x hx\n  exact {} (Litex.semanticObject (M.number (x : ℂ)) (M.member_isSet hx)) (show M.mem (M.number (x : ℂ)) (Litex.denote _law0_domain) from _law_domain_0.symm ▸ hx)\n)",references[count-1]);
        steps.push(format!("exact Litex.derivativeOfSemanticFormula (Litex.denote {f}) (Litex.denote {p}) {coefficient} _real_point {raw} _point_value _interior {formula} {native}"));
        let proof = format!(
            "(by\n{}\n)",
            steps
                .join("\n")
                .lines()
                .map(|line| format!("  {line}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
