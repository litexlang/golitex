use super::compile_builtin_global_continuity_formula::invalid;
use super::helper::source_subject;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_original_continuity_formula_condition(
        &self,
        id: BuiltinTheoremId,
        proof: &VerifyFactResult,
        prior: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let VerifyFactResult::ForallFact(proof) = proof else {
            return Err(invalid("OriginalRestrictionForall"));
        };
        let VerifyForallFactResult::Success(proof) = proof.as_ref() else {
            return Err(invalid("OriginalRestrictionFailure"));
        };
        match proof {
            VerifyForallFactProof::ByKnownForallFact(p) => {
                let scope = SourcePosition::new(
                    Some(prior),
                    SourceOwner::ForallWD(&p.fact, &p.well_defined),
                    0,
                );
                let data = p.well_defined.detailed_ref();
                let [FactWellDefinedProof::Equality(eq)] = data.then.as_slice() else {
                    return Err(invalid("OriginalRestrictionEqualityWD"));
                };
                self.compile_continuity_condition_body(
                    id,
                    &p.fact,
                    eq,
                    &data.introduced_params,
                    &data.assumed_dom_facts,
                    &[],
                    &scope,
                )
            }
            VerifyForallFactProof::ByEmptyParameterDomain(p) => {
                // The emptiness equality is published before the original WD
                // binder scope. Keep its proof and all inferences closed here.
                let empty = SourcePosition::new(Some(prior), SourceOwner::EmptyForall(p), 0);
                let subject = source_subject(&p.empty_carrier_proof)?;
                let compiled = self.compile_verify(&p.empty_carrier_proof, &empty)?;
                self.validate_store(&p.empty_carrier_store.store, &subject)?;
                let mut locals = vec![self.emit_internal_fact(&subject, &compiled, &empty)?];
                let complete = SourcePosition { before: 1, ..empty };
                locals.extend(self.compile_stored_inferences(
                    &p.empty_carrier_store,
                    &subject,
                    &(compiled.0, format!("h_{}", subject.fact_id().value())),
                    &complete,
                )?);
                let scope = SourcePosition::new(
                    Some(&complete),
                    SourceOwner::ForallWD(&p.fact, &p.well_defined),
                    0,
                );
                let data = p.well_defined.detailed_ref();
                let [FactWellDefinedProof::Equality(eq)] = data.then.as_slice() else {
                    return Err(invalid("OriginalRestrictionEmptyEqualityWD"));
                };
                self.compile_continuity_condition_body(
                    id,
                    &p.fact,
                    eq,
                    &data.introduced_params,
                    &data.assumed_dom_facts,
                    &locals,
                    &scope,
                )
            }
            VerifyForallFactProof::ByLocalIntroduction(p) => {
                let scope = SourcePosition::new(Some(prior), SourceOwner::Forall(p), 0);
                let [then] = p.proved_then_facts.as_slice() else {
                    return Err(invalid("OriginalRestrictionThen"));
                };
                let VerifyFactResult::Equality(eq) = &then.verify_result else {
                    return Err(invalid("OriginalRestrictionEquality"));
                };
                let VerifyEqualityResult::Success(eq) = eq.as_ref() else {
                    return Err(invalid("OriginalRestrictionEqualityFailure"));
                };
                self.compile_continuity_condition_body(
                    id,
                    &p.fact,
                    &eq.well_defined_proof,
                    &p.introduced_params,
                    &p.assumed_dom_facts,
                    &[],
                    &scope,
                )
            }
        }
    }
    fn compile_continuity_condition_body(
        &self,
        id: BuiltinTheoremId,
        fact: &ForallFact,
        eq: &EqualFactWellDefinedProof,
        introduced: &IntroduceTypedParametersResult,
        assumed: &[AssumeDomFactResult],
        prefix: &[String],
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use BuiltinTheoremId::*;
        let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equation))] =
            fact.then_facts.as_slice()
        else {
            return Err(invalid("OriginalRestrictionFormula"));
        };
        if !fact.dom_facts.is_empty() {
            return Err(invalid("OriginalRestrictionGuard"));
        }
        let (binders, introductions, mut locals) =
            self.compile_forall_head(fact, introduced, assumed, scope)?;
        let body = SourcePosition {
            before: 1,
            ..*scope
        };
        let data = eq
            .as_detailed()
            .map_err(|_| invalid("OriginalRestrictionDetail"))?;
        super::helper::ensure_object(&equation.right, &data.right)?;
        let operator = self.compile_wd(&data.right, &body)?;
        let arg = match &equation.right {
            Obj::ExpLogOperator(ExpLogOperator::Ln(p)) if id == FnContinuousLn => &p.arg,
            Obj::ExpLogOperator(ExpLogOperator::Log(p)) if id == FnContinuousLog => &p.arg,
            Obj::TrigOperator(TrigOperator::Tan(p)) if id == FnContinuousTan => &p.arg,
            Obj::TrigOperator(TrigOperator::Cot(p)) if id == FnContinuousCot => &p.arg,
            Obj::TrigOperator(TrigOperator::Sec(p)) if id == FnContinuousSec => &p.arg,
            Obj::TrigOperator(TrigOperator::Csc(p)) if id == FnContinuousCsc => &p.arg,
            Obj::HyperbolicOperator(HyperbolicOperator::Coth(p)) if id == FnContinuousCoth => {
                &p.arg
            }
            Obj::HyperbolicOperator(HyperbolicOperator::Csch(p)) if id == FnContinuousCsch => {
                &p.arg
            }
            _ => return Err(invalid("OriginalRestrictionOperator")),
        };
        let input = self.compile_object_reference(arg, &body)?;
        let (condition, leaf) = match id {
            FnContinuousLn => (
                format!("Litex.RealLtValue M (M.number 0) (Litex.denote {input})"),
                "Litex.inRPos_positive _original_operator.val.arg _original_operator.wd",
            ),
            FnContinuousLog => (
                format!("Litex.RealLtValue M (M.number 0) (Litex.denote {input})"),
                "_original_operator.wd.2.2.2.1",
            ),
            FnContinuousTan | FnContinuousSec => (
                format!("Litex.realUnaryValue Real.cos (Litex.denote {input}) ≠ M.number 0"),
                "_original_operator.wd.2",
            ),
            FnContinuousCot | FnContinuousCsc => (
                format!("Litex.realUnaryValue Real.sin (Litex.denote {input}) ≠ M.number 0"),
                "_original_operator.wd.2",
            ),
            FnContinuousCoth | FnContinuousCsch => (
                format!("Litex.denote {input} ≠ M.number 0"),
                "_original_operator.wd.2",
            ),
            _ => return Err(invalid("OriginalRestrictionLaw")),
        };
        let proposition = self.scope_proposition(condition, &locals);
        let proposition =
            self.scope_proposition(format!("∀ {}, {proposition}", binders.join(" ")), prefix);
        locals.push(format!("let _original_operator := {operator}"));
        let definitions = locals.join("\n").replace('\n', "\n  ");
        Ok(format!(
            "(show ({proposition}) from (by\n  {}\n  intro {}\n  {definitions}\n  exact {leaf}\n))",
            prefix.join("\n").replace('\n', "\n  "),
            introductions.join(" ")
        ))
    }
}
