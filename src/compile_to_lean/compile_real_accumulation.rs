//! Replay real-subset accumulation facts and their original quantified witnesses.
use super::compile_function_continuity::continuity_side;
use super::compile_function_limit_definition::validate_approach_accumulation;
use super::compile_real_set_bounds::parameter;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferRealAccumulationFactResult};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_real_accumulation_definition(
        &self,
        source: &RealAccumulationFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ([clause], [checked]) = (requirements, proofs) else {
            return Err(invalid("DefinitionArity"));
        };
        validate_clause(source, clause)?;
        if source_subject(checked)? != *clause {
            return Err(invalid("DefinitionSubject"));
        }
        let (ty, term) = self.compile_verify(checked, &position.atomic_search_prior(0)?)?;
        let formed = position.atomic_search_prior(1)?;
        let domain = self.compile_object_reference(&source.domain, &formed)?;
        let point = self.compile_object_reference(&source.point, &formed)?;
        let side = continuity_side(source.side);
        Ok(format!(
            "(Litex.realAccumulationOfForall .{side} {domain} {point} (show {ty} from {term}))"
        ))
    }

    pub(super) fn compile_real_accumulation_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::RealAccumulationFact(rules),
            Fact::AtomicFact(AtomicFact::RealAccumulationFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let [InferRealAccumulationFactResult::Definition(proof)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        let [stored] = proof.derived.as_slice() else {
            return Err(invalid("InferenceArity"));
        };
        if proof.source_fact_id != seed.fact_id() {
            return Err(invalid("InferenceIdentity"));
        }
        let fact = self.resolve_fact(stored.primary_fact_id(), position)?;
        self.validate_store(&stored.store, &fact)?;
        validate_clause(source, &fact)?;
        let Fact::ForallFact(all) = &fact else {
            unreachable!()
        };
        let radius = parameter(&all.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
        let id = radius.id.value();
        let value = format!("_value_i{id}");
        let raw = format!("(Litex.denote {value})");
        let header=format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}) (_member_i{id} : Litex.In {value} (Litex.RPos (M := M)))");
        let clause = self.compile_function_raw_predicate(
            &all.then_facts[0].clone().into(),
            position,
            &HashMap::from([(radius.id, raw.clone())]),
        )?;
        let ty = format!("∀ {header}, {clause}");
        let term = format!("(fun {header} => ({}) {raw} _member_i{id})", compiled.1);
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(ty, term),
            position,
        )?])
    }

    pub(super) fn validate_real_accumulation_domain(
        &self,
        fact: &AtomicFact,
        requirements: &[&Fact],
    ) -> Result<(), LeanCompileError> {
        let Some((domain, point, _, _)) = accumulation_parts(fact) else {
            return Ok(());
        };
        if !matches!(requirements,[Fact::AtomicFact(AtomicFact::SubsetFact(a)),Fact::AtomicFact(AtomicFact::InFact(b))]
            if a.left.ir()==domain.ir()&&a.right==Obj::StandardSet(StandardSet::R)
                &&b.element.ir()==point.ir()&&b.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("DomainRequirements"));
        }
        Ok(())
    }
}
pub(super) fn accumulation_parts(
    fact: &AtomicFact,
) -> Option<(&Obj, &Obj, RealApproachSide, bool)> {
    Some(match fact {
        AtomicFact::RealAccumulationFact(f) => (&f.domain, &f.point, f.side, false),
        AtomicFact::NotRealAccumulationFact(f) => (&f.domain, &f.point, f.side, true),
        _ => return None,
    })
}
fn validate_clause(source: &RealAccumulationFact, clause: &Fact) -> Result<(), LeanCompileError> {
    let domain = validate_approach_accumulation(
        &source.side.limit_approach(source.point.clone()),
        &[&source.domain],
        clause,
    )?;
    if domain.ir() != source.domain.ir() {
        return Err(invalid("WitnessDomain"));
    }
    Ok(())
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RealAccumulation/{stage}"))
}
