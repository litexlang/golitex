//! Replay existing positive-indexed real-sequence definitions and inference IDs.
use super::compile_real_set_bounds::{contains_parameter, validate_existence};
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferSequenceAnalysisFactResult};
use std::collections::HashMap;

pub(super) fn sequence_parts(fact: &AtomicFact) -> Option<(&Obj, SequenceAnalysisProperty, bool)> {
    Some(match fact {
        AtomicFact::SequenceAnalysisFact(f) => (&f.sequence, f.property, false),
        AtomicFact::NotSequenceAnalysisFact(f) => (&f.sequence, f.property, true),
        _ => return None,
    })
}
pub(super) fn sequence_name(
    kind: SequenceAnalysisProperty,
) -> Result<&'static str, LeanCompileError> {
    use SequenceAnalysisProperty::*;
    Ok(match kind {
        Nondecreasing => "Nondecreasing",
        Nonincreasing => "Nonincreasing",
        StrictlyIncreasing => "StrictlyIncreasing",
        StrictlyDecreasing => "StrictlyDecreasing",
        BoundedAbove => "BoundedAbove",
        BoundedBelow => "BoundedBelow",
        Bounded => "Bounded",
        Cauchy => "Cauchy",
        Convergent => "Convergent",
    })
}
fn boundedness(kind: SequenceAnalysisProperty) -> Option<RealBoundedness> {
    use SequenceAnalysisProperty::*;
    match kind {
        BoundedAbove => Some(RealBoundedness::Above),
        BoundedBelow => Some(RealBoundedness::Below),
        Bounded => Some(RealBoundedness::Both),
        _ => None,
    }
}
fn order_kind(kind: SequenceAnalysisProperty) -> Result<(bool, bool), LeanCompileError> {
    use SequenceAnalysisProperty::*;
    match kind {
        Nondecreasing => Ok((false, false)),
        Nonincreasing => Ok((false, true)),
        StrictlyIncreasing => Ok((true, false)),
        StrictlyDecreasing => Ok((true, true)),
        _ => Err(invalid("OrderProperty")),
    }
}
fn is_range(range: &Obj, sequence: &Obj) -> bool {
    matches!(range, Obj::FunctionSpace(FunctionSpace::FnRange(f)) if f.function.ir() == sequence.ir())
}
fn bound_clause<'a>(
    source: &SequenceAnalysisFact,
    clause: &'a Fact,
) -> Result<&'a Obj, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::RealSetBoundedFact(f)) = clause else {
        return Err(invalid("BoundClause"));
    };
    if Some(f.boundedness) != boundedness(source.property) || !is_range(&f.set, &source.sequence) {
        return Err(invalid("BoundRange"));
    }
    Ok(&f.set)
}
pub(super) fn call_matches(obj: &Obj, sequence: &Obj, argument: &Obj) -> bool {
    matches!(obj, Obj::FnObj(f) if f.head.as_ref() == &FnObjHead::from_obj(sequence.clone())
        && matches!(f.body.as_slice(), [args] if matches!(args.as_slice(), [arg] if arg.ir() == argument.ir())))
}
fn order_clause<'a>(
    source: &SequenceAnalysisFact,
    clause: &'a Fact,
) -> Result<(&'a ForallFact, Vec<&'a BoundName>), LeanCompileError> {
    let (strict, reverse) = order_kind(source.property)?;
    let Fact::ForallFact(f) = clause else {
        return Err(invalid("Universal"));
    };
    let mut params = Vec::new();
    for group in &f.typed_parameters.groups {
        if group.params.is_empty()
            || !matches!(
                &group.param_type,
                ParamType::Obj(Obj::StandardSet(StandardSet::NPos))
            )
        {
            return Err(invalid("IndexCarrier"));
        }
        params.extend(&group.params);
    }
    if params.len() != 2
        || params[0].id == params[1].id
        || params
            .iter()
            .any(|p| contains_parameter(&source.sequence, p.id))
    {
        return Err(invalid("IndexBinders"));
    }
    let m = Obj::Identifier(IdentifierObj::from_bound_name(params[0]));
    let n = Obj::Identifier(IdentifierObj::from_bound_name(params[1]));
    let [Fact::AtomicFact(dom)] = f.dom_facts.as_slice() else {
        return Err(invalid("OrderPremise"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(conclusion)] = f.then_facts.as_slice() else {
        return Err(invalid("OrderConclusion"));
    };
    let (a, b, s) = source_order_oriented(dom)?;
    if a.ir() != m.ir() || b.ir() != n.ir() || s != strict {
        return Err(invalid("IndexComparison"));
    }
    let (a, b, s) = source_order_oriented(conclusion)?;
    let (first, second) = if reverse { (&n, &m) } else { (&m, &n) };
    if s != strict
        || !call_matches(a, &source.sequence, first)
        || !call_matches(b, &source.sequence, second)
    {
        return Err(invalid("ValueComparison"));
    }
    Ok((f, params))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_sequence_analysis_domain(
        &self,
        fact: &AtomicFact,
        source: &CompleteFunctionDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let sequence = if let Some((sequence, kind, _)) = sequence_parts(fact) {
            sequence_name(kind)?;
            sequence
        } else if let Some((sequence, _, _)) = super::compile_sequence_epsilon::limit_parts(fact) {
            sequence
        } else {
            return Err(invalid("DomainSubject"));
        };
        let signature = &source.signature;
        if !matches!(signature.set_bound_parameters.groups.as_slice(), [g] if g.params.len() == 1 && g.param_type.as_ref() == &Obj::StandardSet(StandardSet::NPos))
            || !signature.dom_facts.is_empty()
            || signature.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
        {
            return Err(invalid("CompleteSignature"));
        }
        let proof = self.compile_complete_domain_member(sequence, source, position)?;
        let value = self.compile_object_reference(sequence, position)?;
        let signature = self.compile_complete_domain_signature(source, position)?;
        Ok(format!(
            "have _sequence_domain : Litex.In {value} (Litex.fnSet {signature}) := {proof}"
        ))
    }

    pub(super) fn compile_sequence_analysis_definition(
        &self,
        source: &SequenceAnalysisFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        sequence_name(source.property)?;
        if source.property == SequenceAnalysisProperty::Cauchy {
            return self.compile_sequence_epsilon_definition(
                &source.sequence,
                None,
                requirements,
                proofs,
                position,
            );
        }
        let ([clause], [proof]) = (requirements, proofs) else {
            return Err(invalid("DefinitionArity"));
        };
        if source_subject(proof)? != *clause {
            return Err(invalid("DefinitionSubject"));
        }
        if boundedness(source.property).is_some() {
            bound_clause(source, clause)?;
        } else if source.property == SequenceAnalysisProperty::Convergent {
            super::compile_sequence_epsilon::validate_limit_existence(&source.sequence, clause)?;
        } else {
            order_clause(source, clause)?;
        }
        let prior = position.atomic_search_prior(0)?;
        let (ty, term) = self.compile_verify(proof, &prior)?;
        if boundedness(source.property).is_some()
            || source.property == SequenceAnalysisProperty::Convergent
        {
            return Ok(format!("(show {ty} from {term})"));
        }
        let (strict, reverse) = order_kind(source.property)?;
        Ok(format!(
            "(Litex.sequenceOrderOfForall {strict} {reverse} {} (show {ty} from {term}))",
            self.compile_object_reference(&source.sequence, position)?
        ))
    }

    pub(super) fn compile_sequence_analysis_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (
            InferAtomicFactResult::SequenceAnalysisFact(rules),
            Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(source)),
        ) = (infer, seed)
        else {
            return Err(invalid("InferenceFamily"));
        };
        let [InferSequenceAnalysisFactResult::Definition(p)] = rules.as_slice() else {
            return Err(invalid("InferenceRule"));
        };
        sequence_name(source.property)?;
        let kind = boundedness(source.property);
        let count = match kind {
            Some(RealBoundedness::Both) => 5,
            Some(_) => 2,
            None => 1,
        };
        if p.source_fact_id != seed.fact_id() || p.derived.len() != count {
            return Err(invalid("InferenceIdentity"));
        }
        let mut out = Vec::new();
        for (index, stored) in p.derived.iter().enumerate() {
            let prior = SourcePosition {
                before: position.before + index,
                ..*position
            };
            let fact = self.resolve_fact(stored.primary_fact_id(), &prior)?;
            self.validate_store(&stored.store, &fact)?;
            let (ty, term) = if let Some(kind) = kind {
                let first = self.resolve_fact(p.derived[0].primary_fact_id(), &prior)?;
                let range = bound_clause(source, &first)?;
                let term = match index {
                    0 => compiled.1.clone(),
                    1 | 2 if index == 1 || kind == RealBoundedness::Both => {
                        let direction = if kind == RealBoundedness::Above || index == 2 {
                            RealBoundDirection::Upper
                        } else {
                            RealBoundDirection::Lower
                        };
                        validate_existence(range, direction, &fact)?;
                        if kind == RealBoundedness::Both {
                            format!("({}).{index}", compiled.1)
                        } else {
                            compiled.1.clone()
                        }
                    }
                    3 | 4 if kind == RealBoundedness::Both => {
                        let expected = if index == 3 {
                            SequenceAnalysisProperty::BoundedAbove
                        } else {
                            SequenceAnalysisProperty::BoundedBelow
                        };
                        if !matches!(&fact,Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) if f.sequence.ir() == source.sequence.ir() && f.property == expected)
                        {
                            return Err(invalid("BoundedComponent"));
                        }
                        format!("({}).{}", compiled.1, if index == 3 { 2 } else { 1 })
                    }
                    _ => return Err(invalid("BoundedInferenceIndex")),
                };
                (
                    self.compile_function_raw_predicate(&fact, &prior, &HashMap::new())?,
                    term,
                )
            } else if source.property == SequenceAnalysisProperty::Cauchy {
                self.compile_sequence_epsilon_inference(
                    &source.sequence,
                    &fact,
                    &compiled.1,
                    &prior,
                )?
            } else if source.property == SequenceAnalysisProperty::Convergent {
                super::compile_sequence_epsilon::validate_limit_existence(&source.sequence, &fact)?;
                (
                    self.compile_function_raw_predicate(&fact, &prior, &HashMap::new())?,
                    compiled.1.clone(),
                )
            } else {
                let (all, params) = order_clause(source, &fact)?;
                let mut bindings = HashMap::new();
                let mut header = Vec::new();
                let mut arguments = Vec::new();
                for p in params {
                    let id = p.id.value();
                    let value = format!("_value_i{id}");
                    let raw = format!("(Litex.denote {value})");
                    header.push(format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({value} : Litex.Obj (M := M) _Host_i{id}) (_member_i{id} : Litex.In {value} (Litex.NPos (M := M)))"));
                    arguments.push(format!("{raw} _member_i{id}"));
                    bindings.insert(p.id, raw);
                }
                let premise =
                    self.compile_function_raw_predicate(&all.dom_facts[0], &prior, &bindings)?;
                let premise_name = format!("h_{}", all.dom_facts[0].fact_id().value());
                header.push(format!("({premise_name} : {premise})"));
                arguments.push(premise_name);
                let conclusion = self.compile_function_raw_predicate(
                    &all.then_facts[0].clone().into(),
                    &prior,
                    &bindings,
                )?;
                let header = header.join(" ");
                (
                    format!("∀ {header}, {conclusion}"),
                    format!("(fun {header} => ({}) {})", compiled.1, arguments.join(" ")),
                )
            };
            out.push(self.emit_internal_fact(&fact, &(ty, term), &prior)?);
        }
        Ok(out)
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("SequenceAnalysis/{stage}"),"Sequence evidence differs in its function, positive-natural carrier, binder, order or inference identity.")
}
