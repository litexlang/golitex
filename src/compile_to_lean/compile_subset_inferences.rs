use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferSubsetFactResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_subset_inferences(
        &self,
        rules: &[InferSubsetFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = seed else {
            return Err(LeanCompileError::unsupported("SubsetInference/Seed"));
        };
        let mut lines = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let completed = SourcePosition {
                before: index + 1,
                ..*position
            };
            match rule {
                InferSubsetFactResult::FiniteUpperBound(p) => {
                    if p.source_fact_id != seed.fact_id()
                        || !matches!(source_subject(&p.upper_finite_proof)?,Fact::AtomicFact(AtomicFact::IsFiniteSetFact(ref f)) if f.set.ir()==subset.right.ir())
                    {
                        return Err(LeanCompileError::unsupported(
                            "SubsetInference/FinitePremise",
                        ));
                    }
                    let child = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::EqualityRequirements(std::slice::from_ref(
                            &p.upper_finite_proof,
                        )),
                        0,
                    );
                    let finite = self.compile_verify(&p.upper_finite_proof, &child)?.1;
                    let StoreFactResult::AtomicFact(stored) = &p.derived.store else {
                        return Err(LeanCompileError::unsupported("SubsetInference/FiniteStore"));
                    };
                    if !matches!(&stored.fact,AtomicFact::IsFiniteSetFact(f) if f.set.ir()==subset.left.ir())
                    {
                        return Err(LeanCompileError::unsupported(
                            "SubsetInference/FiniteConclusion",
                        ));
                    }
                    let fact = Fact::AtomicFact(stored.fact.clone());
                    self.validate_store(&p.derived.store, &fact)?;
                    let a = self.compile_object_reference(&subset.left, &completed)?;
                    let b = self.compile_object_reference(&subset.right, &completed)?;
                    let proof = format!(
                        "(Litex.finiteSubsetOfFinite {a} {b} {finite} {})",
                        compiled.1
                    );
                    lines.push(self.emit_internal_fact(
                        &fact,
                        &(self.fact_proposition(&fact, &completed)?, proof),
                        &completed,
                    )?);
                }
                InferSubsetFactResult::ElementwiseMembership(p) => {
                    let StoreFactResult::ForallFact(stored) = &p.derived.store else {
                        return Err(LeanCompileError::unsupported(
                            "SubsetInference/ElementwiseStore",
                        ));
                    };
                    let fact = &stored.fact;
                    if fact.typed_parameters.groups.len() != 1
                        || !fact.dom_facts.is_empty()
                        || fact.then_facts.len() != 1
                    {
                        return Err(LeanCompileError::unsupported(
                            "SubsetInference/ElementwiseShape",
                        ));
                    }
                    let group = &fact.typed_parameters.groups[0];
                    if group.params.len() != 1
                        || !matches!(&group.param_type,ParamType::Obj(o) if o.ir()==subset.left.ir())
                    {
                        return Err(LeanCompileError::unsupported(
                            "SubsetInference/ElementwiseBinder",
                        ));
                    }
                    let binder = &group.params[0];
                    if !matches!(&fact.then_facts[0],ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f))
                        if matches!(&f.element,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==binder.id) && f.set.ir()==subset.right.ir())
                    {
                        return Err(LeanCompileError::unsupported(
                            "SubsetInference/ElementwiseConclusion",
                        ));
                    }
                    let source = Fact::ForallFact(fact.clone());
                    self.validate_store(&p.derived.store, &source)?;
                    let a = self.compile_object_reference(&subset.left, &prior)?;
                    let b = self.compile_object_reference(&subset.right, &prior)?;
                    let name = format!("_value_i{}", binder.id.value());
                    let proposition=format!("∀ ({name} : Litex.Obj (M := M) M.Value), Litex.In {name} {a} → Litex.In {name} {b}");
                    let proof = format!(
                        "(fun {name} _member => ({}) (Litex.denote {name}) _member)",
                        compiled.1
                    );
                    lines.push(self.emit_internal_fact(
                        &source,
                        &(proposition, proof),
                        &completed,
                    )?);
                }
            }
        }
        Ok(lines)
    }
}
