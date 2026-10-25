use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_real_interval_inference(
        &self,
        stores: &[&StoreInferredFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(source)) = seed else {
            return Err(LeanCompileError::unsupported(
                "RealInterval/InferenceSource",
            ));
        };
        let (law, bounds) = match &source.set {
            Obj::SetFormer(SetFormer::IntervalObj(p)) => {
                let (a, b, lc, rc) = real_interval_parts(p);
                (
                    "inRealInterval_iff",
                    vec![(a, &source.element, lc), (&source.element, b, rc)],
                )
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) => {
                let (a, lower, closed) = real_ray_parts(p);
                (
                    "inRealRay_iff",
                    vec![if lower {
                        (a, &source.element, closed)
                    } else {
                        (&source.element, a, closed)
                    }],
                )
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "RealInterval/InferenceSource",
                ))
            }
        };
        if stores.len() != bounds.len() + 1 {
            return Err(LeanCompileError::unsupported(
                "RealInterval/InferenceStages",
            ));
        }
        let carrier = self.compile_object_reference(&source.set, position)?;
        let element = self.compile_object_reference(&source.element, position)?;
        let expanded = format!("((Litex.{law} {carrier} {element}).mp {})", compiled.1);
        let fields = if bounds.len() == 2 {
            vec![".1", ".2.1", ".2.2"]
        } else {
            vec![".1", ".2"]
        };
        let mut ids = std::collections::HashSet::from([source.fact_id]);
        let mut output = Vec::new();
        for (i, captured) in stores.iter().enumerate() {
            let store = &captured.store;
            let fact = self.resolve_fact(store.primary_fact_id(), position)?;
            self.validate_store(store, &fact)?;
            if !ids.insert(fact.fact_id()) {
                return Err(LeanCompileError::unsupported(
                    "RealInterval/InferenceIdentity",
                ));
            }
            let valid = if i == 0 {
                matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==source.element.ir() && f.set==Obj::StandardSet(StandardSet::R))
            } else {
                let (a, b, closed) = bounds[i - 1];
                real_bound_subject(&fact, a, b, closed)
            };
            if !valid {
                return Err(LeanCompileError::unsupported(
                    "RealInterval/InferenceConclusion",
                ));
            }
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::InferredStore(store),
                usize::MAX,
            );
            output.push(self.emit_internal_fact(
                &fact,
                &(
                    self.fact_proposition(&fact, &formed)?,
                    format!("{expanded}{}", fields[i]),
                ),
                &formed,
            )?);
        }
        Ok(output)
    }
}
