use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_forall_fact::VerifyEmptyParameterDomainForallProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_empty_parameter_domain(
        &self,
        proof: &VerifyEmptyParameterDomainForallProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let group = proof
            .fact
            .typed_parameters
            .groups
            .get(proof.parameter_group_index)
            .ok_or_else(|| {
                LeanCompileError::new(
                    "EmptyForall/Group",
                    "The empty input group is outside the original header.",
                )
            })?;
        let ParamType::Obj(carrier) = &group.param_type else {
            return Err(LeanCompileError::new(
                "EmptyForall/CarrierKind",
                "Only an actual empty element domain removes input assignments.",
            ));
        };
        if group.params.is_empty() || carrier.ir() != proof.empty_carrier.ir() {
            return Err(LeanCompileError::new(
                "EmptyForall/CarrierSubject",
                "Empty-domain evidence refers to another carrier or no parameter.",
            ));
        }
        let empty_subject = source_subject(&proof.empty_carrier_proof)?;
        if !matches!(&empty_subject, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir() == carrier.ir() && matches!(&f.right, Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty()))
        {
            return Err(LeanCompileError::new("EmptyForall/EqualitySubject", "The selected source proof does not identify this exact domain with the empty enumeration."));
        }
        let scope = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::EmptyForall(proof),
            before: 0,
        };
        let equality = self.compile_verify(&proof.empty_carrier_proof, &scope)?;
        self.validate_store(&proof.empty_carrier_store.store, &empty_subject)?;
        let completed = SourcePosition { before: 1, ..scope };
        let header = SourcePosition {
            parent: Some(&completed),
            owner: SourceOwner::ForallWD(&proof.fact, &proof.well_defined),
            before: 0,
        };
        let (binders, introductions, definitions) = self.compile_forall_head(
            &proof.fact,
            &proof.well_defined.introduced_params,
            &proof.well_defined.assumed_dom_facts,
            &header,
        )?;
        let head = proof
            .fact
            .typed_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>()
            + proof.fact.dom_facts.len();
        if proof.well_defined.then.len() != proof.fact.then_facts.len()
            || proof.fact.then_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "EmptyForall/ConclusionWD",
                "The vacuous proof still needs every actual conclusion formation check.",
            ));
        }
        let mut conclusions = Vec::new();
        for (i, (fact, wd)) in proof
            .fact
            .then_facts
            .iter()
            .zip(&proof.well_defined.then)
            .enumerate()
        {
            let ExistOrAndChainAtomicFact::AtomicFact(fact) = fact else {
                return Err(LeanCompileError::unsupported(
                    "EmptyForall/CompoundConclusion",
                ));
            };
            let fact = Fact::AtomicFact(fact.clone());
            let prior = SourcePosition {
                before: head + i,
                ..header
            };
            self.compile_fact_wd(wd, &fact, &prior)?;
            let formed = SourcePosition {
                parent: Some(&prior),
                owner: SourceOwner::FactWD(wd),
                before: usize::MAX,
            };
            conclusions.push(self.fact_proposition(&fact, &formed)?);
        }
        let meaning = conclusions
            .into_iter()
            .rev()
            .reduce(|tail, head| format!("({head} ∧ {tail})"))
            .unwrap();
        let meaning = self.scope_proposition(meaning, &definitions);
        let proposition = format!("∀ {}, {meaning}", binders.join(" "));
        let formed = SourcePosition {
            before: head,
            ..header
        };
        let parameter = &group.params[0];
        let element = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let offset = proof
            .fact
            .typed_parameters
            .groups
            .iter()
            .take(proof.parameter_group_index)
            .map(|g| g.params.len())
            .sum::<usize>();
        let membership = &proof
            .well_defined
            .introduced_params
            .defined_params
            .store_and_infer_results[offset];
        let a = self.compile_object_reference(&element, &formed)?;
        let bound = self.compile_object_reference(carrier, &formed)?;
        let source_equality = format!("h_{}", empty_subject.fact_id().value());
        let source_member = format!("h_{}", membership.primary_fact_id().value());
        let contradiction = format!("(Litex.notInEmpty {a} (Litex.inOfSame {a} {a} {bound} (Litex.emptySet (M := M)) (Litex.sameRefl {a}) {source_equality} {source_member}))");
        let body = format!("(by\n  have {source_equality} : {} := {}\n  intro {}\n  {}\n  exact False.elim {contradiction})", equality.0, equality.1, introductions.join(" "), definitions.join("\n").replace('\n', "\n  "));
        Ok((proposition, body))
    }
}
