use crate::compile_to_lean::compile_callee_constructor::exact_constructor_pattern;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Instantiate only a constructor retained in the exact builder clause
    /// which produced this inferred subject. Earlier clause proofs are actual
    /// ordered projections, closed over inside the returned factory.
    pub(in crate::compile_to_lean) fn compile_inferred_builder_constructor(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some(step) = position.inferred_builder_step(store) else {
            return Ok(None);
        };
        let Some(crate::store_fact_and_infer::InferSetBuilderProjectionResult::Condition {
            condition_index,
            ..
        }) = step
            .projections
            .iter()
            .find(|p| std::ptr::eq(&p.stored().store, store))
        else {
            return Ok(None);
        };
        let index = *condition_index;
        let source = step
            .builder
            .facts
            .get(index)
            .ok_or_else(|| LeanCompileError::unsupported("SetBuilder/ConstructorClause"))?;
        let source = crate::instantiate::quantifier_free_fact_to_fact(source.clone());
        let substitution = HashMap::from([(
            step.builder.param_binding.id,
            step.source_membership.element.clone(),
        )]);
        let roots: Vec<&Obj> = match &source {
            Fact::AtomicFact(f) => atomic_fact_args_ref(f),
            Fact::AndFact(f) => f.facts.iter().flat_map(atomic_fact_args_ref).collect(),
            Fact::ChainFact(f) => f.objs.iter().collect(),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "SetBuilder/ConstructorClauseFamily",
                ))
            }
        };
        let Some(pattern) = roots
            .into_iter()
            .find_map(|r| exact_constructor_pattern(r, object, &substitution))
        else {
            return Ok(None);
        };
        let builder = Obj::SetFormer(SetFormer::SetBuilder(step.builder.clone()));
        position.with_visible_wd(&builder, &mut |wd, declaration| {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(captured)), ..
            } = (wd).detailed_ref() else { return Err(LeanCompileError::unsupported("SetBuilder/ConstructorFormation")) };
            let scope = SourcePosition::new(Some(declaration), SourceOwner::SetBuilder(&step.builder, captured), 0);
            self.validate_parameter_store_capture(&captured.defined_params)?;
            if captured.defined_params.store_and_infer_results.len() != 1 || captured.assumed_facts.len() != step.builder.facts.len() {
                return Err(LeanCompileError::unsupported("SetBuilder/ConstructorStages"));
            }
            let introduced = SourcePosition { before: 2, ..scope };
            let binder = &captured.defined_params.store_and_infer_results[0];
            let binder_fact = self.resolve_fact(binder.primary_fact_id(), &introduced)?;
            let binder_name = format!("h_{}", binder_fact.fact_id().value());
            self.compile_wd(&captured.param_set_well_defined, &scope)?;
            let mut binders = vec![format!("(_value_i{} : Litex.Obj (M := M) M.Value)", step.builder.param_binding.id.value()),
                format!("({binder_name} : {})", self.fact_proposition(&binder_fact, &introduced)?)];
            let mut definitions = self.compile_parameter_inferences(binder, &binder_fact,
                &(self.fact_proposition(&binder_fact, &introduced)?, binder_name), &introduced)?;
            let value = self.compile_object_reference(&step.source_membership.element, position)?;
            let mut arguments = vec![format!("(Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value}))")];
            let base = step.projections.iter().find_map(|p| match p {
                crate::store_fact_and_infer::InferSetBuilderProjectionResult::BaseMembership(s) => Some(s), _ => None,
            });
            let base_member = if let Some(base) = base {
                self.cited_fact_reference(base.primary_fact_id(), position)?.1
            } else if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &step.source_membership.element {
                let (_, carrier, _, hypothesis) = position.visible_parameter(*id, &self.runtime)?;
                if carrier.is_none_or(|set| set.ir() != step.builder.param_set.ir()) {
                    return Err(LeanCompileError::unsupported("SetBuilder/ConstructorBoundParameter"));
                }
                hypothesis
            } else {
                return Err(LeanCompileError::unsupported("SetBuilder/ConstructorBoundProjection"));
            };
            arguments.push(base_member);
            for i in 0..index {
                let clause = crate::instantiate::quantifier_free_fact_to_fact(step.builder.facts[i].clone());
                let captured_clause = &captured.assumed_facts[i];
                let prior = SourcePosition { before: 2 + i, ..scope };
                self.compile_fact_wd(&captured_clause.well_defined, &clause, &prior)?;
                self.validate_store(&captured_clause.store_and_infer.store, &clause)?;
                let formed = SourcePosition::new(Some(&prior), SourceOwner::FactWD(&captured_clause.well_defined), usize::MAX);
                let proposition = self.scope_proposition(self.fact_proposition(&clause, &formed)?, &definitions);
                let name = format!("h_{}", clause.fact_id().value());
                binders.push(format!("({name} : {proposition})"));
                let complete = SourcePosition { before: 3 + i, ..scope };
                definitions.extend(self.compile_stored_inferences(&captured_clause.store_and_infer, &clause,
                    &(self.fact_proposition(&clause, &formed)?, name), &complete)?);
                let projection = step.projections.iter().find_map(|p| match p {
                    crate::store_fact_and_infer::InferSetBuilderProjectionResult::Condition { condition_index, stored } if *condition_index == i => Some(stored), _ => None,
                }).ok_or_else(|| LeanCompileError::unsupported("SetBuilder/ConstructorPriorProjection"))?;
                arguments.push(self.cited_fact_reference(projection.primary_fact_id(), position)?.1);
            }
            let prior = SourcePosition { before: 2 + index, ..scope };
            let formation = &captured.assumed_facts[index].well_defined;
            let formed = SourcePosition::new(Some(&prior), SourceOwner::FactWD(formation), usize::MAX);
            let constructor = formed.with_visible_wd(pattern, &mut |original, producer| self.compile_wd(original, producer))?
                .ok_or_else(|| LeanCompileError::unsupported("SetBuilder/ConstructorProducer"))?;
            let body = if definitions.is_empty() { constructor } else {
                format!("(by\n  {}\n  exact {constructor}\n)", definitions.join("\n").replace('\n', "\n  "))
            };
            Ok(format!("((fun {} => {body}) {})", binders.join(" "), arguments.join(" ")))
        })
    }
}
