//! Anonymous-function occurrence aliases for fact results.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// A frozen proof/check Result may repeat an alpha-equivalent anonymous
    /// function under a fresh parser occurrence. Rebind that occurrence only
    /// when the active WD certificate has exactly one semantic owner. This is
    /// the fact-level analogue of witness aliasing and is deliberately scoped
    /// to the current compiler environment.
    pub(in super::super) fn install_fact_anonymous_function_occurrence_aliases(
        &mut self,
        fact: &Fact,
        result_layer: &str,
    ) -> Result<(), String> {
        fn collect_from_object(
            object: &Obj,
            functions: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            if let Obj::AnonymousFn(function) = object {
                if let Some(occurrence_id) = function.source_occurrence_id {
                    functions.push((occurrence_id, obj_equality_key(object)));
                }
            }
            // Function-application traversal treats the callable head as a
            // different structural field from ordinary arguments. Visit it
            // explicitly so an applied anonymous literal is not skipped.
            if let Obj::FnObj(application) = object {
                let head: Obj = application.head.as_ref().clone().into();
                collect_from_object(&head, functions);
            }
            let _: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
                object,
                object,
                &mut |child, _| {
                    collect_from_object(child, functions);
                    Ok(true)
                },
            );
        }

        fn collect_from_forall(
            forall: &ForallFact,
            functions: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            for group in &forall.typed_parameters.groups {
                if let ParamType::Obj(carrier) = &group.param_type {
                    collect_from_object(carrier, functions);
                }
            }
            for premise in &forall.dom_facts {
                collect_from_fact(premise, functions);
            }
            for conclusion in &forall.then_facts {
                collect_from_fact(&conclusion.clone().to_fact(), functions);
            }
        }

        fn collect_from_fact(fact: &Fact, functions: &mut Vec<(SourceObjectOccurrenceId, String)>) {
            let arguments = match fact {
                Fact::AtomicFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ExistFact(fact) => fact.get_args_from_fact_ref(),
                Fact::OrFact(fact) => fact.get_args_from_fact_ref(),
                Fact::AndFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ChainFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ForallFact(forall) => {
                    collect_from_forall(forall, functions);
                    return;
                }
                Fact::ForallFactWithIff(forall) => {
                    collect_from_forall(&forall.forall_fact, functions);
                    for conclusion in &forall.iff_facts {
                        collect_from_fact(&conclusion.clone().to_fact(), functions);
                    }
                    return;
                }
                Fact::NotForall(forall) => {
                    collect_from_forall(&forall.forall_fact, functions);
                    return;
                }
            };
            for argument in arguments {
                collect_from_object(argument, functions);
            }
        }

        let mut functions = Vec::new();
        collect_from_fact(fact, &mut functions);
        functions.sort_by_key(|(occurrence_id, _)| occurrence_id.value());
        functions.dedup_by_key(|(occurrence_id, _)| occurrence_id.value());
        if functions.is_empty() {
            return Ok(());
        }
        let context = self
            .environment_stack
            .well_definedness
            .as_mut()
            .ok_or_else(|| format!("{result_layer} has no active WD Result"))?;
        for (source_occurrence, semantic_key) in functions {
            if context.anonymous_functions.contains_key(&source_occurrence) {
                continue;
            }
            let owners = context
                .anonymous_functions
                .iter()
                .filter_map(|(owner_occurrence, certificate)| {
                    (obj_equality_key(&certificate.source_function) == semantic_key)
                        .then_some(*owner_occurrence)
                })
                .collect::<Vec<_>>();
            let [owner_occurrence] = owners.as_slice() else {
                return Err(format!(
                    "{result_layer} anonymous function occurrence {} has {} alpha-equivalent WD owners",
                    source_occurrence.value(),
                    owners.len()
                ));
            };
            if let Some(previous) = context
                .anonymous_function_occurrence_aliases
                .insert(source_occurrence, *owner_occurrence)
            {
                if previous != *owner_occurrence {
                    return Err(format!(
                        "{result_layer} anonymous function occurrence {} changed its WD owner",
                        source_occurrence.value()
                    ));
                }
            }
        }
        Ok(())
    }
}
