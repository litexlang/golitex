//! Formula-only display layout; conversion never executes or instantiates ASTs.
use super::fact::{conclusions, fact, parameters};
use super::obj::obj;
use crate::module_manager::GlobalModuleManager;
use crate::prelude::*;

pub(crate) fn predicate_to_display_latex(
    name: &str,
    parameters: &crate::ast::param::TypedParameterList,
) -> String {
    let args = parameters
        .groups
        .iter()
        .flat_map(|group| {
            group
                .params
                .iter()
                .map(|param| super::helper::ident(&param.name))
        })
        .collect::<Vec<_>>();
    super::helper::predicate_or_fn_call(&super::helper::ident(name), &args.join(", "))
}

pub(crate) fn fact_to_display_latex(
    value: &Fact,
    modules: &GlobalModuleManager,
    language: OutputLanguage,
) -> RuntimeResult<String> {
    match value {
        Fact::AtomicFact(atomic) => {
            comparison(atomic, modules, language).unwrap_or_else(|| fact(value, modules, language))
        }
        Fact::ForallFact(universal) if universal.dom_facts.is_empty() => {
            let body = match universal.then_facts.as_slice() {
                [crate::ast::fact::ExistOrAndChainAtomicFact::AtomicFact(atomic)] => {
                    comparison(atomic, modules, language)
                        .unwrap_or_else(|| conclusions(&universal.then_facts, modules, language))?
                }
                _ => conclusions(&universal.then_facts, modules, language)?,
            };
            let binders = parameters(&universal.typed_parameters, modules, language)?;
            if binders.is_empty() {
                return Ok(body);
            }
            Ok(format!(
                r"\begin{{gathered}}\forall {binders}:\\[0.6em]{body}\end{{gathered}}"
            ))
        }
        // Guarded/nested logical structures retain the canonical compiler's
        // grouping rather than being split by rendered-string heuristics.
        _ => fact(value, modules, language),
    }
}

fn comparison(
    value: &AtomicFact,
    modules: &GlobalModuleManager,
    language: OutputLanguage,
) -> Option<RuntimeResult<String>> {
    let relation = match value {
        AtomicFact::EqualFact(_) => "=",
        AtomicFact::NotEqualFact(_) => r"\ne",
        AtomicFact::LessFact(_) => "<",
        AtomicFact::GreaterFact(_) => ">",
        AtomicFact::LessEqualFact(_) => r"\leq",
        AtomicFact::GreaterEqualFact(_) => r"\geq",
        _ => return None,
    };
    let args = crate::ast::fact::atomic_fact_args_ref(value);
    Some((|| {
        let left = obj(args[0], modules, language)?;
        let right = obj(args[1], modules, language)?;
        Ok(format!(
            r"\begin{{aligned}}&{left}\\&{relation}\ {right}\end{{aligned}}"
        ))
    })())
}
