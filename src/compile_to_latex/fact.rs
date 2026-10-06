use super::helper::{ident, name, operator, parens};
use super::language::{phrase, Phrase};
use super::obj::obj;
use crate::ast::fact::*;
use crate::ast::param::{ParamType, TypedParameterList};
use crate::launch_command::OutputLanguage;
use crate::module_manager::GlobalModuleManager;
use crate::runtime::{RuntimeError, RuntimeResult};

pub(super) fn fact(
    value: &Fact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    match value {
        Fact::AtomicFact(x) => atomic(x, modules, lang),
        Fact::AndFact(x) => conjunction(&x.facts, modules, lang),
        Fact::OrFact(x) => disjunction(x, modules, lang),
        Fact::ChainFact(x) => chain(x, modules, lang),
        Fact::ExistFact(x) => existential(x, r"\exists", modules, lang),
        Fact::ExistUniqueFact(x) => existential(x, r"\exists!", modules, lang),
        Fact::NotExistFact(x) => existential(x, r"\nexists", modules, lang),
        Fact::ForallFact(x) => forall(x, modules, lang),
        Fact::ForallFactWithIff(x) => {
            let left = conclusions(&x.forall_fact.then_facts, modules, lang)?;
            let right = conclusions(&x.iff_facts, modules, lang)?;
            let body = format!(r"{}\Longleftrightarrow{}", parens(&left), parens(&right));
            let dom = facts(&x.forall_fact.dom_facts, modules, lang)?;
            quantify(
                &parameters(&x.forall_fact.typed_parameters, modules, lang)?,
                &implication(&dom, &body),
            )
        }
        Fact::NotForall(x) => {
            let dom = quantifier_frees(&x.dom_facts, modules, lang)?;
            let then = quantifier_frees(&x.then_facts, modules, lang)?;
            Ok(format!(
                r"\neg\left({}\right)",
                quantify(
                    &parameters(&x.typed_parameters, modules, lang)?,
                    &implication(&dom, &then)
                )?
            ))
        }
    }
}

pub(super) fn atomic(
    value: &AtomicFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    if matches!(
        value,
        AtomicFact::IsCartFact(_)
            | AtomicFact::IsTupleFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
    ) {
        return Err(RuntimeError::Unsupported(
            "LaTeX: retired cart/tuple shape predicate AST".into(),
        ));
    }
    let mut args = Vec::new();
    for arg in atomic_fact_args_ref(value) {
        args.push(obj(arg, modules, lang)?);
    }
    let positive = atomic_fact_has_positive_polarity(value);
    let relation = match value {
        AtomicFact::EqualFact(_) => Some("="),
        AtomicFact::NotEqualFact(_) => Some(r"\ne"),
        AtomicFact::LessFact(_) => Some("<"),
        AtomicFact::GreaterFact(_) => Some(">"),
        AtomicFact::LessEqualFact(_) => Some(r"\leq"),
        AtomicFact::GreaterEqualFact(_) => Some(r"\geq"),
        AtomicFact::InFact(_) => Some(r"\in"),
        AtomicFact::NotInFact(_) => Some(r"\notin"),
        AtomicFact::SubsetFact(_) => Some(r"\subseteq"),
        AtomicFact::SupersetFact(_) => Some(r"\supseteq"),
        AtomicFact::ProperSubsetFact(_) => Some(r"\subsetneq"),
        AtomicFact::ProperSupersetFact(_) => Some(r"\supsetneq"),
        AtomicFact::DvdFact(_) => Some(r"\mid"),
        AtomicFact::NotDvdFact(_) => Some(r"\nmid"),
        _ => None,
    };
    if let Some(rel) = relation {
        return Ok(format!("{} {rel} {}", args[0], args[1]));
    }
    let pred = value.prop_name();
    let body = match value {
        AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_) => {
            format!("{}{}", name(&pred, modules)?, parens(&args.join(", ")))
        }
        AtomicFact::NotLessFact(_) => format!("{} < {}", args[0], args[1]),
        AtomicFact::NotGreaterFact(_) => format!("{} > {}", args[0], args[1]),
        AtomicFact::NotLessEqualFact(_) => format!(r"{} \leq {}", args[0], args[1]),
        AtomicFact::NotGreaterEqualFact(_) => format!(r"{} \geq {}", args[0], args[1]),
        AtomicFact::NotSubsetFact(_) => format!(r"{} \subseteq {}", args[0], args[1]),
        AtomicFact::NotSupersetFact(_) => format!(r"{} \supseteq {}", args[0], args[1]),
        AtomicFact::NotProperSubsetFact(_) => format!(r"{} \subsetneq {}", args[0], args[1]),
        AtomicFact::NotProperSupersetFact(_) => format!(r"{} \supsetneq {}", args[0], args[1]),
        _ => operator(pred.local_name(), &args),
    };
    Ok(if positive {
        body
    } else {
        format!(r"\neg {}", parens(&body))
    })
}

pub(super) fn parameters(
    value: &TypedParameterList,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut groups = Vec::new();
    for group in &value.groups {
        let names = group
            .params
            .iter()
            .map(|p| ident(&p.name))
            .collect::<Vec<_>>()
            .join(", ");
        groups.push(match &group.param_type {
            ParamType::Obj(x) => format!(r"{names}\in {}", obj(x, modules, lang)?),
            ParamType::Set(_) => format!(r"{names}:\text{{{}}}", phrase(lang, Phrase::Set)),
            ParamType::NonemptySet(_) => {
                format!(r"{names}:\text{{{}}}", phrase(lang, Phrase::NonemptySet))
            }
            ParamType::FiniteSet(_) => {
                format!(r"{names}:\text{{{}}}", phrase(lang, Phrase::FiniteSet))
            }
        });
    }
    Ok(groups.join(r";\ "))
}
pub(super) fn facts(
    value: &[Fact],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut items = Vec::new();
    for f in value {
        items.push(parens(&fact(f, modules, lang)?));
    }
    Ok(items.join(r" \land "))
}
pub(super) fn forall(
    value: &ForallFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let body = implication(
        &facts(&value.dom_facts, modules, lang)?,
        &conclusions(&value.then_facts, modules, lang)?,
    );
    quantify(&parameters(&value.typed_parameters, modules, lang)?, &body)
}
pub(super) fn conclusions(
    value: &[ExistOrAndChainAtomicFact],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut items = Vec::new();
    for f in value {
        items.push(parens(&conclusion(f, modules, lang)?));
    }
    Ok(items.join(r" \land "))
}
fn conclusion(
    value: &ExistOrAndChainAtomicFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    match value {
        ExistOrAndChainAtomicFact::AtomicFact(x) => atomic(x, modules, lang),
        ExistOrAndChainAtomicFact::AndFact(x) => conjunction(&x.facts, modules, lang),
        ExistOrAndChainAtomicFact::ChainFact(x) => chain(x, modules, lang),
        ExistOrAndChainAtomicFact::OrFact(x) => disjunction(x, modules, lang),
        ExistOrAndChainAtomicFact::ExistFact(x) => existential(x, r"\exists", modules, lang),
        ExistOrAndChainAtomicFact::ExistUniqueFact(x) => existential(x, r"\exists!", modules, lang),
        ExistOrAndChainAtomicFact::NotExistFact(x) => existential(x, r"\nexists", modules, lang),
    }
}
pub(super) fn exist_shaped(
    value: &ExistShapedFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let quantifier = match value {
        ExistShapedFact::Exist(_) => r"\exists",
        ExistShapedFact::ExistUnique(_) => r"\exists!",
        ExistShapedFact::NotExist(_) => r"\nexists",
    };
    existential(value.plain(), quantifier, modules, lang)
}
fn existential(
    value: &PlainExistFact,
    quantifier: &str,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    Ok(format!(
        r"{quantifier} {}:\ {}",
        parameters(&value.typed_parameters, modules, lang)?,
        parens(&quantifier_frees(&value.facts, modules, lang)?)
    ))
}
pub(super) fn quantifier_frees(
    value: &[QuantifierFreeFact],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut items = Vec::new();
    for f in value {
        items.push(parens(&quantifier_free(f, modules, lang)?));
    }
    Ok(items.join(r" \land "))
}
pub(super) fn quantifier_free(
    value: &QuantifierFreeFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    match value {
        QuantifierFreeFact::AtomicFact(x) => atomic(x, modules, lang),
        QuantifierFreeFact::AndFact(x) => conjunction(&x.facts, modules, lang),
        QuantifierFreeFact::ChainFact(x) => chain(x, modules, lang),
        QuantifierFreeFact::OrFact(x) => disjunction(x, modules, lang),
    }
}
pub(super) fn and_chain(
    value: &AndChainAtomicFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    match value {
        AndChainAtomicFact::AtomicFact(x) => atomic(x, modules, lang),
        AndChainAtomicFact::AndFact(x) => conjunction(&x.facts, modules, lang),
        AndChainAtomicFact::ChainFact(x) => chain(x, modules, lang),
    }
}
fn conjunction(
    value: &[AtomicFact],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut items = Vec::new();
    for f in value {
        items.push(parens(&atomic(f, modules, lang)?));
    }
    Ok(items.join(r" \land "))
}
fn disjunction(
    value: &OrFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut items = Vec::new();
    for f in &value.facts {
        items.push(parens(&and_chain(f, modules, lang)?));
    }
    Ok(items.join(r" \lor "))
}
fn chain(
    value: &ChainFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    if value.prop_names.is_empty() || value.objs.len() != value.prop_names.len() + 1 {
        return Err(RuntimeError::Unsupported(
            "LaTeX: malformed chain AST".into(),
        ));
    }
    let mut items = Vec::new();
    let mut joined = obj(&value.objs[0], modules, lang)?;
    let mut can_chain = true;
    for (i, prop) in value.prop_names.iter().enumerate() {
        let left = obj(&value.objs[i], modules, lang)?;
        let right = obj(&value.objs[i + 1], modules, lang)?;
        let symbol = match prop {
            crate::ast::names::AtomicName::Plain { name } => match name.as_str() {
                "=" => Some("="),
                "!=" => Some(r"\ne"),
                "<" => Some("<"),
                ">" => Some(">"),
                "<=" => Some(r"\leq"),
                ">=" => Some(r"\geq"),
                "in" => Some(r"\in"),
                "subset" => Some(r"\subseteq"),
                "superset" => Some(r"\supseteq"),
                "proper_subset" => Some(r"\subsetneq"),
                "proper_superset" => Some(r"\supsetneq"),
                _ => None,
            },
            _ => None,
        };
        if let Some(s) = symbol {
            joined.push_str(&format!(" {s} {right}"));
        } else {
            can_chain = false;
        }
        items.push(if let Some(s) = symbol {
            format!("{left} {s} {right}")
        } else {
            format!(
                "{}{}",
                name(prop, modules)?,
                parens(&format!("{left}, {right}"))
            )
        });
    }
    if can_chain {
        return Ok(joined);
    }
    Ok(items
        .into_iter()
        .map(|x| parens(&x))
        .collect::<Vec<_>>()
        .join(r" \land "))
}
fn implication(dom: &str, then: &str) -> String {
    if dom.is_empty() {
        then.into()
    } else {
        format!(r"{}\Rightarrow{}", parens(dom), parens(then))
    }
}

fn quantify(params: &str, body: &str) -> RuntimeResult<String> {
    Ok(if params.is_empty() {
        body.into()
    } else {
        format!(r"\forall {params}:\ {body}")
    })
}
