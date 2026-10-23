//! Read-only mathematical display data. No new facts or runtime IDs are made.
use super::*;
use crate::ast::param::{ParamType, TypedParameterList};
use crate::ast::stmt::{ByStmt, DefineObjStmt, DefinitionStmt, ProofBlockStmt};
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferNormalAtomicFactResult, InferResult,
};

fn parameters(list: &TypedParameterList) -> JsonValue {
    JsonValue::Array(
        list.groups
            .iter()
            .map(|group| {
                let (kind, domain) = match &group.param_type {
                    ParamType::Obj(domain) => ("element", text(&domain.readable_string())),
                    ParamType::Set(_) => ("set", JsonValue::Null),
                    ParamType::NonemptySet(_) => ("nonempty_set", JsonValue::Null),
                    ParamType::FiniteSet(_) => ("finite_set", JsonValue::Null),
                };
                object(vec![
                    (
                        "names",
                        strings(
                            &group
                                .params
                                .iter()
                                .map(|param| param.name.clone())
                                .collect::<Vec<_>>(),
                        ),
                    ),
                    ("kind", text(kind)),
                    ("domain", domain),
                ])
            })
            .collect(),
    )
}

fn subject(fact: &Fact) -> JsonValue {
    object(vec![
        ("kind", text("fact")),
        ("subject", text(&fact.readable_string())),
        ("subject_fact_id", text(&fact.fact_id().to_string())),
    ])
}

pub(super) fn statement_math(
    statement: &Stmt,
    runtime: &Runtime,
    language: OutputLanguage,
) -> JsonValue {
    match statement {
        Stmt::Definition(DefinitionStmt::DefPropStmt(definition)) => {
            let names = definition
                .typed_parameters
                .groups
                .iter()
                .flat_map(|group| group.params.iter().map(|param| param.name.clone()))
                .collect::<Vec<_>>();
            object(vec![
                ("kind", text("predicate_definition")),
                (
                    "subject",
                    text(&format!("${}({})", definition.name, names.join(", "))),
                ),
                ("parameters", parameters(&definition.typed_parameters)),
                (
                    "latex",
                    definition_latex(
                        &definition.name,
                        &definition.typed_parameters,
                        &definition.iff_facts,
                        runtime,
                        language,
                    ),
                ),
                (
                    "facts",
                    strings(
                        &definition
                            .iff_facts
                            .iter()
                            .map(|value| value.readable_string())
                            .collect::<Vec<_>>(),
                    ),
                ),
            ])
        }
        Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(definition)) => object(vec![
            ("kind", text("abstract_predicate")),
            (
                "subject",
                text(&format!(
                    "${}({})",
                    definition.name,
                    definition.params.join(", ")
                )),
            ),
        ]),
        Stmt::Definition(DefinitionStmt::DefineObj(definition)) => match definition {
            DefineObjStmt::HaveObjInNonemptySetStmt(value) => object(vec![
                ("kind", text("objects")),
                ("parameters", parameters(&value.param_def)),
            ]),
            DefineObjStmt::HaveObjEqualStmt(value) => object(vec![
                ("kind", text("objects")),
                ("parameters", parameters(&value.param_def)),
                (
                    "values",
                    strings(
                        &value
                            .objs_equal_to
                            .iter()
                            .map(|value| value.readable_string())
                            .collect::<Vec<_>>(),
                    ),
                ),
            ]),
            DefineObjStmt::HaveObjByExistFactsStmt(value) => object(vec![
                ("kind", text("objects")),
                ("parameters", parameters(&value.param_def)),
                (
                    "facts",
                    strings(
                        &value
                            .facts
                            .iter()
                            .map(|value| {
                                crate::instantiate::quantifier_free_fact_to_fact(value.clone())
                                    .readable_string()
                            })
                            .collect::<Vec<_>>(),
                    ),
                ),
            ]),
            DefineObjStmt::LetObjStmt(value) => object(vec![
                ("kind", text("binding")),
                ("name", text(&value.name.name)),
                ("value", text(&value.value.readable_string())),
            ]),
            _ => JsonValue::Null,
        },
        Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(value)) => {
            let function = &value.equal_to_anonymous_fn;
            let names = function
                .body
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|group| group.params.iter().map(|param| param.name.clone()))
                .collect::<Vec<_>>();
            let params = function
                .body
                .set_bound_parameters
                .groups
                .iter()
                .map(|group| {
                    object(vec![
                        (
                            "names",
                            strings(
                                &group
                                    .params
                                    .iter()
                                    .map(|param| param.name.clone())
                                    .collect::<Vec<_>>(),
                            ),
                        ),
                        ("kind", text("element")),
                        ("domain", text(&group.param_type.readable_string())),
                    ])
                })
                .collect();
            object(vec![
                ("kind", text("function")),
                ("parameters", JsonValue::Array(params)),
                (
                    "domain_facts",
                    strings(
                        &function
                            .body
                            .dom_facts
                            .iter()
                            .map(|value| {
                                crate::instantiate::quantifier_free_fact_to_fact(value.clone())
                                    .readable_string()
                            })
                            .collect::<Vec<_>>(),
                    ),
                ),
                ("codomain", text(&function.body.ret_set.readable_string())),
                (
                    "subject",
                    text(&format!(
                        "{}({}) = {}",
                        value.name.name,
                        names.join(", "),
                        function.equal_to.readable_string()
                    )),
                ),
            ])
        }
        Stmt::Fact(fact) => subject(fact),
        Stmt::Definition(DefinitionStmt::DefThmStmt(value)) => subject(&value.fact),
        Stmt::Definition(DefinitionStmt::AxiomStmt(value)) => {
            subject(&Fact::ForallFact(value.forall_fact.clone()))
        }
        Stmt::Definition(DefinitionStmt::DefStrategyStmt(value)) => {
            subject(&Fact::ForallFact(value.forall_fact.clone()))
        }
        Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(value)) => subject(&value.fact),
        Stmt::By(ByStmt::ByDefStmt(value)) => subject(&Fact::AtomicFact(value.fact.clone())),
        Stmt::By(ByStmt::ByThmStmt(value)) => {
            subject(&Fact::AtomicFact(value.selected_fact.clone()))
        }
        Stmt::By(ByStmt::ByContraStmt(value)) => subject(&value.to_prove),
        Stmt::By(ByStmt::ByCasesStmt(value)) => object(vec![
            ("kind", text("facts")),
            (
                "facts",
                strings(
                    &value
                        .then_facts
                        .iter()
                        .map(|value| value.readable_string())
                        .collect::<Vec<_>>(),
                ),
            ),
        ]),
        _ => JsonValue::Null,
    }
}

fn stored_fact(store: &StoreFactResult) -> Fact {
    match store {
        StoreFactResult::AtomicFact(value) => Fact::AtomicFact(value.fact.clone()),
        StoreFactResult::AndFact(value) => Fact::AndFact(value.fact.clone()),
        StoreFactResult::ChainFact(value) => Fact::ChainFact(value.fact.clone()),
        StoreFactResult::OrFact(value) => Fact::OrFact(value.fact.clone()),
        StoreFactResult::ExistShapedFact(value) => match &value.fact {
            crate::ast::fact::ExistShapedFact::Exist(fact) => Fact::ExistFact(fact.clone()),
            crate::ast::fact::ExistShapedFact::ExistUnique(fact) => {
                Fact::ExistUniqueFact(fact.clone())
            }
            crate::ast::fact::ExistShapedFact::NotExist(fact) => Fact::NotExistFact(fact.clone()),
        },
        StoreFactResult::NotForallFact(value) => Fact::NotForall(value.fact.clone()),
        StoreFactResult::ForallFact(value) => Fact::ForallFact(value.fact.clone()),
        StoreFactResult::ForallFactWithIff(value) => Fact::ForallFactWithIff(value.fact.clone()),
    }
}

fn parameter_meaning(store: &StoreFactResult) -> JsonValue {
    let fact = stored_fact(store);
    let (argument, kind, domain) = match &fact {
        Fact::AtomicFact(AtomicFact::InFact(value)) => (
            &value.element,
            "element",
            text(&value.set.readable_string()),
        ),
        Fact::AtomicFact(AtomicFact::IsSetFact(value)) => (&value.set, "set", JsonValue::Null),
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(value)) => {
            (&value.set, "nonempty_set", JsonValue::Null)
        }
        Fact::AtomicFact(AtomicFact::IsFiniteSetFact(value)) => {
            (&value.set, "finite_set", JsonValue::Null)
        }
        _ => return text(&fact.readable_string()),
    };
    object(vec![
        ("names", strings(&[argument.readable_string()])),
        ("kind", text(kind)),
        ("domain", domain),
    ])
}

/// Preserve each complete instantiated iff clause, including conjunctions
/// stored as several components. Published output filtering is not an iff.
pub(super) fn inference_math(
    result: &StoreFactAndInferResult,
    runtime: &Runtime,
    language: OutputLanguage,
) -> JsonValue {
    let StoreFactResult::AtomicFact(seed) = &result.store else {
        return JsonValue::Null;
    };
    let AtomicFact::NormalAtomicFact(normal) = &seed.fact else {
        return JsonValue::Null;
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(steps))) =
        &result.infer
    else {
        return JsonValue::Null;
    };
    let mut parameters = Vec::new();
    let mut clauses = None;
    for step in steps {
        match step {
            InferNormalAtomicFactResult::ParamTypes(value) => {
                parameters.extend(value.derived.iter())
            }
            InferNormalAtomicFactResult::ExpandDefinition(value) => clauses = Some(&value.derived),
        }
    }
    let Some(clauses) = clauses.filter(|clauses| !clauses.is_empty()) else {
        return JsonValue::Null;
    };
    // Instantiation can omit an unsupported clause. Only claim an iff when
    // every original clause is present; reading never fills in missing proofs.
    let Some(definition) = runtime.def_prop_visible(&normal.predicate) else {
        return JsonValue::Null;
    };
    if parameters.len() != normal.body.len() || clauses.len() != definition.iff_facts.len() {
        return JsonValue::Null;
    }
    object(vec![
        ("kind", text("predicate_equivalence")),
        (
            "latex",
            inference_latex(
                &stored_fact(&result.store),
                &parameters,
                clauses,
                runtime,
                language,
            ),
        ),
        ("subject", text(&seed.fact.readable_string())),
        ("subject_fact_id", text(&seed.fact_id.to_string())),
        (
            "parameters",
            JsonValue::Array(
                parameters
                    .iter()
                    .map(|value| parameter_meaning(&value.store))
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            "parameter_fact_ids",
            strings(
                &parameters
                    .iter()
                    .map(|value| value.primary_fact_id().to_string())
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            "facts",
            strings(
                &clauses
                    .iter()
                    .map(|value| stored_fact(&value.store).readable_string())
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            "fact_ids",
            strings(
                &clauses
                    .iter()
                    .map(|value| value.primary_fact_id().to_string())
                    .collect::<Vec<_>>(),
            ),
        ),
    ])
}

fn definition_latex(
    name: &str,
    parameters: &TypedParameterList,
    facts: &[Fact],
    runtime: &Runtime,
    language: OutputLanguage,
) -> JsonValue {
    use crate::compile_to_latex::{fact_to_display_latex, parameters_to_latex};
    let mut domains = Vec::new();
    for group in &parameters.groups {
        // Split groups without changing binder identity or dependent domains.
        for param in &group.params {
            let mut single = parameters.clone();
            single.groups = vec![group.clone()];
            single.groups[0].params = vec![param.clone()];
            let Ok(domain) = parameters_to_latex(&single, &runtime.global_module_manager, language)
            else {
                return JsonValue::Null;
            };
            domains.push(domain);
        }
    }
    let clauses = facts
        .iter()
        .map(|fact| fact_to_display_latex(fact, &runtime.global_module_manager, language))
        .collect::<RuntimeResult<Vec<_>>>();
    match clauses {
        Ok(clauses) => object(vec![
            (
                "subject",
                text(&crate::compile_to_latex::predicate_to_display_latex(
                    name, parameters,
                )),
            ),
            ("parameters", strings(&domains)),
            ("facts", strings(&clauses)),
        ]),
        Err(_) => JsonValue::Null,
    }
}

fn inference_latex(
    subject: &Fact,
    parameters: &[&crate::store_fact_and_infer::StoreInferredFactResult],
    clauses: &[crate::store_fact_and_infer::StoreInferredFactResult],
    runtime: &Runtime,
    language: OutputLanguage,
) -> JsonValue {
    use crate::compile_to_latex::fact_to_display_latex;
    let render = |values: &[&crate::store_fact_and_infer::StoreInferredFactResult]| {
        values
            .iter()
            .map(|value| {
                fact_to_display_latex(
                    &stored_fact(&value.store),
                    &runtime.global_module_manager,
                    language,
                )
            })
            .collect::<RuntimeResult<Vec<_>>>()
    };
    let domains = render(parameters);
    let facts = render(&clauses.iter().collect::<Vec<_>>());
    let subject = fact_to_display_latex(subject, &runtime.global_module_manager, language);
    match (subject, domains, facts) {
        (Ok(subject), Ok(domains), Ok(facts)) => object(vec![
            ("subject", text(&subject)),
            ("parameters", strings(&domains)),
            ("facts", strings(&facts)),
        ]),
        _ => JsonValue::Null,
    }
}
