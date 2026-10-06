use super::fact::{
    and_chain, atomic, conclusions, exist_shaped, fact, facts, forall, parameters, quantifier_frees,
};
use super::helper::{display, escape_text, ident, identifier, inline, name, parens};
use super::language::{phrase, sentence, Phrase};
use super::obj::{fn_set, function_space, obj};
use crate::ast::fact::{Fact, ForallFact};
use crate::ast::names::BoundName;
use crate::ast::stmt::*;
use crate::launch_command::OutputLanguage;
use crate::module_manager::GlobalModuleManager;
use crate::runtime::{RuntimeError, RuntimeResult};

pub(super) fn statements(
    values: &[Stmt],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut out = String::new();
    for value in values {
        out.push_str(&statement(value, modules, lang)?);
        out.push('\n');
    }
    Ok(out)
}

fn statement(
    value: &Stmt,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let o = |x| obj(x, modules, lang);
    let f = |x| fact(x, modules, lang);
    let say = |key, a: &str, b: &str, c: &str| paragraph(&sentence(lang, key, a, b, c));
    Ok(match value {
        Stmt::Fact(x) => fact_paragraph(x, modules, lang)?,
        Stmt::Trust(x) => match x {
            TrustBoundaryStmt::TrustStmt(x) => format!(
                "{}{}",
                heading(Phrase::Trusted, "", lang),
                say(
                    Phrase::Suppose,
                    &inline(&facts(&x.facts, modules, lang)?),
                    "",
                    ""
                )
            ),
            TrustBoundaryStmt::TrustHaveStmt(x) => format!(
                "{}{}",
                heading(Phrase::Trusted, "", lang),
                say(
                    Phrase::Given,
                    &inline(&parameters(&x.param_def, modules, lang)?),
                    &inline(&facts(&x.facts, modules, lang)?),
                    ""
                )
            ),
        },
        Stmt::Definition(x) => definition(x, modules, lang)?,
        Stmt::By(x) => match x {
            ByStmt::ByThmStmt(x) => say(
                Phrase::ByTheorem,
                &inline(&theorem_call(&x.call, modules, lang)?),
                &inline(&atomic(&x.selected_fact, modules, lang)?),
                "",
            ),
            ByStmt::ByDefStmt(x) => say(
                Phrase::Unfold,
                &inline(&atomic(&x.fact, modules, lang)?),
                "",
                "",
            ),
            ByStmt::ByContraStmt(x) => format!(
                "{}{}{}{}{}",
                say(Phrase::Goal, &inline(&f(&x.to_prove)?), "", ""),
                say(Phrase::ContradictionMethod, "", "", ""),
                say(
                    Phrase::Suppose,
                    &inline(&format!(r"\neg {}", parens(&f(&x.to_prove)?))),
                    "",
                    ""
                ),
                proof(&x.proof, modules, lang)?,
                say(
                    Phrase::Contradiction,
                    &inline(&f(&x.impossible_fact)?),
                    "",
                    ""
                )
            ),
            ByStmt::ByCasesStmt(x) => {
                if x.cases.len() != x.proofs.len() || x.cases.len() != x.impossible_facts.len() {
                    return Err(RuntimeError::Unsupported(
                        "LaTeX: inconsistent case/proof counts".into(),
                    ));
                }
                let mut out = say(
                    Phrase::Goal,
                    &inline(&facts(&x.then_facts, modules, lang)?),
                    "",
                    "",
                );
                out.push_str(&say(Phrase::Cases, "", "", ""));
                for (i, case) in x.cases.iter().enumerate() {
                    out.push_str(&heading(Phrase::Case, &(i + 1).to_string(), lang));
                    out.push_str(&say(
                        Phrase::Suppose,
                        &inline(&and_chain(case, modules, lang)?),
                        "",
                        "",
                    ));
                    out.push_str(&proof(&x.proofs[i], modules, lang)?);
                    if let Some(impossible) = &x.impossible_facts[i] {
                        out.push_str(&say(
                            Phrase::Contradiction,
                            &inline(&atomic(impossible, modules, lang)?),
                            "",
                            "",
                        ));
                    }
                }
                out
            }
            ByStmt::ByInducStmt(x) => induction(
                Phrase::Induction,
                &x.param_binding,
                &x.induc_from,
                &x.to_prove,
                &x.proof,
                &x.base_proof,
                &x.step_proof,
                modules,
                lang,
            )?,
            ByStmt::ByStrongInducStmt(x) => induction(
                Phrase::StrongInduction,
                &x.param_binding,
                &x.induc_from,
                &x.to_prove,
                &x.proof,
                &x.base_proof,
                &x.step_proof,
                modules,
                lang,
            )?,
            ByStmt::ByEnumerateFiniteSetStmt(x) => format!(
                "{}{}",
                say(
                    Phrase::Enumerate,
                    &inline(&forall(&x.forall_fact, modules, lang)?),
                    "",
                    ""
                ),
                proof(&x.proof, modules, lang)?
            ),
            ByStmt::ByForStmt(x) => format!(
                "{}{}",
                say(
                    Phrase::Iterate,
                    &inline(&forall(&x.forall_fact, modules, lang)?),
                    "",
                    ""
                ),
                proof(&x.proof, modules, lang)?
            ),
            ByStmt::ByExtensionStmt(x) => format!(
                "{}{}",
                say(
                    Phrase::Extension,
                    &inline(&format!("{} = {}", o(&x.left)?, o(&x.right)?)),
                    "",
                    ""
                ),
                proof(&x.proof, modules, lang)?
            ),
            ByStmt::ByFnExtensionStmt(x) => format!(
                "{}{}",
                say(
                    Phrase::FnExtension,
                    &inline(&format!("{} = {}", o(&x.left)?, o(&x.right)?)),
                    "",
                    ""
                ),
                proof(&x.proof, modules, lang)?
            ),
        },
        Stmt::ReleaseAndExpand(x) => match x {
            ReleaseAndExpandStmt::ReleaseThmStmt(x) => say(
                Phrase::ApplyTheorem,
                &inline(&theorem_call(&x.call, modules, lang)?),
                "",
                "",
            ),
            ReleaseAndExpandStmt::ReleaseStructDefStmt(x) => {
                say(Phrase::ReleaseStruct, &inline(&o(&x.obj)?), "", "")
            }
            ReleaseAndExpandStmt::ReleaseObjDefStmt(x) => say(
                Phrase::ReleaseObj,
                &inline(&identifier(&x.name, modules)?),
                "",
                "",
            ),
            ReleaseAndExpandStmt::ReleaseCartDefStmt(x) => say(Phrase::ReleaseObj, &inline(&o(&crate::ast::obj::Obj::ProductShape(crate::ast::obj::ProductShape::Cart(x.cart.clone())))?), "", ""),
            ReleaseAndExpandStmt::ExpandRangeStmt(x) => {
                let (start, end, relation) = match &x.range {
                    ClosedRangeOrRange::ClosedRange(x) => (o(&x.start)?, o(&x.end)?, r"\leq"),
                    ClosedRangeOrRange::Range(x) => (o(&x.start)?, o(&x.end)?, "<"),
                };
                let range = format!(
                    r"\left\{{\iota\in\mathbb{{Z}}\;\middle|\;{start}\leq\iota {relation} {end}\right\}}"
                );
                say(
                    Phrase::ExpandRange,
                    &inline(&format!(r"{}\in {range}", o(&x.element)?)),
                    "",
                    "",
                )
            }
            ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(x) => format!(
                "{}{}",
                say(Phrase::Choice, &inline(&o(&x.family)?), "", ""),
                proof(&x.proof, modules, lang)?
            ),
            ReleaseAndExpandStmt::ReleaseRegularityAxiomStmt(x) => {
                say(Phrase::Regularity, &inline(&o(&x.set)?), "", "")
            }
            ReleaseAndExpandStmt::ReleaseZornLemmaStmt(x) => {
                let names = format!(
                    "{}, {}, {}",
                    name(&x.prop_name, modules)?,
                    name(&x.upper_bound_prop_name, modules)?,
                    name(&x.maximal_prop_name, modules)?
                );
                format!(
                    "{}{}",
                    say(Phrase::Zorn, &inline(&o(&x.set)?), &inline(&names), ""),
                    proof(&x.proof, modules, lang)?
                )
            }
        },
        Stmt::Register(x) => {
            let (key, value) = match x {
                RegisterStmt::RegisterTransitivePropStmt(x) => {
                    (Phrase::RegisterTransitive, &x.forall_fact)
                }
                RegisterStmt::RegisterSymmetricPropStmt(x) => {
                    (Phrase::RegisterSymmetric, &x.forall_fact)
                }
                RegisterStmt::RegisterReflexivePropStmt(x) => {
                    (Phrase::RegisterReflexive, &x.forall_fact)
                }
            };
            say(key, &inline(&forall(value, modules, lang)?), "", "")
        }
        Stmt::Witness(x) => match x {
            WitnessStmt::WitnessExistFact(x) => {
                let mut witnesses = Vec::new();
                for y in &x.equal_tos {
                    witnesses.push(o(y)?);
                }
                format!(
                    "{}{}",
                    say(
                        Phrase::Witness,
                        &inline(&witnesses.join(", ")),
                        &inline(&exist_shaped(
                            &x.exist_shaped_fact_in_witness,
                            modules,
                            lang
                        )?),
                        ""
                    ),
                    proof(&x.proof, modules, lang)?
                )
            }
            WitnessStmt::WitnessAtomicFact(x) => {
                let mut witnesses = Vec::new();
                for y in &x.witnesses {
                    witnesses.push(o(y)?);
                }
                let mut args = Vec::new();
                for y in &x.atomic_fact.body {
                    args.push(o(y)?);
                }
                let goal = format!(
                    "{}{}",
                    name(&x.atomic_fact.predicate, modules)?,
                    parens(&args.join(", "))
                );
                format!(
                    "{}{}",
                    say(
                        Phrase::Witness,
                        &inline(&witnesses.join(", ")),
                        &inline(&goal),
                        ""
                    ),
                    proof(&x.proof, modules, lang)?
                )
            }
            WitnessStmt::WitnessNonemptySet(x) => format!(
                "{}{}",
                say(
                    Phrase::Witness,
                    &inline(&o(&x.obj)?),
                    &inline(&format!(r"{}\ne\varnothing", o(&x.set)?)),
                    ""
                ),
                proof(&x.proof, modules, lang)?
            ),
        },
        Stmt::ProofBlock(x) => match x {
            ProofBlockStmt::ClaimStmt(x) => format!(
                "{}{}{}",
                heading(Phrase::Claim, "", lang),
                fact_paragraph(&x.fact, modules, lang)?,
                proof(&x.proof, modules, lang)?
            ),
            ProofBlockStmt::SketchStmt(x) => format!(
                "{}{}",
                heading(Phrase::Sketch, "", lang),
                quote(&statements(&x.proof, modules, lang)?)
            ),
        },
        Stmt::Command(CommandStmt::EvalStmt(x)) => {
            say(Phrase::Evaluate, &inline(&o(&x.obj_to_eval)?), "", "")
        }
    })
}

fn definition(
    value: &DefinitionStmt,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let say = |key, a: &str, b: &str, c: &str| paragraph(&sentence(lang, key, a, b, c));
    Ok(match value {
        DefinitionStmt::DefineObj(x) => define_obj(x, modules, lang)?,
        DefinitionStmt::HaveFnEqualStmt(x) => {
            let fun = &x.equal_to_anonymous_fn;
            let mut names = Vec::new();
            for g in &fun.body.set_bound_parameters.groups {
                for p in &g.params {
                    names.push(ident(&p.name));
                }
            }
            let equation = format!(
                "{}{} = {}",
                ident(&x.name.name),
                parens(&names.join(", ")),
                obj(&fun.equal_to, modules, lang)?
            );
            format!(
                "{}{}{}",
                heading(Phrase::Definition, &x.name.name, lang),
                say(
                    Phrase::Let,
                    &inline(&format!(
                        "{} : {}",
                        ident(&x.name.name),
                        fn_set(&fun.body, modules, lang)?
                    )),
                    "",
                    ""
                ),
                display(&equation)
            )
        }
        DefinitionStmt::HaveFnEqualCaseByCaseStmt(x) => function_cases(
            &x.name,
            Phrase::Definition,
            &x.fn_set_clause,
            &x.cases,
            &x.equal_tos,
            modules,
            lang,
        )?,
        DefinitionStmt::DefAlgoByCasesStmt(x) => function_cases(
            &x.name,
            Phrase::Algorithm,
            &x.fn_set_clause,
            &x.cases,
            &x.equal_tos,
            modules,
            lang,
        )?,
        DefinitionStmt::HaveFnByInducStmt(x) => function_induction(
            &x.name,
            Phrase::Definition,
            &x.fn_set_clause,
            &x.measure,
            &x.lower_bound,
            &x.cases,
            modules,
            lang,
        )?,
        DefinitionStmt::DefAlgoByInducStmt(x) => function_induction(
            &x.name,
            Phrase::Algorithm,
            &x.fn_set_clause,
            &x.measure,
            &x.lower_bound,
            &x.cases,
            modules,
            lang,
        )?,
        DefinitionStmt::HaveFnByForallExistUniqueStmt(x) => format!(
            "{}{}",
            heading(Phrase::Definition, &x.name.name, lang),
            say(
                Phrase::Define,
                &inline(&ident(&x.name.name)),
                &inline(&forall(&x.forall, modules, lang)?),
                ""
            )
        ),
        DefinitionStmt::DefPropStmt(x) => {
            let mut args = Vec::new();
            for g in &x.typed_parameters.groups {
                for p in &g.params {
                    args.push(ident(&p.name));
                }
            }
            let body = format!(
                r"{}{}\Longleftrightarrow{}",
                ident(&x.name),
                parens(&args.join(", ")),
                parens(&facts(&x.iff_facts, modules, lang)?)
            );
            format!(
                "{}{}",
                heading(Phrase::Definition, &x.name, lang),
                say(
                    Phrase::ForEvery,
                    &inline(&parameters(&x.typed_parameters, modules, lang)?),
                    &inline(&body),
                    ""
                )
            )
        }
        DefinitionStmt::DefAbstractPropStmt(x) => {
            let args = x
                .params
                .iter()
                .map(|p| ident(p))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "{}{}",
                heading(Phrase::AbstractPredicate, &x.name, lang),
                say(
                    Phrase::Let,
                    &inline(&format!("{}{}", ident(&x.name), parens(&args))),
                    "",
                    ""
                )
            )
        }
        DefinitionStmt::DefThmStmt(x) => format!(
            "{}{}{}",
            heading(Phrase::Theorem, &x.name, lang),
            fact_paragraph(&x.fact, modules, lang)?,
            proof(&x.prove_process, modules, lang)?
        ),
        DefinitionStmt::AxiomStmt(x) => format!(
            "{}{}",
            heading(Phrase::Axiom, &x.name, lang),
            forall_paragraph(&x.forall_fact, modules, lang)?
        ),
        DefinitionStmt::DefStrategyStmt(x) => format!(
            "{}{}{}",
            heading(Phrase::Strategy, &x.name, lang),
            forall_paragraph(&x.forall_fact, modules, lang)?,
            proof(&x.prove_process, modules, lang)?
        ),
        DefinitionStmt::DefStructStmt(x) => {
            let mut out = heading(Phrase::Structure, &x.name, lang);
            if let Some((params, dom)) = &x.param_def_with_dom {
                out.push_str(&say(
                    Phrase::Given,
                    &inline(&parameters(params, modules, lang)?),
                    &inline(&quantifier_frees(dom, modules, lang)?),
                    "",
                ));
            }
            if !x.fields.is_empty() {
                out.push_str("\\begin{description}\n");
                for field in &x.fields {
                    out.push_str(&format!(
                        "\\item[{}] {}\n",
                        inline(&ident(&field.binding.name)),
                        inline(&obj(&field.field_type, modules, lang)?)
                    ));
                }
                out.push_str("\\end{description}\n");
            }
            if !x.equivalent_facts.is_empty() {
                out.push_str(&display(&facts(&x.equivalent_facts, modules, lang)?));
            }
            out
        }
        DefinitionStmt::DefTemplateStmt(x) => {
            let inner = match &x.template_def_stmt {
                TemplateDefEnum::HaveObjInNonemptySetStmt(y) => define_obj(
                    &DefineObjStmt::HaveObjInNonemptySetStmt(y.clone()),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::HaveObjEqualStmt(y) => {
                    define_obj(&DefineObjStmt::HaveObjEqualStmt(y.clone()), modules, lang)?
                }
                TemplateDefEnum::HaveObjByExistFactsStmt(y) => define_obj(
                    &DefineObjStmt::HaveObjByExistFactsStmt(y.clone()),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::HaveByReplacementAxiomStmt(y) => define_obj(
                    &DefineObjStmt::HaveByReplacementAxiomStmt(y.clone()),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::TrustHaveStmt(y) => statement(
                    &Stmt::Trust(TrustBoundaryStmt::TrustHaveStmt(y.clone())),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::ObtainObjFromExistFact(y) => define_obj(
                    &DefineObjStmt::ObtainObjFromExistFact(y.clone()),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::ObtainObjFromAtomicFact(y) => define_obj(
                    &DefineObjStmt::ObtainObjFromAtomicFact(y.clone()),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::HaveFnEqualStmt(y) => {
                    definition(&DefinitionStmt::HaveFnEqualStmt(y.clone()), modules, lang)?
                }
                TemplateDefEnum::HaveFnEqualCaseByCaseStmt(y) => definition(
                    &DefinitionStmt::HaveFnEqualCaseByCaseStmt(y.clone()),
                    modules,
                    lang,
                )?,
                TemplateDefEnum::HaveFnByInducStmt(y) => {
                    definition(&DefinitionStmt::HaveFnByInducStmt(y.clone()), modules, lang)?
                }
                TemplateDefEnum::HaveFnByForallExistUniqueStmt(y) => definition(
                    &DefinitionStmt::HaveFnByForallExistUniqueStmt(y.clone()),
                    modules,
                    lang,
                )?,
            };
            let mut out = heading(Phrase::Template, &x.template_name, lang);
            let params = inline(&parameters(&x.template_arg_def, modules, lang)?);
            if x.template_arg_dom.is_empty() {
                out.push_str(&say(Phrase::Let, &params, "", ""));
            } else {
                out.push_str(&say(
                    Phrase::Given,
                    &params,
                    &inline(&quantifier_frees(&x.template_arg_dom, modules, lang)?),
                    "",
                ));
            }
            out.push_str(&quote(&inner));
            out
        }
    })
}

fn define_obj(
    value: &DefineObjStmt,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let say = |key, a: &str, b: &str, c: &str| paragraph(&sentence(lang, key, a, b, c));
    Ok(match value {
        DefineObjStmt::LetObjStmt(x) => say(
            Phrase::Let,
            &inline(&format!(
                "{} = {}",
                ident(&x.name.name),
                obj(&x.value, modules, lang)?
            )),
            "",
            "",
        ),
        DefineObjStmt::HaveObjInNonemptySetStmt(x) => say(
            Phrase::Let,
            &inline(&parameters(&x.param_def, modules, lang)?),
            "",
            "",
        ),
        DefineObjStmt::HaveObjEqualStmt(x) => {
            let names = x
                .param_def
                .groups
                .iter()
                .flat_map(|g| g.params.iter())
                .collect::<Vec<_>>();
            if names.len() != x.objs_equal_to.len() {
                return Err(RuntimeError::Unsupported(
                    "LaTeX: binding/value counts differ".into(),
                ));
            }
            let mut equalities = Vec::new();
            for (p, y) in names.iter().zip(&x.objs_equal_to) {
                equalities.push(format!("{} = {}", ident(&p.name), obj(y, modules, lang)?));
            }
            say(
                Phrase::Given,
                &inline(&parameters(&x.param_def, modules, lang)?),
                &inline(&equalities.join(r",\ ")),
                "",
            )
        }
        DefineObjStmt::HaveObjByExistFactsStmt(x) => say(
            Phrase::Given,
            &inline(&parameters(&x.param_def, modules, lang)?),
            &inline(&quantifier_frees(&x.facts, modules, lang)?),
            "",
        ),
        DefineObjStmt::ObtainObjFromExistFact(x) => say(
            Phrase::Choose,
            &inline(&bound_names(&x.equal_tos)),
            &inline(&exist_shaped(&x.fact, modules, lang)?),
            "",
        ),
        DefineObjStmt::ObtainObjFromAtomicFact(x) => {
            let mut args = Vec::new();
            for a in &x.fact.body {
                args.push(obj(a, modules, lang)?);
            }
            let source = format!(
                "{}{}",
                name(&x.fact.predicate, modules)?,
                parens(&args.join(", "))
            );
            say(
                Phrase::Choose,
                &inline(&bound_names(&x.equal_tos)),
                &inline(&source),
                "",
            )
        }
        DefineObjStmt::HaveByPreimageStmt(x) => say(
            Phrase::Preimage,
            &inline(&bound_names(&x.preimage_names)),
            &inline(&format!(
                r"{}\in {}",
                obj(&x.range_membership.element, modules, lang)?,
                obj(&x.range_membership.set, modules, lang)?
            )),
            "",
        ),
        DefineObjStmt::HaveByReplacementAxiomStmt(x) => say(
            Phrase::Replacement,
            &inline(&ident(&x.name.name)),
            &inline(&name(&x.prop_name, modules)?),
            &inline(&obj(&x.source_set, modules, lang)?),
        ),
    })
}

fn fact_paragraph(
    value: &Fact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    match value {
        Fact::ForallFact(x) => forall_paragraph(x, modules, lang),
        _ => Ok(display(&fact(value, modules, lang)?)),
    }
}
fn forall_paragraph(
    value: &ForallFact,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    if value.typed_parameters.groups.is_empty() {
        let then = conclusions(&value.then_facts, modules, lang)?;
        return if value.dom_facts.is_empty() {
            Ok(display(&then))
        } else {
            Ok(paragraph(&sentence(
                lang,
                Phrase::IfThen,
                &inline(&facts(&value.dom_facts, modules, lang)?),
                &inline(&then),
                "",
            )))
        };
    }
    let params = inline(&parameters(&value.typed_parameters, modules, lang)?);
    let then = inline(&conclusions(&value.then_facts, modules, lang)?);
    let text = if value.dom_facts.is_empty() {
        sentence(lang, Phrase::ForEvery, &params, &then, "")
    } else {
        sentence(
            lang,
            Phrase::ForEveryIf,
            &params,
            &inline(&facts(&value.dom_facts, modules, lang)?),
            &then,
        )
    };
    Ok(paragraph(&text))
}
fn theorem_call(
    value: &TheoremCall,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut text = name(&value.name, modules)?;
    if let TheoremCallArguments::Parenthesized(args) = &value.arguments {
        let mut items = Vec::new();
        for arg in args {
            items.push(obj(arg, modules, lang)?);
        }
        text.push_str(&parens(&items.join(", ")));
    }
    Ok(text)
}
fn function_cases(
    value: &BoundName,
    label: Phrase,
    clause: &FnSetClause,
    cases: &[crate::ast::fact::AndChainAtomicFact],
    equal_tos: &[crate::ast::obj::Obj],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    if cases.len() != equal_tos.len() {
        return Err(RuntimeError::Unsupported(
            "LaTeX: function case/value counts differ".into(),
        ));
    }
    let mut rows = Vec::new();
    for (case, result) in cases.iter().zip(equal_tos) {
        rows.push(format!(
            "{} & {}",
            obj(result, modules, lang)?,
            and_chain(case, modules, lang)?
        ));
    }
    let mut names = Vec::new();
    for g in &clause.set_bound_parameters.groups {
        for p in &g.params {
            names.push(ident(&p.name));
        }
    }
    Ok(format!(
        "{}{}{}",
        heading(label, &value.name, lang),
        function_signature(value, clause, modules, lang)?,
        display(&format!(
            "{}{} = \\begin{{cases}}\n{}\n\\end{{cases}}",
            ident(&value.name),
            parens(&names.join(", ")),
            rows.join(" \\\\\n")
        ))
    ))
}
fn function_signature(
    value: &BoundName,
    clause: &FnSetClause,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let signature = format!(
        r"{}:\ {}",
        ident(&value.name),
        function_space(
            &clause.set_bound_parameters,
            &clause.dom_facts,
            &clause.ret_set,
            modules,
            lang
        )?
    );
    Ok(paragraph(&sentence(
        lang,
        Phrase::Let,
        &inline(&signature),
        "",
        "",
    )))
}
fn function_induction(
    value: &BoundName,
    label: Phrase,
    clause: &FnSetClause,
    measure: &crate::ast::obj::Obj,
    lower: &crate::ast::obj::Obj,
    cases: &[HaveFnByInducCase],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut out = heading(label, &value.name, lang);
    out.push_str(&function_signature(value, clause, modules, lang)?);
    out.push_str(&paragraph(&sentence(
        lang,
        Phrase::Induction,
        &inline(&obj(measure, modules, lang)?),
        &inline(&obj(lower, modules, lang)?),
        "",
    )));
    let mut names = Vec::new();
    for g in &clause.set_bound_parameters.groups {
        for p in &g.params {
            names.push(ident(&p.name));
        }
    }
    let head = format!("{}{}", ident(&value.name), parens(&names.join(", ")));
    out.push_str(&inductive_cases(cases, &head, modules, lang)?);
    Ok(out)
}
fn inductive_cases(
    values: &[HaveFnByInducCase],
    head: &str,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut out = String::new();
    for (i, value) in values.iter().enumerate() {
        out.push_str(&heading(Phrase::Case, &(i + 1).to_string(), lang));
        out.push_str(&paragraph(&sentence(
            lang,
            Phrase::Suppose,
            &inline(&and_chain(&value.case_fact, modules, lang)?),
            "",
            "",
        )));
        match &value.body {
            HaveFnByInducCaseBody::EqualTo(x) => {
                out.push_str(&display(&format!("{head} = {}", obj(x, modules, lang)?)))
            }
            HaveFnByInducCaseBody::NestedCases(xs) => {
                out.push_str(&quote(&inductive_cases(xs, head, modules, lang)?))
            }
        }
    }
    Ok(out)
}
#[allow(clippy::too_many_arguments)]
fn induction(
    key: Phrase,
    param: &str,
    from: &crate::ast::obj::Obj,
    goals: &[crate::ast::fact::ExistOrAndChainAtomicFact],
    body: &[Stmt],
    base: &Option<Vec<Stmt>>,
    step: &Option<Vec<Stmt>>,
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    let mut out = paragraph(&sentence(
        lang,
        Phrase::Goal,
        &inline(&conclusions(goals, modules, lang)?),
        "",
        "",
    ));
    out.push_str(&paragraph(&sentence(
        lang,
        key,
        &inline(&ident(param)),
        &inline(&obj(from, modules, lang)?),
        "",
    )));
    if let Some(base) = base {
        out.push_str(&heading(Phrase::Base, "", lang));
        out.push_str(&quote(&statements(base, modules, lang)?));
    }
    if let Some(step) = step {
        out.push_str(&heading(Phrase::Step, "", lang));
        out.push_str(&quote(&statements(step, modules, lang)?));
    }
    out.push_str(&proof(body, modules, lang)?);
    Ok(out)
}
fn bound_names(names: &[BoundName]) -> String {
    names
        .iter()
        .map(|p| ident(&p.name))
        .collect::<Vec<_>>()
        .join(", ")
}
fn heading(key: Phrase, title: &str, lang: OutputLanguage) -> String {
    format!(
        "\\par\\noindent\\textbf{{{}{}{}.}}\\par\n",
        phrase(lang, key),
        if title.is_empty() { "" } else { " " },
        escape_text(title)
    )
}
fn paragraph(text: &str) -> String {
    format!("\\par\\noindent {text}\n")
}
fn quote(text: &str) -> String {
    format!("\\begin{{quote}}\n{text}\\end{{quote}}\n")
}
fn proof(
    body: &[Stmt],
    modules: &GlobalModuleManager,
    lang: OutputLanguage,
) -> RuntimeResult<String> {
    if body.is_empty() {
        Ok(String::new())
    } else {
        Ok(format!(
            "{}{}",
            heading(Phrase::Proof, "", lang),
            quote(&statements(body, modules, lang)?)
        ))
    }
}
