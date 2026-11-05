use super::dense_order_theorem_tests::invocation;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ExpLogOperatorObjWellDefinedProofByDef as E, HyperbolicOperatorObjWellDefinedProofByDef as H,
    TrigOperatorObjWellDefinedProofByDef as T,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
const SOURCES: [&str; 9] = [
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_ln_restricted:
    ? forall f fn(x R+) R:
        forall x R+:
            f(x)=ln(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_ln(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_log_restricted:
    ? forall f fn(x R+) R,base R+:
        base!=1
        forall x R+:
            f(x)=log(base,x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_log(f,base)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_tan_restricted:
    ? forall f fn(x R: cos(x)!=0) R:
        forall x {z R: cos(z)!=0}:
            f(x)=tan(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_tan(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_cot_restricted:
    ? forall f fn(x R: sin(x)!=0) R:
        forall x {z R: sin(z)!=0}:
            f(x)=cot(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_cot(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_sec_restricted:
    ? forall f fn(x R: cos(x)!=0) R:
        forall x {z R: cos(z)!=0}:
            f(x)=sec(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_sec(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_csc_restricted:
    ? forall f fn(x R: sin(x)!=0) R:
        forall x {z R: sin(z)!=0}:
            f(x)=csc(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_csc(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_coth_restricted:
    ? forall f fn(x R: x!=0) R:
        forall x {z R: z!=0}:
            f(x)=coth(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_coth(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_csch_restricted:
    ? forall f fn(x R: x!=0) R:
        forall x {z R: z!=0}:
            f(x)=csch(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_csch(f)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_sqrt_restricted:
    ? forall f fn(x R: x>=0) R:
        forall x {z R: z>=0}:
            f(x)=sqrt(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_sqrt(f)
"#,
];
const LITERALS: [&str; 9] = [
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_ln(fn(x R+) R{ln(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_log(fn(x R+) R{log(2,x)},2)
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_tan(fn(x R:cos(x)!=0) R{tan(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_cot(fn(x R:sin(x)!=0) R{cot(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_sec(fn(x R:cos(x)!=0) R{sec(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_csc(fn(x R:sin(x)!=0) R{csc(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_coth(fn(x R:x!=0) R{coth(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_csch(fn(x R:x!=0) R{csch(x)})
"#,
    r#"# Continuity on the complete declared domain, preserving original operator conditions.
release thm fn_continuous_sqrt(fn(x R:x>=0) R{sqrt(x)})
"#,
];
const EMPTY: &str = r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_ln_empty_no_formula:
    ? forall f fn(x {}) R:
        $is_continuous(f)
    release thm fn_continuous_ln(f)
"#;
fn release(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    if matches!(&run.statement_results[0], ExecStmtResult::Definition(_)) {
        return invocation(run);
    }
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("original literal release")
    };
    p
}
fn forall(proof: &VerifyFactResult) -> &VerifyForallFactProof {
    let VerifyFactResult::ForallFact(p) = proof else {
        panic!("original forall")
    };
    let VerifyForallFactResult::Success(p) = p.as_ref() else {
        panic!("successful forall")
    };
    p
}
fn forall_mut(proof: &mut VerifyFactResult) -> &mut VerifyForallFactProof {
    let VerifyFactResult::ForallFact(p) = proof else {
        panic!("original forall")
    };
    let VerifyForallFactResult::Success(p) = p.as_mut() else {
        panic!("successful forall")
    };
    p
}
fn named_mut(run: &mut RunLitexCodeResult) -> &mut ExecDefThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem")
    };
    p
}
fn original_operator(run: &mut RunLitexCodeResult, index: usize) -> &mut ObjWellDefinedProof {
    let p = named_mut(run);
    let ExecDefThmBodyProof::Forall(b) = &mut p.body else {
        panic!()
    };
    let FactWellDefinedProof::ForallFact(wd) = &mut b.assumed_dom_facts[index].well_defined else {
        panic!()
    };
    let FactWellDefinedProof::Equality(eq) = &mut wd.as_detailed_mut().unwrap().then[0] else {
        panic!()
    };
    &mut eq.as_detailed_mut().unwrap().right
}
fn stages(
    wd: &mut ObjWellDefinedProof,
) -> (
    &mut Vec<Box<ObjWellDefinedProof>>,
    &mut Vec<VerifyFactResult>,
) {
    let DetailedObjWellDefinedProof::ByDef { proof, .. } = wd.as_detailed_mut().unwrap() else {
        panic!("fresh source operator WD")
    };
    match proof {
        ObjWellDefinedProofByDef::ExpLogOperator(E::Ln(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::ExpLogOperator(E::Log(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::ExpLogOperator(E::Sqrt(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::TrigOperator(T::Tan(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::TrigOperator(T::Cot(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::TrigOperator(T::Sec(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::TrigOperator(T::Csc(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::HyperbolicOperator(H::Coth(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ObjWellDefinedProofByDef::HyperbolicOperator(H::Csch(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        _ => panic!("actual selected operator"),
    }
}
#[test]
fn restricted_continuity_replays_nine_actual_native_schemas_deterministically() {
    use crate::builtin_theorem::BuiltinTheoremId::*;
    for ((source, id), law) in SOURCES
        .into_iter()
        .zip([
            FnContinuousLn,
            FnContinuousLog,
            FnContinuousTan,
            FnContinuousCot,
            FnContinuousSec,
            FnContinuousCsc,
            FnContinuousCoth,
            FnContinuousCsch,
            FnContinuousSqrt,
        ])
        .zip([
            "Ln", "Log", "Tan", "Cot", "Sec", "Csc", "Coth", "Csch", "Sqrt",
        ])
    {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert!(matches!(
            p.theorem_derivation,
            crate::execute::execute_by_stmt::TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(
            p.dom_proofs.len(),
            if id == FnContinuousLog { 6 } else { 4 }
        );
        let out = c
            .compile_run(&run, "restricted_continuity")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains(&format!("Litex.functionContinuousOf{law}")));
        assert_eq!(out, c.compile_run(&run, "restricted_continuity").unwrap());
    }
}
#[test]
fn restricted_continuity_retains_actual_known_local_and_empty_forall_owners() {
    let mut seen = [false; 3];
    for source in SOURCES.into_iter().chain(LITERALS).chain([EMPTY]) {
        let (mut run, c) = super::execute(source);
        let p = release(&mut run);
        seen[match forall(p.dom_proofs.last().unwrap()) {
            VerifyForallFactProof::ByKnownForallFact(_) => 0,
            VerifyForallFactProof::ByLocalIntroduction(_) => 1,
            VerifyForallFactProof::ByEmptyParameterDomain(_) => 2,
        }] = true;
        c.compile_run(&run, "restriction_owners")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
    assert_eq!(seen, [true, true, true], "actual verifier routes");
    for source in [
        r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_ln_empty_domain:
    ? forall f fn(x {}) R:
        forall x {}:
            f(x)=ln(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_ln(f)
"#,
        r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_sqrt_singleton_zero:
    ? forall f fn(x {0}) R:
        forall x {0}:
            f(x)=sqrt(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_sqrt(f)
"#,
        r#"# Preserve the original real argument when constructing an inferred trigonometric subject.
thm checked_inferred_sin_nonzero_real:
    ? forall x R:
        sin(x)!=0
        =>:
            sin(x) $in R
    sin(x) $in R
"#,
        r#"# Preserve the original real argument when constructing an inferred trigonometric subject.
thm checked_inferred_cos_nonzero_real:
    ? forall x R:
        cos(x)!=0
        =>:
            cos(x) $in R
    cos(x) $in R
"#,
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "domain_edges")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}
#[test]
fn restricted_continuity_requires_every_original_ordered_pipeline_stage() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "derivation",
            "arguments",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store_order" => p.dom_stores.swap(0, 1),
                "arguments" => p.builtin.as_mut().unwrap().arguments.clear(),
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(
                c.compile_run(&run, "bad_restriction_stage").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn restricted_continuity_keeps_the_complete_domain_binder_and_exact_equation() {
    for source in SOURCES {
        for change in ["domain", "capture", "guard", "operator", "output", "extra"] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &b.arguments[0] else {
                panic!()
            };
            let id = *id;
            let Fact::ForallFact(f) = b.requirements.last_mut().unwrap() else {
                panic!()
            };
            match change {
                "domain" => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                "capture" => f.typed_parameters.groups[0].params[0].id = id,
                "extra" => f.then_facts.push(f.then_facts[0].clone()),
                "guard" => f.dom_facts.push(Fact::AtomicFact(AtomicFact::EqualFact(
                    crate::ast::fact::EqualFact {
                        fact_id: FactId::new(999999),
                        left: super::number_object("0"),
                        right: super::number_object("0"),
                        line_file: None,
                    },
                ))),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) =
                        &mut f.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == "operator" {
                        e.right = super::number_object("0");
                    } else {
                        e.left = super::number_object("0");
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_restriction_formula").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn restricted_continuity_log_retains_positive_nonunit_base_and_argument_order() {
    for change in ["carrier", "base", "nonunit", "orientation", "formula_base"] {
        let (mut run, c) = super::execute(SOURCES[1]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        match change {
            "carrier" | "base" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[3] else {
                    panic!()
                };
                if change == "carrier" {
                    f.set = Obj::StandardSet(StandardSet::R);
                } else {
                    f.element = super::number_object("2");
                }
            }
            "nonunit" | "orientation" => {
                let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut b.requirements[4] else {
                    panic!()
                };
                if change == "nonunit" {
                    f.right = super::number_object("0");
                } else {
                    std::mem::swap(&mut f.left, &mut f.right);
                }
            }
            _ => {
                let Fact::ForallFact(f) = &mut b.requirements[5] else {
                    panic!()
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) =
                    &mut f.then_facts[0]
                else {
                    panic!()
                };
                let Obj::ExpLogOperator(ExpLogOperator::Log(log)) = &mut e.right else {
                    panic!()
                };
                std::mem::swap(&mut log.base, &mut log.arg);
            }
        }
        assert!(
            c.compile_run(&run, "bad_original_log_base").is_err(),
            "{change}"
        );
    }
}
#[test]
fn restricted_continuity_retains_original_call_identity_result_function_and_property() {
    for source in SOURCES {
        for change in ["identity", "property", "function", "polarity"] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "identity" {
                b.theorem = crate::builtin_theorem::BuiltinTheoremId::FnContinuousIdentity;
            } else if change == "polarity" {
                let Fact::AtomicFact(f) = &b.conclusions[0] else {
                    panic!()
                };
                b.conclusions[0] =
                    Fact::AtomicFact(crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap());
            } else {
                let Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) = &mut b.conclusions[0]
                else {
                    panic!()
                };
                if change == "property" {
                    f.property = FunctionContinuityProperty::UniformContinuous;
                } else {
                    f.function = super::number_object("0");
                }
            }
            assert!(
                c.compile_run(&run, "bad_restriction_result").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn restricted_continuity_known_formulas_require_original_visible_citations_and_binders() {
    for source in SOURCES {
        for change in ["future", "renaming", "types", "stores", "wd"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
            let VerifyForallFactProof::ByKnownForallFact(f) =
                forall_mut(p.dom_proofs.last_mut().unwrap())
            else {
                panic!("actual known formula")
            };
            match change {
                "future" => f.cite_fact_id = future,
                "renaming" => f.parameter_renamings.clear(),
                "types" => f
                    .well_defined
                    .as_detailed_mut()
                    .unwrap()
                    .introduced_params
                    .param_type_well_defined
                    .clear(),
                "stores" => f
                    .well_defined
                    .as_detailed_mut()
                    .unwrap()
                    .introduced_params
                    .defined_params
                    .store_and_infer_results
                    .clear(),
                _ => f.well_defined.as_detailed_mut().unwrap().then.clear(),
            }
            assert!(
                c.compile_run(&run, "bad_restriction_citation").is_err(),
                "{change}"
            );
        }
    }
    for source in LITERALS {
        for change in ["types", "then"] {
            let (mut run, c) = super::execute(source);
            let p = release(&mut run);
            let VerifyForallFactProof::ByLocalIntroduction(f) =
                forall_mut(p.dom_proofs.last_mut().unwrap())
            else {
                panic!("actual local formula")
            };
            if change == "types" {
                f.introduced_params.param_type_well_defined.clear();
            } else {
                f.proved_then_facts.clear();
            }
            assert!(
                c.compile_run(&run, "bad_original_local_formula").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn restricted_continuity_rejects_damaged_original_operator_children_and_restrictions() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in ["child", "count", "condition"] {
            let (mut run, c) = super::execute(source);
            let wd = original_operator(&mut run, usize::from(i == 1));
            let (children, requirements) = stages(wd);
            match change {
                "child" => children.clear(),
                "count" => {
                    requirements.pop();
                }
                _ => {
                    let index = if i == 1 {
                        3
                    } else if i == 0 {
                        0
                    } else {
                        1
                    };
                    let fact = &mut super::atomic_proof_mut(&mut requirements[index]).fact;
                    match fact {
                        AtomicFact::InFact(f) => f.set = Obj::StandardSet(StandardSet::R),
                        AtomicFact::NotEqualFact(f) => f.right = super::number_object("1"),
                        AtomicFact::GreaterFact(f) => f.right = super::number_object("1"),
                        AtomicFact::LessEqualFact(f) => f.left = super::number_object("1"),
                        _ => panic!("actual operator restriction"),
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_original_operator_condition")
                    .is_err(),
                "{i} {change}"
            );
        }
    }
}
#[test]
fn inferred_trigonometric_constructors_use_only_the_exact_visible_real_argument() {
    for (source, kind) in [
        (
            r#"# Preserve the original real argument when constructing an inferred trigonometric subject.
thm checked_inferred_sin_nonzero_real:
    ? forall x R:
        sin(x)!=0
        =>:
            sin(x) $in R
    sin(x) $in R
"#,
            "sin",
        ),
        (
            r#"# Preserve the original real argument when constructing an inferred trigonometric subject.
thm checked_inferred_cos_nonzero_real:
    ? forall x R:
        cos(x)!=0
        =>:
            cos(x) $in R
    cos(x) $in R
"#,
            "cos",
        ),
    ] {
        let (mut run, c) = super::execute(source);
        let p = named_mut(&mut run);
        let Fact::ForallFact(f) = &p.statement.fact else {
            panic!()
        };
        let Fact::AtomicFact(AtomicFact::NotEqualFact(guard)) = &f.dom_facts[0] else {
            panic!()
        };
        let complete = SourcePosition::new(None, SourceOwner::Named(p), 1);
        let term = c
            .compile_inferred_numeric_obj(&guard.left, &complete)
            .unwrap();
        assert!(term.0.contains(&format!("Litex.{kind}")));
        assert!(term.1.contains("Litex.realToComplex"));
        let future = SourcePosition {
            before: 0,
            ..complete
        };
        assert!(c
            .compile_inferred_numeric_obj(&guard.left, &future)
            .is_err());
    }
    let (mut run,c)=super::execute("thm checked_restricted_continuity_complex_reflexivity_control:\n    ? forall x C:\n        x=x\n    x=x\n");
    let p = named_mut(&mut run);
    let Fact::ForallFact(f) = &p.statement.fact else {
        panic!()
    };
    let x = Obj::Identifier(IdentifierObj::from_bound_name(
        &f.typed_parameters.groups[0].params[0],
    ));
    let scope = SourcePosition::new(None, SourceOwner::Named(p), 1);
    for value in [
        Obj::TrigOperator(TrigOperator::Sin(Sin {
            arg: Box::new(x.clone()),
        })),
        Obj::TrigOperator(TrigOperator::Cos(Cos {
            arg: Box::new(x.clone()),
        })),
    ] {
        assert!(
            c.compile_inferred_numeric_obj(&value, &scope).is_err(),
            "a complex argument is not an original real certificate"
        );
    }
}
#[test]
fn restricted_continuity_literal_inferences_retain_identity_derived_facts_and_formation() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferFunctionContinuousFactResult, InferResult,
    };
    for source in LITERALS {
        for change in ["identity", "derived", "formation"] {
            let (mut run, c) = super::execute(source);
            let p = release(&mut run);
            if change == "formation" {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.stored_wd[0] else {
                    panic!()
                };
                wd.as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .clear();
            } else {
                let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionContinuousFact(
                    rules,
                ))) = &mut p.stored[0].infer
                else {
                    panic!()
                };
                let InferFunctionContinuousFactResult::Definition(f) = &mut rules[0];
                if change == "identity" {
                    f.source_fact_id = f.derived[0].primary_fact_id();
                } else {
                    f.derived.clear();
                }
            }
            assert!(
                c.compile_run(&run, "bad_restriction_inference").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn restricted_continuity_actual_call_owners_cannot_lose_original_proofs_or_wd() {
    use crate::execute::execute_by_stmt::{ExecByStmtResult, ExecByThmStmtResult};
    for source in [
        r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_ln_call:
    ? forall f fn(x R+) R:
        forall x R+:
            f(x)=ln(x)
        =>:
            $is_continuous(f)
    by thm fn_continuous_ln(f) => $is_continuous(f)
"#,
        r#"# Continuity on the complete declared domain, preserving original operator conditions.
thm checked_function_continuous_tan_call:
    ? forall f fn(x R: cos(x)!=0) R:
        forall x {z R: cos(z)!=0}:
            f(x)=tan(x)
        =>:
            $is_continuous(f)
    by thm fn_continuous_tan(f) => $is_continuous(f)
"#,
    ] {
        for change in ["proof", "wd"] {
            let (mut run, c) = super::execute(source);
            let p = named_mut(&mut run);
            let ExecDefThmBodyProof::Forall(b) = &mut p.body else {
                panic!()
            };
            let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
                &mut b.proof_steps[0]
            else {
                panic!("actual explicit-goal Call")
            };
            if change == "proof" {
                p.dom_proofs.pop();
            } else {
                p.conclusions_wd.clear();
            }
            assert!(c.compile_run(&run, "bad_restriction_call").is_err());
        }
    }
}
#[test]
fn restricted_continuity_empty_route_requires_original_carrier_equality_store_and_wd() {
    for change in ["carrier", "group", "equality", "store", "wd"] {
        let (mut run, c) = super::execute(EMPTY);
        let p = invocation(&mut run);
        let VerifyForallFactProof::ByEmptyParameterDomain(f) = forall_mut(&mut p.dom_proofs[3])
        else {
            panic!("actual empty-domain producer")
        };
        match change {
            "carrier" => f.empty_carrier = Obj::StandardSet(StandardSet::R),
            "group" => f.parameter_group_index = 1,
            "equality" => {
                super::equality_proof_mut(&mut f.empty_carrier_proof)
                    .fact
                    .right = Obj::StandardSet(StandardSet::R);
            }
            "store" => {
                let crate::store_fact_and_infer::StoreFactResult::AtomicFact(stored) =
                    &mut f.empty_carrier_store.store
                else {
                    panic!("original carrier equality store")
                };
                let AtomicFact::EqualFact(eq) = &mut stored.fact else {
                    panic!("original equality")
                };
                eq.right = Obj::StandardSet(StandardSet::R);
            }
            _ => f.well_defined.as_detailed_mut().unwrap().then.clear(),
        }
        assert!(
            c.compile_run(&run, "bad_original_empty_domain").is_err(),
            "{change}"
        );
    }
}
