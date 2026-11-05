use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const CASES: [(&str, &str); 11] = [
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_exp:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=exp(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_exp(f)
"#,
        "Exp",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_sin:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=sin(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_sin(f)
"#,
        "Sin",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_cos:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=cos(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_cos(f)
"#,
        "Cos",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_arcsin:
    ? forall f fn(x R: -1<=x, x<=1) R:
        forall x {z R: -1<=z, z<=1}:
            f(x)=arcsin(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_arcsin(f)
"#,
        "Arcsin",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_arccos:
    ? forall f fn(x R: -1<=x, x<=1) R:
        forall x {z R: -1<=z, z<=1}:
            f(x)=arccos(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_arccos(f)
"#,
        "Arccos",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_arctan:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=arctan(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_arctan(f)
"#,
        "Arctan",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_arccot:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=arccot(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_arccot(f)
"#,
        "Arccot",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_sinh:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=sinh(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_sinh(f)
"#,
        "Sinh",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_cosh:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=cosh(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_cosh(f)
"#,
        "Cosh",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_tanh:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=tanh(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_tanh(f)
"#,
        "Tanh",
    ),
    (
        r#"# Global continuity of the exact elementary formula on its complete source domain.
thm checked_function_continuous_sech:
    ? forall f fn(x R) R:
        forall x R:
            f(x)=sech(x)
        =>:
            $is_continuous(f)
    release thm fn_continuous_sech(f)
"#,
        "Sech",
    ),
];

#[test]
fn global_elementary_continuity_requires_all_original_stages() {
    for (source, law) in CASES {
        for change in ["proof", "store", "wd", "order"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            assert_eq!(call.dom_proofs.len(), 4);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "wd" => call.conclusions_wd.clear(),
                _ => call.dom_proofs.swap(2, 3),
            }
            assert!(
                compiler.compile_run(&run, change).is_err(),
                "{law}: {change}"
            );
        }
    }
}

#[test]
fn global_elementary_continuity_rejects_another_operator_argument_domain_and_captured_binder() {
    for (source, law) in CASES {
        for change in ["operator", "argument", "domain", "capture", "extra"] {
            let (mut run, compiler) = super::execute(source);
            let builtin = invocation(&mut run).builtin.as_mut().unwrap();
            let Obj::Identifier(IdentifierObj::Plain {
                id: function_id, ..
            }) = &builtin.arguments[0]
            else {
                panic!("function parameter")
            };
            let function_id = *function_id;
            let Fact::ForallFact(all) = &mut builtin.requirements[3] else {
                panic!("original formula")
            };
            match change {
                "domain" => {
                    all.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                "capture" => all.typed_parameters.groups[0].params[0].id = function_id,
                "extra" => all.then_facts.push(all.then_facts[0].clone()),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut all.then_facts[0]
                    else {
                        panic!("formula equality")
                    };
                    if change == "operator" {
                        eq.right = super::number_object("0");
                    } else {
                        eq.left = super::number_object("0");
                    }
                }
            }
            assert!(
                compiler.compile_run(&run, change).is_err(),
                "{law}: {change}"
            );
        }
    }
}

#[test]
fn global_elementary_continuity_rejects_wrong_call_identity_arguments_and_output_property() {
    for (source, law) in CASES {
        for change in ["call", "argument", "property", "function"] {
            let (mut run, compiler) = super::execute(source);
            let builtin = invocation(&mut run).builtin.as_mut().unwrap();
            match change {
                "call" => {
                    builtin.theorem = crate::builtin_theorem::BuiltinTheoremId::FnContinuousIdentity
                }
                "argument" => builtin.arguments.push(super::number_object("0")),
                _ => {
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) =
                        &mut builtin.conclusions[0]
                    else {
                        panic!("continuous output")
                    };
                    if change == "property" {
                        f.property = FunctionContinuityProperty::UniformContinuous;
                    } else {
                        f.function = super::number_object("0");
                    }
                }
            }
            assert!(
                compiler.compile_run(&run, change).is_err(),
                "{law}: {change}"
            );
        }
    }
}

#[test]
fn global_elementary_literal_inference_requires_original_identity_and_published_formation() {
    use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
    use crate::execute::ExecReleaseAndExpandStmtResult;
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferFunctionContinuousFactResult, InferResult,
    };
    for change in ["identity", "derived", "formation"] {
        let (mut run, compiler) = super::execute(
            r#"# Preserve the complete source domain and function object in elementary continuity.
release thm fn_continuous_sin(fn(x R) R{sin(x)})
"#,
        );
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(call),
        )) = &mut run.statement_results[0]
        else {
            panic!("original literal release")
        };
        if change == "formation" {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut call.stored_wd[0] else {
                panic!("original output formation")
            };
            wd.as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .clear();
        } else {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionContinuousFact(rules))) =
                &mut call.stored[0].infer
            else {
                panic!("original global inference")
            };
            let InferFunctionContinuousFactResult::Definition(proof) = &mut rules[0];
            if change == "identity" {
                proof.source_fact_id = proof.derived[0].primary_fact_id();
            } else {
                proof.derived.clear();
            }
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}
