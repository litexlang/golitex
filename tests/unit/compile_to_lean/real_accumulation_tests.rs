use crate::execute::execute_by_stmt::{
    ExecByDefStmtResult, ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{
    ExecDefThmBodyProof, ExecDefThmForallProof, ExecDefThmStmtResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition as Definition,
    AtomicExceptEqualityFactSearchedProof as Search, BuiltinPropDefinitionProof as Builtin,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::execute::ExecDefinitionStmtResult;
use crate::launch_command::parse_launch_command;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferRealAccumulationFactResult, InferResult,
};

const CITATIONS: [&str; 3] = [
    r#"# Cite positive and negative at accumulation facts on a real subset.
thm at_accumulation_citation:
    ? forall A set, p R:
        A $subset R
        $is_real_accumulation_at(A,p)
        =>:
            $is_real_accumulation_at(A,p)

thm at_accumulation_negation_citation:
    ? forall A set, p R:
        A $subset R
        not $is_real_accumulation_at(A,p)
        =>:
            not $is_real_accumulation_at(A,p)
"#,
    r#"# Cite positive and negative left accumulation facts on a real subset.
thm left_accumulation_citation:
    ? forall A set, p R:
        A $subset R
        $is_real_accumulation_left(A,p)
        =>:
            $is_real_accumulation_left(A,p)

thm left_accumulation_negation_citation:
    ? forall A set, p R:
        A $subset R
        not $is_real_accumulation_left(A,p)
        =>:
            not $is_real_accumulation_left(A,p)
"#,
    r#"# Cite positive and negative right accumulation facts on a real subset.
thm right_accumulation_citation:
    ? forall A set, p R:
        A $subset R
        $is_real_accumulation_right(A,p)
        =>:
            $is_real_accumulation_right(A,p)

thm right_accumulation_negation_citation:
    ? forall A set, p R:
        A $subset R
        not $is_real_accumulation_right(A,p)
        =>:
            not $is_real_accumulation_right(A,p)
"#,
];
const DEFINITIONS: [&str; 3] = [
    r#"# Fold the at accumulation definition from its quantified witnesses.
thm at_accumulation_from_witnesses:
    ? forall A set, p R:
        A $subset R
        forall radius R+:
            exist x A st {0<abs(x-p) and abs(x-p)<radius}
        =>:
            $is_real_accumulation_at(A,p)
    by def $is_real_accumulation_at(A,p)
"#,
    r#"# Fold the left accumulation definition from its quantified witnesses.
thm left_accumulation_from_witnesses:
    ? forall A set, p R:
        A $subset R
        forall radius R+:
            exist x A st {0<p-x and p-x<radius}
        =>:
            $is_real_accumulation_left(A,p)
    by def $is_real_accumulation_left(A,p)
"#,
    r#"# Fold the right accumulation definition from its quantified witnesses.
thm right_accumulation_from_witnesses:
    ? forall A set, p R:
        A $subset R
        forall radius R+:
            exist x A st {0<x-p and x-p<radius}
        =>:
            $is_real_accumulation_right(A,p)
    by def $is_real_accumulation_right(A,p)
"#,
];
const CONNECTIONS: [&str; 6] = [
    r#"# A limit equal to the point value gives at continuity on the original domain.
thm at_continuity_from_limit:
    ? forall f fn(x R) R, p R:
        $has_limit_at(f,p,f(p))
        =>:
            $is_continuous_at(f,p)
    by thm fn_continuous_at_from_limit(f,p) => $is_continuous_at(f,p)
"#,
    r#"# Convert at continuity into a limit using the original domain's accumulation fact.
thm at_limit_from_continuity:
    ? forall f fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_real_accumulation_at(R,p)
        =>:
            $has_limit_at(f,p,f(p))
    by thm fn_continuous_at_to_limit(f,p) => $has_limit_at(f,p,f(p))
"#,
    r#"# A limit equal to the point value gives left continuity on the original domain.
thm left_continuity_from_limit:
    ? forall f fn(x R) R, p R:
        $has_limit_left(f,p,f(p))
        =>:
            $is_continuous_left(f,p)
    by thm fn_continuous_left_from_limit(f,p) => $is_continuous_left(f,p)
"#,
    r#"# Convert left continuity into a limit using the original domain's accumulation fact.
thm left_limit_from_continuity:
    ? forall f fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_real_accumulation_left(R,p)
        =>:
            $has_limit_left(f,p,f(p))
    by thm fn_continuous_left_to_limit(f,p) => $has_limit_left(f,p,f(p))
"#,
    r#"# A limit equal to the point value gives right continuity on the original domain.
thm right_continuity_from_limit:
    ? forall f fn(x R) R, p R:
        $has_limit_right(f,p,f(p))
        =>:
            $is_continuous_right(f,p)
    by thm fn_continuous_right_from_limit(f,p) => $is_continuous_right(f,p)
"#,
    r#"# Convert right continuity into a limit using the original domain's accumulation fact.
thm right_limit_from_continuity:
    ? forall f fn(x R) R, p R:
        $is_continuous_right(f,p)
        $is_real_accumulation_right(R,p)
        =>:
            $has_limit_right(f,p,f(p))
    by thm fn_continuous_right_to_limit(f,p) => $has_limit_right(f,p,f(p))
"#,
];
fn body(run: &mut RunLitexCodeResult) -> &mut ExecDefThmForallProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    p
}
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
        &mut body(run).proof_steps[0]
    else {
        panic!("builtin invocation")
    };
    p
}
#[test]
fn real_accumulation_formation_requires_real_subset_and_real_point() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(CITATIONS[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut body(&mut run).assumed_dom_facts[1].well_defined
        else {
            panic!("atomic WD")
        };
        let PredicateDomainProof::ByRequirements(requirements) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("domain requirements")
        };
        match mutation {
            0 => {
                requirements.pop();
            }
            1 => requirements.swap(0, 1),
            _ => {
                let Fact::AtomicFact(AtomicFact::SubsetFact(f)) = &mut requirements[0].requirement
                else {
                    panic!("real subset")
                };
                f.right = Obj::StandardSet(StandardSet::C);
            }
        }
        c.compile_run(&run, "changed_accumulation_domain")
            .expect_err("real subset and point");
    }
}
#[test]
fn real_accumulation_inference_requires_original_identity_and_clause() {
    for missing in [false, true] {
        let (mut run, c) = super::execute(CITATIONS[0]);
        let b = body(&mut run);
        let wrong = b.assumed_dom_facts[0]
            .store_and_infer
            .store
            .primary_fact_id();
        let Some(InferResult::AtomicFact(InferAtomicFactResult::RealAccumulationFact(rules))) =
            &mut b.assumed_dom_facts[1].store_and_infer.infer
        else {
            panic!("inference")
        };
        let [InferRealAccumulationFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition")
        };
        if missing {
            p.derived.clear();
        } else {
            p.source_fact_id = wrong;
        }
        c.compile_run(&run, "changed_accumulation_inference")
            .expect_err("original identity and stored clause");
    }
}
#[test]
fn real_accumulation_definition_requires_original_witness_domain_and_radius() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(DEFINITIONS[0]);
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut body(&mut run).proof_steps[0]
        else {
            panic!("by definition")
        };
        let p = super::atomic_proof_mut(&mut p.proof);
        let Search::ByDefinition(Definition::BuiltinProp(Builtin::RealAccumulation(p))) =
            &mut p.searched_proof
        else {
            panic!("accumulation definition")
        };
        match mutation {
            0 => p.proof_of_requirement_facts.clear(),
            1 => {
                let Fact::ForallFact(all) = &mut p.requirement_facts[0] else {
                    panic!("forall")
                };
                all.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            }
            _ => {
                let Fact::ForallFact(all) = &mut p.requirement_facts[0] else {
                    panic!("forall")
                };
                let ExistOrAndChainAtomicFact::ExistFact(exists) = &mut all.then_facts[0] else {
                    panic!("exists")
                };
                exists.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            }
        }
        c.compile_run(&run, "changed_accumulation_definition")
            .expect_err("original radius and witness domain");
    }
}
#[test]
fn continuity_limit_connections_reject_missing_steps_or_changed_subjects() {
    for (index, source) in CONNECTIONS.into_iter().enumerate() {
        for mutation in 0..5 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.dom_stores.clear(),
                2 => p.conclusions_wd.clear(),
                3 => {
                    let b = p.builtin.as_mut().unwrap();
                    let f = if index % 2 == 0 {
                        &mut b.requirements[4]
                    } else {
                        &mut b.conclusions[0]
                    };
                    let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = f else {
                        panic!("limit")
                    };
                    f.value = b.arguments[1].clone();
                }
                _ => {
                    let b = p.builtin.as_mut().unwrap();
                    if index % 2 == 1 {
                        let Fact::AtomicFact(AtomicFact::RealAccumulationFact(f)) =
                            &mut b.requirements[5]
                        else {
                            panic!("accumulation")
                        };
                        f.domain = Obj::StandardSet(StandardSet::C);
                    } else {
                        let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
                            &mut b.requirements[4]
                        else {
                            panic!("limit")
                        };
                        f.approach = if index == 0 {
                            LimitApproach::FromLeft(b.arguments[1].clone().into())
                        } else {
                            LimitApproach::AtPoint(b.arguments[1].clone().into())
                        };
                    }
                }
            }
            c.compile_run(&run, "changed_continuity_limit")
                .expect_err("original value, approach, accumulation and stages");
        }
    }
}

#[test]
fn continuity_on_an_isolated_domain_does_not_supply_a_punctured_limit() {
    let source="thm missing_accumulation:\n    ? forall f fn(x R: x=0) R:\n        $is_continuous_at(f,0)\n        =>:\n            $has_limit_at(f,0,f(0))\n    by thm fn_continuous_at_to_limit(f,0) => $has_limit_at(f,0,f(0))\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let result = runtime.run_litex_code(source).unwrap();
    assert!(!result.success && result.session_error.is_none());
    let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(runtime);
    compiler
        .compile_run(&result, "isolated_domain")
        .expect_err("the required accumulation fact is absent");
}
