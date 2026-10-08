//! Exhaustive Normal projection for every non-Fact ExecStmtResult branch.
//! Fact stays in `project_normal.rs` (richer proof_method).

use super::explain::explain_stmt_kind;
use super::helper::{
    array_of_strings, bool_value, empty_string_array, infer_fact_texts_from_store_and_infer,
    object, output_language, split_have_fact_id_texts, store_fact_texts, string,
};
use crate::execute::execute_by_stmt::{
    ExecByCasesStmtResult, ExecByContraStmtResult, ExecByDefStmtResult,
    ExecByEnumerateFiniteSetStmtResult, ExecByExtensionStmtResult, ExecByFnExtensionStmtResult,
    ExecByForStmtResult, ExecByInducStmtResult, ExecByStmtResult, ExecByStrongInducStmtResult,
    ExecByThmStmtResult,
};
use crate::execute::execute_eval_stmt::{ExecCommandStmtResult, ExecEvalStmtResult};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimStmtResult, ExecProofBlockStmtResult, ExecSketchStmtFailed, ExecSketchStmtResult,
};
use crate::execute::execute_register_stmt::ExecRegisterStmtResult;
use crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult;
use crate::execute::execute_unsafe_stmt::ExecTrustBoundaryStmtResult;
use crate::execute::execute_witness_stmt::ExecWitnessStmtResult;
use crate::execute::{
    ExecAxiomStmtResult, ExecDefAlgoByCasesStmtResult, ExecDefAlgoByInducStmtResult,
    ExecDefPropStmtResult, ExecDefStrategyStmtResult, ExecDefStructStmtResult,
    ExecDefTemplateStmtResult, ExecDefThmStmtResult, ExecDefineObjStmtResult,
    ExecDefinitionStmtResult, ExecHaveByFnPreimageStmtResult, ExecHaveByReplacementAxiomStmtResult,
    ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByInducStmtResult,
    ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnEqualStmtFailed, ExecHaveFnEqualStmtResult,
    ExecHaveObjByExistFactsStmtResult, ExecHaveObjEqualStmtResult,
    ExecHaveObjInNonemptySetStmtResult, ExecLetObjStmtResult,
    ExecObtainObjFromAtomicFactStmtResult, ExecObtainObjFromExistFactStmtResult,
    ExecReleaseAndExpandStmtResult, ExecReleaseStructDefStmtResult, ExecStmtResult,
    ExecTrustHaveStmtResult, ExecTrustStmtResult, ExecWitnessAtomicFactStmtResult,
    ExecWitnessExistFactStmtResult, ExecWitnessNonemptySetStmtResult,
};
use crate::knowledge_base::JsonValue;
use crate::runtime::{FactId, Runtime};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub(super) fn project_non_fact_stmt(result: &ExecStmtResult, runtime: &Runtime) -> JsonValue {
    match result {
        ExecStmtResult::Fact(_) => unreachable!("fact projected elsewhere"),
        ExecStmtResult::Definition(d) => project_definition(d, runtime),
        ExecStmtResult::Witness(w) => project_witness(w, runtime),
        ExecStmtResult::Trust(t) => project_trust(t, runtime),
        ExecStmtResult::By(b) => project_by(b, runtime),
        ExecStmtResult::Register(r) => project_register(r, runtime),
        ExecStmtResult::ReleaseAndExpand(r) => project_release(r, runtime),
        ExecStmtResult::ProofBlock(p) => project_proof_block(p, runtime),
        ExecStmtResult::Command(c) => project_command(c, runtime),
    }
}

fn project_definition(def: &ExecDefinitionStmtResult, runtime: &Runtime) -> JsonValue {
    match def {
        ExecDefinitionStmtResult::DefineObj(o) => project_define_obj(o, runtime),
        ExecDefinitionStmtResult::HaveFnEqual(r) => match r {
            ExecHaveFnEqualStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_fn_equal",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveFnEqualStmtResult::Failed(
                ExecHaveFnEqualStmtFailed::AnonymousFnWellDefined(wd)
                | ExecHaveFnEqualStmtFailed::FnSetWellDefined(wd),
            ) => failed_with_details(
                runtime,
                "have fn …",
                "have_fn_equal",
                super::project_detailed::project_verify_obj_wd(wd, runtime),
            ),
        },
        ExecDefinitionStmtResult::HaveFnEqualCaseByCase(r) => match r {
            ExecHaveFnEqualCaseByCaseStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_fn_cases",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveFnEqualCaseByCaseStmtResult::Failed(failure) => failed_with_details(
                runtime,
                "have fn … case by case",
                "have_fn_cases",
                super::project_detailed::project_cases_definition_failure(failure, runtime),
            ),
        },
        ExecDefinitionStmtResult::HaveFnByForallExistUnique(r) => match r {
            ExecHaveFnByForallExistUniqueStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_fn_forall_exist_unique",
                &s.stored_fact_ids,
            ),
            ExecHaveFnByForallExistUniqueStmtResult::Failed(_) => failed(
                runtime,
                "have fn … by exist!",
                "have_fn_forall_exist_unique",
            ),
        },
        ExecDefinitionStmtResult::HaveFnByInduc(r) => match r {
            ExecHaveFnByInducStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_fn_induc",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveFnByInducStmtResult::Failed(f) => failed_with_details(
                runtime,
                "have fn … by induc",
                "have_fn_induc",
                super::project_detailed::project_induc_definition_failure(f, runtime),
            ),
        },
        ExecDefinitionStmtResult::DefProp(r) => match r {
            ExecDefPropStmtResult::Success(s) => {
                success_plain(runtime, s.statement.readable_string(), "def_prop")
            }
            ExecDefPropStmtResult::Failed(f) => failed_with_details(
                runtime,
                "prop …",
                "def_prop",
                super::project_detailed::project_def_prop_failure(f, runtime),
            ),
        },
        ExecDefinitionStmtResult::DefAbstractProp(s) => {
            success_plain(runtime, s.statement.readable_string(), "def_abstract_prop")
        }
        ExecDefinitionStmtResult::DefStruct(r) => match r {
            ExecDefStructStmtResult::Success(s) => {
                let mut stores = Vec::new();
                let mut infers = Vec::new();
                for published in &s.definition_facts {
                    stores.extend(store_fact_texts(&published.store_and_infer.store));
                    infers.extend(infer_fact_texts_from_store_and_infer(
                        runtime,
                        &published.store_and_infer,
                    ));
                }
                success_parts(
                    runtime,
                    s.statement.readable_string(),
                    "def_struct",
                    stores,
                    infers,
                )
            }
            ExecDefStructStmtResult::Failed(_) => failed(runtime, "struct …", "def_struct"),
        },
        ExecDefinitionStmtResult::DefTemplate(r) => match r {
            ExecDefTemplateStmtResult::Success(s) => {
                let mut stores = Vec::new();
                let mut infers = Vec::new();
                for published in &s.definition_facts {
                    stores.extend(store_fact_texts(&published.store_and_infer.store));
                    infers.extend(infer_fact_texts_from_store_and_infer(
                        runtime,
                        &published.store_and_infer,
                    ));
                }
                success_parts(
                    runtime,
                    s.statement.readable_string(),
                    "def_template",
                    stores,
                    infers,
                )
            }
            ExecDefTemplateStmtResult::Failed(failure) => failed_with_details(
                runtime,
                "template …",
                "def_template",
                super::project_detailed::project_template_failure(failure, runtime),
            ),
        },
        ExecDefinitionStmtResult::DefAlgoByCases(r) => match r {
            ExecDefAlgoByCasesStmtResult::Success(s) => {
                success_plain(runtime, s.statement.readable_string(), "def_algo_cases")
            }
            ExecDefAlgoByCasesStmtResult::Failed(_) => {
                failed(runtime, "algo … by cases", "def_algo_cases")
            }
        },
        ExecDefinitionStmtResult::DefAlgoByInduc(r) => match r {
            ExecDefAlgoByInducStmtResult::Success(s) => {
                success_plain(runtime, s.statement.readable_string(), "def_algo_induc")
            }
            ExecDefAlgoByInducStmtResult::Failed(
                crate::execute::ExecDefAlgoByInducStmtFailed::DefineFn(f),
            ) => failed_with_details(
                runtime,
                "algo … by induc",
                "def_algo_induc",
                super::project_detailed::project_induc_definition_failure(f, runtime),
            ),
            ExecDefAlgoByInducStmtResult::Failed(
                crate::execute::ExecDefAlgoByInducStmtFailed::AlgoAlreadyDefined,
            ) => failed(runtime, "algo … by induc", "def_algo_induc"),
        },
        ExecDefinitionStmtResult::DefThm(r) => match r {
            ExecDefThmStmtResult::Success(s) => {
                let stores = store_fact_texts(&s.stored.store);
                let infers = infer_fact_texts_from_store_and_infer(runtime, &s.stored);
                let statement = stores.first().cloned().unwrap_or_else(|| "thm".to_string());
                success_parts(runtime, statement, "def_thm", stores, infers)
            }
            ExecDefThmStmtResult::Failed(f) => failed_with_details(
                runtime,
                "thm",
                "def_thm",
                super::project_detailed::project_def_thm_failure(f, runtime),
            ),
        },
        ExecDefinitionStmtResult::Axiom(r) => match r {
            ExecAxiomStmtResult::Success(s) => {
                let stores = store_fact_texts(&s.stored.store);
                let infers = infer_fact_texts_from_store_and_infer(runtime, &s.stored);
                let statement = stores
                    .first()
                    .cloned()
                    .unwrap_or_else(|| "axiom".to_string());
                success_parts(runtime, statement, "axiom", stores, infers)
            }
            ExecAxiomStmtResult::Failed(_) => failed(runtime, "axiom", "axiom"),
        },
        ExecDefinitionStmtResult::DefStrategy(r) => match r {
            ExecDefStrategyStmtResult::Success(_) => {
                success_plain(runtime, "strategy".into(), "def_strategy")
            }
            ExecDefStrategyStmtResult::Failed(_) => failed(runtime, "strategy", "def_strategy"),
        },
    }
}

fn project_define_obj(obj: &ExecDefineObjStmtResult, runtime: &Runtime) -> JsonValue {
    match obj {
        ExecDefineObjStmtResult::LetObj(r) => match r {
            ExecLetObjStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "let",
                &s.stored_fact_ids,
            ),
            ExecLetObjStmtResult::Failed(wd) => failed_with_details(
                runtime,
                "let …",
                "let",
                super::project_detailed::project_verify_obj_wd(wd, runtime),
            ),
        },
        ExecDefineObjStmtResult::HaveObjInNonemptySet(r) => match r {
            ExecHaveObjInNonemptySetStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_in_nonempty",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveObjInNonemptySetStmtResult::Failed(_) => {
                failed(runtime, "have …", "have_in_nonempty")
            }
        },
        ExecDefineObjStmtResult::HaveObjEqual(r) => match r {
            ExecHaveObjEqualStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_equal",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveObjEqualStmtResult::Failed(_) => failed(runtime, "have … = …", "have_equal"),
        },
        ExecDefineObjStmtResult::HaveObjByExistFacts(r) => match r {
            ExecHaveObjByExistFactsStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_by_exist",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveObjByExistFactsStmtResult::Failed(_) => {
                failed(runtime, "have … by exist", "have_by_exist")
            }
        },
        ExecDefineObjStmtResult::ObtainObjFromExistFact(r) => match r {
            ExecObtainObjFromExistFactStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "obtain_exist",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecObtainObjFromExistFactStmtResult::Failed(_) => {
                failed(runtime, "obtain … from exist", "obtain_exist")
            }
        },
        ExecDefineObjStmtResult::ObtainObjFromAtomicFact(r) => match r {
            ExecObtainObjFromAtomicFactStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "obtain_atomic",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecObtainObjFromAtomicFactStmtResult::Failed(_) => {
                failed(runtime, "obtain … from atomic", "obtain_atomic")
            }
        },
        ExecDefineObjStmtResult::HaveByFnPreimage(r) => match r {
            ExecHaveByFnPreimageStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_by_preimage",
                &s.store_and_infer_result.stored_fact_ids,
            ),
            ExecHaveByFnPreimageStmtResult::Failed(_) => {
                failed(runtime, "have by preimage …", "have_by_preimage")
            }
        },
        ExecDefineObjStmtResult::HaveByReplacementAxiom(r) => match r {
            ExecHaveByReplacementAxiomStmtResult::Success(s) => success_with_ids(
                runtime,
                s.statement.readable_string(),
                "have_by_replacement",
                &s.stored_fact_ids,
            ),
            ExecHaveByReplacementAxiomStmtResult::Failed(_) => {
                failed(runtime, "have by replacement …", "have_by_replacement")
            }
        },
    }
}

fn project_witness(w: &ExecWitnessStmtResult, runtime: &Runtime) -> JsonValue {
    match w {
        ExecWitnessStmtResult::WitnessExistFact(r) => match r {
            ExecWitnessExistFactStmtResult::Success(s) => success_from_store(
                runtime,
                s.statement.readable_string(),
                "witness_exist",
                &s.store_and_infer_result,
            ),
            ExecWitnessExistFactStmtResult::Failed(_) => {
                failed(runtime, "witness exist …", "witness_exist")
            }
        },
        ExecWitnessStmtResult::WitnessAtomicFact(r) => match r {
            ExecWitnessAtomicFactStmtResult::Success(s) => success_from_store(
                runtime,
                s.statement.readable_string(),
                "witness_atomic",
                &s.store_and_infer_result,
            ),
            ExecWitnessAtomicFactStmtResult::Failed(_) => {
                failed(runtime, "witness …", "witness_atomic")
            }
        },
        ExecWitnessStmtResult::WitnessNonemptySet(r) => match r {
            ExecWitnessNonemptySetStmtResult::Success(s) => success_from_store(
                runtime,
                s.statement.readable_string(),
                "witness_nonempty",
                &s.store_and_infer_result,
            ),
            ExecWitnessNonemptySetStmtResult::Failed(_) => {
                failed(runtime, "witness nonempty …", "witness_nonempty")
            }
        },
    }
}

fn project_trust(t: &ExecTrustBoundaryStmtResult, runtime: &Runtime) -> JsonValue {
    match t {
        ExecTrustBoundaryStmtResult::TrustStmt(r) => match r {
            ExecTrustStmtResult::Success(s) => {
                let (stores, infers) = flatten_store_nodes(runtime, &s.store_and_infer_results);
                success_parts(
                    runtime,
                    s.statement.readable_string(),
                    "trust",
                    stores,
                    infers,
                )
            }
            ExecTrustStmtResult::Failed(_) => failed(runtime, "trust …", "trust"),
        },
        ExecTrustBoundaryStmtResult::TrustHaveStmt(r) => match r {
            ExecTrustHaveStmtResult::Success(s) => {
                let (stores, infers) =
                    flatten_store_nodes(runtime, &s.body_store_and_infer_results);
                success_parts(
                    runtime,
                    s.statement.readable_string(),
                    "trust_have",
                    stores,
                    infers,
                )
            }
            ExecTrustHaveStmtResult::Failed(_) => failed(runtime, "trust have …", "trust_have"),
        },
    }
}

fn project_by(b: &ExecByStmtResult, runtime: &Runtime) -> JsonValue {
    match b {
        ExecByStmtResult::Cases(r) => match r {
            ExecByCasesStmtResult::Success(s) => {
                let (stores, infers) = flatten_store_nodes(runtime, &s.stored);
                success_parts(runtime, "by cases".into(), "by_cases", stores, infers)
            }
            ExecByCasesStmtResult::Failed(f) => failed_with_details(
                runtime,
                "by cases",
                "by_cases",
                super::project_detailed::project_cases_failure(f, runtime),
            ),
        },
        ExecByStmtResult::Contra(r) => match r {
            ExecByContraStmtResult::Success(s) => {
                success_from_store(runtime, s.goal.readable_string(), "by_contra", &s.stored)
            }
            ExecByContraStmtResult::Failed(f) => failed_with_details(
                runtime,
                "by contradiction",
                "by_contra",
                super::project_detailed::project_contra_failure(f, runtime),
            ),
        },
        ExecByStmtResult::Def(r) => match r {
            ExecByDefStmtResult::Success(s) => {
                success_from_store(runtime, "by def".into(), "by_def", &s.stored)
            }
            ExecByDefStmtResult::Failed(_) => failed(runtime, "by def", "by_def"),
        },
        ExecByStmtResult::Extension(r) => match r {
            ExecByExtensionStmtResult::Success(s) => {
                success_from_store(runtime, "by extension".into(), "by_extension", &s.stored)
            }
            ExecByExtensionStmtResult::Failed(f) => failed_with_details(
                runtime,
                "by extension",
                "by_extension",
                super::project_detailed::project_extension_failure(f, runtime),
            ),
        },
        ExecByStmtResult::FnExtension(r) => match r {
            ExecByFnExtensionStmtResult::Success(s) => success_from_store(
                runtime,
                "by fn_extension".into(),
                "by_fn_extension",
                &s.stored,
            ),
            ExecByFnExtensionStmtResult::Failed(_) => {
                failed(runtime, "by fn_extension", "by_fn_extension")
            }
        },
        ExecByStmtResult::EnumerateFiniteSet(r) => match r {
            ExecByEnumerateFiniteSetStmtResult::Success(s) => {
                success_from_store(runtime, "by enumerate".into(), "by_enumerate", &s.stored)
            }
            ExecByEnumerateFiniteSetStmtResult::Failed(_) => {
                failed(runtime, "by enumerate", "by_enumerate")
            }
        },
        ExecByStmtResult::For(r) => match r {
            ExecByForStmtResult::Success(s) => {
                success_from_store(runtime, "by for".into(), "by_for", &s.stored)
            }
            ExecByForStmtResult::Failed(_) => failed(runtime, "by for", "by_for"),
        },
        ExecByStmtResult::Thm(r) => match r {
            ExecByThmStmtResult::Success(s) => success_from_store(
                runtime,
                format!("by thm {}", s.call.name.local_name()),
                "by_thm",
                &s.stored,
            ),
            ExecByThmStmtResult::Failed(f) => failed_with_details(
                runtime,
                "by thm",
                "by_thm",
                super::project_detailed::project_by_thm_failure(f, runtime),
            ),
        },
        ExecByStmtResult::Induc(r) => match r {
            ExecByInducStmtResult::Success(s) => {
                success_from_store(runtime, "by induc".into(), "by_induc", &s.stored)
            }
            ExecByInducStmtResult::Failed(f) => failed_with_details(
                runtime,
                "by induc",
                "by_induc",
                super::project_detailed::project_induc_failure(f, runtime),
            ),
        },
        ExecByStmtResult::StrongInduc(r) => match r {
            ExecByStrongInducStmtResult::Success(s) => success_from_store(
                runtime,
                "by strong_induc".into(),
                "by_strong_induc",
                &s.stored,
            ),
            ExecByStrongInducStmtResult::Failed(f) => failed_with_details(
                runtime,
                "by strong_induc",
                "by_strong_induc",
                super::project_detailed::project_strong_induc_failure(f, runtime),
            ),
        },
    }
}

fn project_register(r: &ExecRegisterStmtResult, runtime: &Runtime) -> JsonValue {
    let (ok, kind) = match r {
        ExecRegisterStmtResult::ReflexiveProp(x) => (!x.is_failed(), "register_reflexive"),
        ExecRegisterStmtResult::SymmetricProp(x) => (!x.is_failed(), "register_symmetric"),
        ExecRegisterStmtResult::TransitiveProp(x) => (!x.is_failed(), "register_transitive"),
    };
    if ok {
        success_plain(runtime, kind.replace('_', " "), kind)
    } else {
        failed(runtime, &kind.replace('_', " "), kind)
    }
}

fn project_release(r: &ExecReleaseAndExpandStmtResult, runtime: &Runtime) -> JsonValue {
    match r {
        ExecReleaseAndExpandStmtResult::Thm(x) => match x {
            crate::execute::execute_by_stmt::ExecReleaseThmStmtResult::Failed(f) => {
                failed_with_details(
                    runtime,
                    "release thm …",
                    "release_thm",
                    super::project_detailed::project_release_thm_failure(f, runtime),
                )
            }
            crate::execute::execute_by_stmt::ExecReleaseThmStmtResult::Success(s) => {
                let (stores, infers) = flatten_store_nodes(runtime, &s.stored);
                success_parts(
                    runtime,
                    format!("release thm {}", s.call.name.local_name()),
                    "release_thm",
                    stores,
                    infers,
                )
            }
        },
        ExecReleaseAndExpandStmtResult::StructDef(x) => match x {
            ExecReleaseStructDefStmtResult::Success(s) => {
                success_plain(runtime, s.statement.readable_string(), "release_struct")
            }
            ExecReleaseStructDefStmtResult::Failed(_) => {
                failed(runtime, "release struct …", "release_struct")
            }
        },
        ExecReleaseAndExpandStmtResult::ObjDef(x) => match x {
            ExecReleaseObjDefStmtResult::Success(s) => {
                let (stores, infers) = flatten_store_nodes(runtime, &s.store_and_infer);
                success_parts(
                    runtime,
                    s.statement.readable_string(),
                    "release_obj",
                    stores,
                    infers,
                )
            }
            ExecReleaseObjDefStmtResult::Failed(_) => {
                failed(runtime, "release obj …", "release_obj")
            }
        },
        ExecReleaseAndExpandStmtResult::TupleDef(x) => match x {
            crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult::Success(s) => {
                let (stores, infers) = flatten_store_nodes(runtime, &s.stored);
                success_parts(runtime, s.statement.readable_string(), "release_tuple_def", stores, infers)
            }
            crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult::Failed(_) => failed_with_details(
                runtime, "release tuple def …", "release_tuple_def", super::project_detailed::project_release_tuple_def(x, runtime),
            ),
        },
        ExecReleaseAndExpandStmtResult::CartDef(x) => match x {
            crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult::Success(s) => {
                let (stores, infers) = flatten_store_nodes(runtime, std::slice::from_ref(&s.store_and_infer));
                success_parts(runtime, s.statement.readable_string(), "release_cart_def", stores, infers)
            }
            crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult::Failed(_) => failed_with_details(
                runtime, "release cart def …", "release_cart_def", super::project_detailed::project_release_cart_def(x, runtime),
            ),
        },
        ExecReleaseAndExpandStmtResult::ExpandRange(x) => {
            if x.is_failed() {
                failed(runtime, "expand range …", "expand_range")
            } else {
                success_plain(runtime, "expand range …".into(), "expand_range")
            }
        }
        ExecReleaseAndExpandStmtResult::ZornLemma(x) => {
            if x.is_failed() {
                failed(runtime, "release zorn …", "release_zorn")
            } else {
                success_plain(runtime, "release zorn …".into(), "release_zorn")
            }
        }
        ExecReleaseAndExpandStmtResult::AxiomOfChoice(x) => {
            if x.is_failed() {
                failed(runtime, "release choice …", "release_choice")
            } else {
                success_plain(runtime, "release choice …".into(), "release_choice")
            }
        }
        ExecReleaseAndExpandStmtResult::RegularityAxiom(x) => {
            if x.is_failed() {
                failed(runtime, "release regularity …", "release_regularity")
            } else {
                success_plain(runtime, "release regularity …".into(), "release_regularity")
            }
        }
    }
}

fn project_proof_block(p: &ExecProofBlockStmtResult, runtime: &Runtime) -> JsonValue {
    match p {
        ExecProofBlockStmtResult::Claim(r) => match r {
            ExecClaimStmtResult::Success(s) => {
                let stores = store_fact_texts(&s.stored.store);
                let infers = infer_fact_texts_from_store_and_infer(runtime, &s.stored);
                let statement = stores
                    .first()
                    .cloned()
                    .map(|g| format!("claim: {g}"))
                    .unwrap_or_else(|| "claim".to_string());
                success_parts(runtime, statement, "claim", stores, infers)
            }
            ExecClaimStmtResult::Failed(f) => failed_with_details(
                runtime,
                "claim",
                "claim",
                super::project_detailed::project_claim_failure(f, runtime),
            ),
        },
        ExecProofBlockStmtResult::Sketch(r) => match r {
            ExecSketchStmtResult::Success(_) => success_plain(runtime, "sketch".into(), "sketch"),
            ExecSketchStmtResult::Failed(ExecSketchStmtFailed::ProofBody(f)) => {
                failed_with_details(
                    runtime,
                    "sketch",
                    "sketch",
                    object(
                        output_language(runtime),
                        vec![
                            ("step_index", JsonValue::Number(f.step_index as f64)),
                            (
                                "result",
                                super::project_normal::project_stmt_normal(&f.result, runtime),
                            ),
                        ],
                    ),
                )
            }
        },
    }
}

fn project_command(c: &ExecCommandStmtResult, runtime: &Runtime) -> JsonValue {
    match c {
        ExecCommandStmtResult::Eval(r) => match r {
            ExecEvalStmtResult::Success(s) => {
                let mut value = success_from_store(
                    runtime,
                    s.statement.readable_string(),
                    "eval",
                    &s.store_and_infer_result,
                );
                if let JsonValue::Object(fields) = &mut value {
                    fields.insert(
                        super::json_keys::localize_key(
                            "evaluated_object",
                            output_language(runtime),
                        ),
                        string(s.evaluated_object.readable_string()),
                    );
                }
                value
            }
            ExecEvalStmtResult::Failed(crate::execute::ExecEvalStmtFailed::WellDefined(
                failed_wd,
            )) => failed_with_details(
                runtime,
                "eval …",
                "eval",
                super::project_detailed::project_verify_obj_wd(failed_wd, runtime),
            ),
            ExecEvalStmtResult::Failed(crate::execute::ExecEvalStmtFailed::AlgorithmEquation(proof)) => failed_with_details(
                runtime,
                "eval …",
                "eval",
                super::project_detailed::project_verify_fact(proof, runtime),
            ),
            ExecEvalStmtResult::Failed(crate::execute::ExecEvalStmtFailed::EvaluatedEqualityWellDefined(wd)) => failed_with_details(
                runtime,
                "eval …",
                "eval",
                super::project_detailed::project_verify_equal_wd(wd, runtime),
            ),
            ExecEvalStmtResult::Failed(
                crate::execute::ExecEvalStmtFailed::UnsupportedExpression,
            ) => failed_with_details(
                runtime,
                "eval …",
                "eval",
                object(
                    output_language(runtime),
                    vec![("cause", string("unsupported_expression"))],
                ),
            ),
            ExecEvalStmtResult::Failed(
                crate::execute::ExecEvalStmtFailed::AggregateBudgetExceeded,
            ) => failed_with_details(
                runtime,
                "eval …",
                "eval",
                object(
                    output_language(runtime),
                    vec![("cause", string("aggregate_budget_exceeded"))],
                ),
            ),
            ExecEvalStmtResult::Failed(
                crate::execute::ExecEvalStmtFailed::AggregateRangeOverflow,
            ) => failed_with_details(
                runtime,
                "eval …",
                "eval",
                object(
                    output_language(runtime),
                    vec![("cause", string("aggregate_range_overflow"))],
                ),
            ),
            ExecEvalStmtResult::Failed(_) => failed(runtime, "eval …", "eval"),
        },
    }
}

fn success_with_ids(
    runtime: &Runtime,
    statement: String,
    kind: &str,
    fact_ids: &[FactId],
) -> JsonValue {
    let (stores, infers) = split_have_fact_id_texts(runtime, fact_ids);
    success_parts(runtime, statement, kind, stores, infers)
}

fn success_from_store(
    runtime: &Runtime,
    statement: String,
    kind: &str,
    store: &StoreFactAndInferResult,
) -> JsonValue {
    let stores = store_fact_texts(&store.store);
    let infers = infer_fact_texts_from_store_and_infer(runtime, store);
    success_parts(runtime, statement, kind, stores, infers)
}

fn success_plain(runtime: &Runtime, statement: String, kind: &str) -> JsonValue {
    success_parts(runtime, statement, kind, Vec::new(), Vec::new())
}

fn success_parts(
    runtime: &Runtime,
    statement: String,
    kind: &str,
    stores: Vec<String>,
    infers: Vec<String>,
) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_stmt_kind(kind, lang);
    object(
        lang,
        vec![
            ("success", bool_value(true)),
            ("statement", string(statement)),
            (
                "proof_method",
                object(
                    lang,
                    vec![
                        ("type", string(text.type_tag)),
                        ("rule_name", string(text.rule_name)),
                        ("message", string(text.message)),
                    ],
                ),
            ),
            ("stores", array_of_strings(stores)),
            ("infers", array_of_strings(infers)),
        ],
    )
}

fn failed(runtime: &Runtime, statement: &str, kind: &str) -> JsonValue {
    let lang = output_language(runtime);
    let text = explain_stmt_kind(kind, lang);
    object(
        lang,
        vec![
            ("success", bool_value(false)),
            ("statement", string(statement)),
            (
                "why_failed",
                object(
                    lang,
                    vec![
                        ("type", string(text.type_tag)),
                        ("rule_name", string(text.rule_name)),
                        ("message", string(text.message)),
                        ("phase", string(kind)),
                    ],
                ),
            ),
            ("stores", empty_string_array()),
            ("infers", empty_string_array()),
        ],
    )
}

fn failed_with_details(
    runtime: &Runtime,
    statement: &str,
    kind: &str,
    details: JsonValue,
) -> JsonValue {
    let mut value = failed(runtime, statement, kind);
    let lang = output_language(runtime);
    let reason_key = super::json_keys::localize_key("why_failed", lang);
    if let JsonValue::Object(fields) = &mut value {
        if let Some(JsonValue::Object(mut reason)) = fields.get(&reason_key).cloned() {
            reason.insert(super::json_keys::localize_key("failure", lang), details);
            fields.insert(reason_key, JsonValue::Object(reason));
        }
    }
    value
}

fn flatten_store_nodes(
    runtime: &Runtime,
    nodes: &[StoreFactAndInferResult],
) -> (Vec<String>, Vec<String>) {
    let mut stores = Vec::new();
    let mut infers = Vec::new();
    for node in nodes {
        stores.extend(store_fact_texts(&node.store));
        infers.extend(infer_fact_texts_from_store_and_infer(runtime, node));
    }
    (stores, infers)
}
