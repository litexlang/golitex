use crate::prelude::*;

pub(in crate::json_output) fn project_have_equal_failure(
    failure: &ExecHaveObjEqualStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecHaveObjEqualStmtFailed::ParamCountMismatch => super::helper::failure_message(
            rt,
            "parameter_count",
            super::super::failure_kind::FailureKind::Arity,
            "parameter and value counts differ",
        ),
        ExecHaveObjEqualStmtFailed::ParamType(result) => {
            super::helper::obj_wd_failure(rt, "parameter_type", result)
        }
        ExecHaveObjEqualStmtFailed::EqualToWellDefined(result) => {
            super::helper::obj_wd_failure(rt, "value_well_defined", result)
        }
        ExecHaveObjEqualStmtFailed::Membership(result) => super::helper::verification_failure(
            rt,
            "membership",
            result,
            super::super::failure_kind::FailureKind::Membership,
        ),
        ExecHaveObjEqualStmtFailed::AutoOpenStructLayer(failed) => {
            project_struct_layer_failure(failed, rt)
        }
    }
}

pub(in crate::json_output) fn project_struct_failure(
    failure: &ExecDefStructStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecDefStructStmtFailed::NameClash(message) => super::helper::failure_message(
            rt,
            "name_clash",
            super::super::failure_kind::FailureKind::NameClash,
            message,
        ),
        ExecDefStructStmtFailed::ParamType(result) => {
            super::helper::obj_wd_failure(rt, "parameter_type", result)
        }
        ExecDefStructStmtFailed::AutoOpenStructLayer(failed) => {
            project_struct_layer_failure(failed, rt)
        }
        ExecDefStructStmtFailed::StructureDomain(failed) => {
            super::helper::fact_wd_failure(rt, "structure_domain", failed)
        }
        ExecDefStructStmtFailed::FieldType(result) => {
            super::helper::obj_wd_failure(rt, "field_type", result)
        }
        ExecDefStructStmtFailed::EquivalentFact(failed) => {
            super::helper::fact_wd_failure(rt, "equivalent_fact", failed)
        }
    }
}

pub(in crate::json_output) fn project_have_fn_exist_failure(
    failure: &ExecHaveFnByForallExistUniqueStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecHaveFnByForallExistUniqueStmtFailed::NameClash(message) => {
            super::helper::failure_message(
                rt,
                "name_clash",
                super::super::failure_kind::FailureKind::NameClash,
                message,
            )
        }
        ExecHaveFnByForallExistUniqueStmtFailed::SourceForall(result) => {
            super::helper::verification_failure(
                rt,
                "source_forall",
                result,
                super::super::failure_kind::FailureKind::ProofSearch,
            )
        }
        ExecHaveFnByForallExistUniqueStmtFailed::FnSetWellDefined(result) => {
            super::helper::obj_wd_failure(rt, "fn_set_well_defined", result)
        }
        ExecHaveFnByForallExistUniqueStmtFailed::PropertyWellDefined(failed) => {
            super::helper::fact_wd_failure(rt, "property_well_defined", failed)
        }
    }
}

pub(in crate::json_output) fn project_have_exist_failure(
    failure: &ExecHaveObjByExistFactsStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecHaveObjByExistFactsStmtFailed::Exist(failed) => {
            super::verify::project_exist_failed("exist", failed, rt)
        }
    }
}

pub(in crate::json_output) fn project_obtain_exist_failure(
    failure: &ExecObtainObjFromExistFactStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecObtainObjFromExistFactStmtFailed::ArityMismatch { expected, got } => {
            let result = super::super::helper::object_for(
                rt,
                vec![
                    ("phase", super::super::helper::string("witness_count")),
                    ("expected", JsonValue::Number(*expected as f64)),
                    ("actual", JsonValue::Number(*got as f64)),
                ],
            );
            super::super::helper::with_failure_diagnostic(
                rt,
                result,
                super::super::failure_kind::FailureKind::Arity,
                vec![],
            )
        }
        ExecObtainObjFromExistFactStmtFailed::NotExistSource => super::helper::failure_message(
            rt,
            "source_kind",
            super::super::failure_kind::FailureKind::Unsupported,
            "obtain requires a positive existential source",
        ),
        ExecObtainObjFromExistFactStmtFailed::Exist(failed) => {
            super::verify::project_exist_failed("exist", failed, rt)
        }
    }
}

pub(in crate::json_output) fn project_obtain_atomic_failure(
    failure: &ExecObtainObjFromAtomicFactStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecObtainObjFromAtomicFactStmtFailed::AbstractProp => super::helper::failure_message(
            rt,
            "abstract_prop",
            super::super::failure_kind::FailureKind::DefinitionProofUnavailable,
            "abstract predicates have no existential definition",
        ),
        ExecObtainObjFromAtomicFactStmtFailed::PropNotFound => super::helper::failure_message(
            rt,
            "prop_not_found",
            super::super::failure_kind::FailureKind::NameNotFound,
            "predicate definition was not found",
        ),
        ExecObtainObjFromAtomicFactStmtFailed::BadDefinition(message) => {
            super::helper::failure_message(
                rt,
                "definition",
                super::super::failure_kind::FailureKind::Unsupported,
                message,
            )
        }
        ExecObtainObjFromAtomicFactStmtFailed::AtomicVerifyFailed(result) => {
            super::helper::verification_failure(
                rt,
                "source_fact",
                result,
                super::super::failure_kind::FailureKind::ProofSearch,
            )
        }
        ExecObtainObjFromAtomicFactStmtFailed::Instantiate(message) => {
            super::helper::failure_message(
                rt,
                "instantiate",
                super::super::failure_kind::FailureKind::Instantiation,
                message,
            )
        }
        ExecObtainObjFromAtomicFactStmtFailed::Apply(failed) => {
            project_obtain_exist_failure(failed, rt)
        }
    }
}

pub(in crate::json_output) fn project_preimage_failure(
    failure: &ExecHaveByFnPreimageStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecHaveByFnPreimageStmtFailed::NotFnRange(message) => super::helper::failure_message(
            rt,
            "source_shape",
            super::super::failure_kind::FailureKind::Unsupported,
            message,
        ),
        ExecHaveByFnPreimageStmtFailed::NoFnSetBody(message) => super::helper::failure_message(
            rt,
            "function_domain",
            super::super::failure_kind::FailureKind::Domain,
            message,
        ),
        ExecHaveByFnPreimageStmtFailed::ArityMismatch { expected, got } => {
            super::helper::failure_message(
                rt,
                "parameter_count",
                super::super::failure_kind::FailureKind::Arity,
                &format!("expected {expected} objects, got {got}"),
            )
        }
        ExecHaveByFnPreimageStmtFailed::SourceMembership(result) => {
            super::helper::verification_failure(
                rt,
                "source_membership",
                result,
                super::super::failure_kind::FailureKind::Membership,
            )
        }
    }
}

pub(in crate::json_output) fn project_replacement_failure(
    failure: &ExecHaveByReplacementAxiomStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failure {
        ExecHaveByReplacementAxiomStmtFailed::PropArity(message) => super::helper::failure_message(
            rt,
            "predicate_arity",
            super::super::failure_kind::FailureKind::Arity,
            message,
        ),
        ExecHaveByReplacementAxiomStmtFailed::SourceWd(result) => {
            super::helper::obj_wd_failure(rt, "source_well_defined", result)
        }
        ExecHaveByReplacementAxiomStmtFailed::UniquenessMissing(message) => {
            super::helper::failure_message(
                rt,
                "uniqueness",
                super::super::failure_kind::FailureKind::ProofSearch,
                message,
            )
        }
        ExecHaveByReplacementAxiomStmtFailed::Define(message) => super::helper::failure_message(
            rt,
            "define",
            super::super::failure_kind::FailureKind::DefinitionConstruction,
            message,
        ),
    }
}

pub(super) fn project_struct_layer_failure(
    failed: &crate::execute::FailToReleaseOneStructLayer,
    rt: &Runtime,
) -> JsonValue {
    let projected = super::super::helper::object_for(
        rt,
        vec![
            (
                "phase",
                super::super::helper::string("auto_open_struct_layer"),
            ),
            (
                "obj",
                super::super::helper::string(failed.obj.readable_string()),
            ),
            (
                "struct_obj",
                super::super::helper::string(failed.struct_obj.readable_string()),
            ),
            ("reason", super::super::helper::string(&failed.reason)),
        ],
    );
    super::super::helper::with_failure_diagnostic(
        rt,
        projected,
        super::super::failure_kind::FailureKind::StructExpansion,
        vec![],
    )
}
