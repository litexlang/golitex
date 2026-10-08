//! Generated Obj WD by-def projection. Prefer regenerating via scripts if shapes change.
use super::searched::project_known_equality_path;
use super::store::project_verify_facts;
use super::wd::{project_fact_wd_proof, project_obj_wd_proof};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ObjWellDefinedProof, ObjWellDefinedProofByDef, *,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

fn project_common_by_def(
    obj: &Obj,
    family: &str,
    kind: &str,
    children: &[Box<ObjWellDefinedProof>],
    requirements: &[crate::execute::execute_fact_stmt::VerifyFactResult],
    runtime: &Runtime,
) -> JsonValue {
    let child_json: Vec<JsonValue> = children
        .iter()
        .map(|c| project_obj_wd_proof(c, runtime))
        .collect();
    object_for(
        runtime,
        vec![
            ("type", string("by_def")),
            ("family", string(family)),
            ("kind", string(kind)),
            ("obj", string(obj.readable_string())),
            ("child_obj_well_defined", JsonValue::Array(child_json)),
            (
                "requirement_fact_verified",
                project_verify_facts(requirements, runtime),
            ),
        ],
    )
}

pub(super) fn project_obj_wd_by_def(
    obj: &Obj,
    proof: &ObjWellDefinedProofByDef,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Abs(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Abs",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Add(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Add",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Ceil(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Ceil",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Div",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Floor(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Floor",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Max(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Max",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Min(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Min",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Mul(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Mul",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Neg(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Neg",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Pow",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Sign(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Sign",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(
            ArithmeticOperatorObjWellDefinedProofByDef::Sub(p),
        ) => project_common_by_def(
            obj,
            "ArithmeticOperator",
            "Sub",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ComplexOperator(
            ComplexOperatorObjWellDefinedProofByDef::ComplexAbs(p),
        ) => project_common_by_def(
            obj,
            "ComplexOperator",
            "ComplexAbs",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ComplexOperator(
            ComplexOperatorObjWellDefinedProofByDef::ImaginaryPart(p),
        ) => project_common_by_def(
            obj,
            "ComplexOperator",
            "ImaginaryPart",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ComplexOperator(
            ComplexOperatorObjWellDefinedProofByDef::RealPart(p),
        ) => project_common_by_def(
            obj,
            "ComplexOperator",
            "RealPart",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Exp(
            p,
        )) => project_common_by_def(
            obj,
            "ExpLogOperator",
            "Exp",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Ln(p)) => {
            project_common_by_def(
                obj,
                "ExpLogOperator",
                "Ln",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Log(
            p,
        )) => project_common_by_def(
            obj,
            "ExpLogOperator",
            "Log",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(
            p,
        )) => project_common_by_def(
            obj,
            "ExpLogOperator",
            "Sqrt",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::FiniteSetStat(
            FiniteSetStatObjWellDefinedProofByDef::FiniteSetMax(p),
        ) => project_common_by_def(
            obj,
            "FiniteSetStat",
            "FiniteSetMax",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::FiniteSetStat(
            FiniteSetStatObjWellDefinedProofByDef::FiniteSetMin(p),
        ) => project_common_by_def(
            obj,
            "FiniteSetStat",
            "FiniteSetMin",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::FiniteSetStat(
            FiniteSetStatObjWellDefinedProofByDef::FiniteSetSize(p),
        ) => project_common_by_def(
            obj,
            "FiniteSetStat",
            "FiniteSetSize",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::FnObj(p) => {
            let child_json: Vec<JsonValue> = p
                .child_obj_well_defined
                .iter()
                .map(|c| project_obj_wd_proof(c, runtime))
                .collect();
            let mut entries = vec![
                ("type", string("by_def")),
                ("family", string("FnObj")),
                ("kind", string("FnObj")),
                ("obj", string(obj.readable_string())),
                ("child_obj_well_defined", JsonValue::Array(child_json)),
                (
                    "requirement_fact_verified",
                    project_verify_facts(&p.requirement_fact_verified, runtime),
                ),
            ];
            if let Some(domain) = &p.domain_fn_set {
                let d = match domain {
                    FnObjDomainFnSetEvidence::FiniteFunction(source) => {
                        super::function_domain::project_finite_function_source(source, runtime)
                    }
                    FnObjDomainFnSetEvidence::InFunctionSet {
                        fn_set,
                        fact_id,
                        function_equal,
                    } => object_for(
                        runtime,
                        vec![
                            ("type", string("in_function_set")),
                            (
                                "fn_set",
                                string(crate::display_and_ir::readable_string_from_ir_text(
                                    fn_set.ir().as_str(),
                                )),
                            ),
                            ("fact_id", string(fact_id.to_string())),
                            (
                                "function_equal",
                                project_known_equality_path(function_equal, runtime),
                            ),
                        ],
                    ),
                    FnObjDomainFnSetEvidence::TemplateDefinition {
                        fn_set,
                        function_equal,
                    } => object_for(
                        runtime,
                        vec![
                            ("type", string("template_definition")),
                            (
                                "fn_set",
                                string(
                                    crate::ast::obj::Obj::FunctionSpace(
                                        crate::ast::obj::FunctionSpace::FnSet(fn_set.clone()),
                                    )
                                    .readable_string(),
                                ),
                            ),
                            (
                                "function_equal",
                                project_known_equality_path(function_equal, runtime),
                            ),
                        ],
                    ),
                    FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => object_for(
                        runtime,
                        vec![
                            ("type", string("anonymous_literal")),
                            (
                                "fn_set",
                                string(crate::display_and_ir::readable_string_from_ir_text(
                                    fn_set.ir().as_str(),
                                )),
                            ),
                        ],
                    ),
                };
                entries.push(("domain_fn_set", d));
            }
            object_for(runtime, entries)
        }
        ObjWellDefinedProofByDef::FunctionSpace(
            FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(p),
        ) => {
            let entries = vec![
                ("type", string("by_def")),
                ("family", string("FunctionSpace")),
                ("kind", string("AnonymousFn")),
                ("obj", string(obj.readable_string())),
                (
                    "param_type_well_defined",
                    JsonValue::Array(
                        p.param_type_well_defined
                            .iter()
                            .map(|c| project_obj_wd_proof(c, runtime))
                            .collect(),
                    ),
                ),
                (
                    "dom_fact_well_defined",
                    JsonValue::Array(
                        p.dom_fact_well_defined
                            .iter()
                            .map(|f| project_fact_wd_proof(f, runtime))
                            .collect(),
                    ),
                ),
                (
                    "ret_set_well_defined",
                    project_obj_wd_proof(&p.ret_set_well_defined, runtime),
                ),
                (
                    "body_well_defined",
                    project_obj_wd_proof(&p.body_well_defined, runtime),
                ),
                (
                    "body_in_ret_set",
                    match &p.body_in_ret_set {
                        AnonymousFnBodyInReturnSetProof::CheckedMembership(proof) => {
                            super::verify::project_verify_fact(proof, runtime)
                        }
                        AnonymousFnBodyInReturnSetProof::EmptyCompleteDomain(proof) => object_for(
                            runtime,
                            vec![
                                ("type", string("return_bound_vacuous_empty_domain")),
                                (
                                    "domain_empty",
                                    super::function_domain::project_domain_empty(proof, runtime),
                                ),
                            ],
                        ),
                    },
                ),
            ];
            object_for(runtime, entries)
        }
        ObjWellDefinedProofByDef::FunctionSpace(
            FunctionSpaceObjWellDefinedProofByDef::Preimage(p),
        ) => project_preimage_wd(
            obj,
            "Preimage",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            &p.construction,
            runtime,
        ),
        ObjWellDefinedProofByDef::FunctionSpace(
            FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p),
        ) => project_preimage_wd(
            obj,
            "PreimageSet",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            &p.construction,
            runtime,
        ),
        ObjWellDefinedProofByDef::FunctionSpace(
            FunctionSpaceObjWellDefinedProofByDef::FnRange(p),
        ) => object_for(
            runtime,
            vec![
                ("type", string("by_def")),
                ("family", string("FunctionSpace")),
                ("kind", string("FnRange")),
                ("obj", string(obj.readable_string())),
                (
                    "child_obj_well_defined",
                    JsonValue::Array(
                        p.child_obj_well_defined
                            .iter()
                            .map(|proof| project_obj_wd_proof(proof, runtime))
                            .collect(),
                    ),
                ),
                (
                    "requirement_fact_verified",
                    project_verify_facts(&p.requirement_fact_verified, runtime),
                ),
                (
                    "source",
                    JsonValue::Array(
                        p.function_domains
                            .iter()
                            .map(|proof| super::function_domain::project_source(proof, runtime))
                            .collect(),
                    ),
                ),
            ],
        ),
        ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
            p,
        )) => object_for(
            runtime,
            vec![
                ("type", string("by_def")),
                ("family", string("FunctionSpace")),
                ("kind", string("FnSet")),
                ("obj", string(obj.readable_string())),
                (
                    "param_type_well_defined",
                    JsonValue::Array(
                        p.param_type_well_defined
                            .iter()
                            .map(|c| project_obj_wd_proof(c, runtime))
                            .collect(),
                    ),
                ),
                (
                    "dom_fact_well_defined",
                    JsonValue::Array(
                        p.dom_fact_well_defined
                            .iter()
                            .map(|f| project_fact_wd_proof(f, runtime))
                            .collect(),
                    ),
                ),
                (
                    "ret_set_well_defined",
                    project_obj_wd_proof(&p.ret_set_well_defined, runtime),
                ),
            ],
        ),
        ObjWellDefinedProofByDef::Identifier(p) => {
            let _ = p;
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("Identifier")),
                    ("kind", string("Identifier")),
                    ("obj", string(obj.readable_string())),
                ],
            )
        }
        ObjWellDefinedProofByDef::InstantiatedTemplateObj(p) => project_common_by_def(
            obj,
            "InstantiatedTemplateObj",
            "InstantiatedTemplateObj",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IntegerOperator(
            IntegerOperatorObjWellDefinedProofByDef::Factorial(p),
        ) => project_common_by_def(
            obj,
            "IntegerOperator",
            "Factorial",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IntegerOperator(
            IntegerOperatorObjWellDefinedProofByDef::Gcd(p),
        ) => project_common_by_def(
            obj,
            "IntegerOperator",
            "Gcd",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IntegerOperator(
            IntegerOperatorObjWellDefinedProofByDef::Lcm(p),
        ) => project_common_by_def(
            obj,
            "IntegerOperator",
            "Lcm",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IntegerOperator(
            IntegerOperatorObjWellDefinedProofByDef::Mod(p),
        ) => project_common_by_def(
            obj,
            "IntegerOperator",
            "Mod",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IntegerOperator(
            IntegerOperatorObjWellDefinedProofByDef::Quot(p),
        ) => project_common_by_def(
            obj,
            "IntegerOperator",
            "Quot",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IteratedOperator(
            IteratedOperatorObjWellDefinedProofByDef::FiniteSetReduce(p),
        ) => project_common_by_def(
            obj,
            "IteratedOperator",
            "FiniteSetReduce",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IteratedOperator(
            IteratedOperatorObjWellDefinedProofByDef::Product(p),
        ) => project_common_by_def(
            obj,
            "IteratedOperator",
            "Product",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IteratedOperator(
            IteratedOperatorObjWellDefinedProofByDef::ProductOfFiniteSet(p),
        ) => project_common_by_def(
            obj,
            "IteratedOperator",
            "ProductOfFiniteSet",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IteratedOperator(
            IteratedOperatorObjWellDefinedProofByDef::Reduce(p),
        ) => project_common_by_def(
            obj,
            "IteratedOperator",
            "Reduce",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IteratedOperator(
            IteratedOperatorObjWellDefinedProofByDef::Sum(p),
        ) => project_common_by_def(
            obj,
            "IteratedOperator",
            "Sum",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::IteratedOperator(
            IteratedOperatorObjWellDefinedProofByDef::SumOfFiniteSet(p),
        ) => project_common_by_def(
            obj,
            "IteratedOperator",
            "SumOfFiniteSet",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::EulerNumber(p)) => {
            let _ = p;
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("Literal")),
                    ("kind", string("EulerNumber")),
                    ("obj", string(obj.readable_string())),
                ],
            )
        }
        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::ImaginaryUnit(p)) => {
            let _ = p;
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("Literal")),
                    ("kind", string("ImaginaryUnit")),
                    ("obj", string(obj.readable_string())),
                ],
            )
        }
        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(p)) => {
            let _ = p;
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("Literal")),
                    ("kind", string("Number")),
                    ("obj", string(obj.readable_string())),
                ],
            )
        }
        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Pi(p)) => {
            let _ = p;
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("Literal")),
                    ("kind", string("Pi")),
                    ("obj", string(obj.readable_string())),
                ],
            )
        }
        ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Cart(p)) => {
            project_common_by_def(
                obj,
                "ProductShape",
                "Cart",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Tuple(p)) => {
            project_common_by_def(
                obj,
                "ProductShape",
                "Tuple",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ClosedRange(p)) => {
            project_common_by_def(
                obj,
                "SetFormer",
                "ClosedRange",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(p)) => {
            project_common_by_def(
                obj,
                "SetFormer",
                "FiniteSeqSet",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::IntervalObj(p)) => {
            project_common_by_def(
                obj,
                "SetFormer",
                "IntervalObj",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ListSet(p)) => {
            project_common_by_def(
                obj,
                "SetFormer",
                "ListSet",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(
            SetFormerObjWellDefinedProofByDef::OneSideInfinityIntervalObj(p),
        ) => project_common_by_def(
            obj,
            "SetFormer",
            "OneSideInfinityIntervalObj",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::Range(p)) => {
            project_common_by_def(
                obj,
                "SetFormer",
                "Range",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SeqSet(p)) => {
            project_common_by_def(
                obj,
                "SetFormer",
                "SeqSet",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(p)) => {
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("SetFormer")),
                    ("kind", string("SetBuilder")),
                    ("obj", string(obj.readable_string())),
                    (
                        "param_set_well_defined",
                        project_obj_wd_proof(&p.param_set_well_defined, runtime),
                    ),
                    (
                        "fact_well_defined",
                        JsonValue::Array(
                            p.fact_well_defined
                                .iter()
                                .map(|f| project_fact_wd_proof(f, runtime))
                                .collect(),
                        ),
                    ),
                ],
            )
        }
        ObjWellDefinedProofByDef::SetOperator(
            SetOperatorObjWellDefinedProofByDef::FamilyIntersect(p),
        ) => project_common_by_def(
            obj,
            "SetOperator",
            "FamilyIntersect",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetOperator(
            SetOperatorObjWellDefinedProofByDef::FamilyUnion(p),
        ) => project_common_by_def(
            obj,
            "SetOperator",
            "FamilyUnion",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexCart(
            p,
        )) => project_common_by_def(
            obj,
            "SetOperator",
            "IndexCart",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetOperator(
            SetOperatorObjWellDefinedProofByDef::IndexIntersect(p),
        ) => project_common_by_def(
            obj,
            "SetOperator",
            "IndexIntersect",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexUnion(
            p,
        )) => project_common_by_def(
            obj,
            "SetOperator",
            "IndexUnion",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::Intersect(
            p,
        )) => project_common_by_def(
            obj,
            "SetOperator",
            "Intersect",
            &p.child_obj_well_defined,
            &p.requirement_fact_verified,
            runtime,
        ),
        ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::PowerSet(p)) => {
            project_common_by_def(
                obj,
                "SetOperator",
                "PowerSet",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::SetMinus(p)) => {
            project_common_by_def(
                obj,
                "SetOperator",
                "SetMinus",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::Union(p)) => {
            project_common_by_def(
                obj,
                "SetOperator",
                "Union",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::StandardSet(p) => {
            let _ = p;
            object_for(
                runtime,
                vec![
                    ("type", string("by_def")),
                    ("family", string("StandardSet")),
                    ("kind", string("StandardSet")),
                    ("obj", string(obj.readable_string())),
                ],
            )
        }
        ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(p)) => {
            project_common_by_def(
                obj,
                "Structish",
                "FieldAccess",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(p)) => {
            project_common_by_def(
                obj,
                "Structish",
                "StructObj",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arccos(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Arccos",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arccot(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Arccot",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arcsin(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Arcsin",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arctan(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Arctan",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Cos(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Cos",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Cot(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Cot",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Sin(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Sin",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
        ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Tan(p)) => {
            project_common_by_def(
                obj,
                "TrigOperator",
                "Tan",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                runtime,
            )
        }
    }
}

pub(super) fn project_preimage_construction(
    proof: &crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "source",
                super::function_domain::project_source(&proof.source, runtime),
            ),
            (
                "bounded_subset",
                string(
                    Obj::SetFormer(crate::ast::obj::SetFormer::SetBuilder(
                        proof.builder.clone(),
                    ))
                    .readable_string(),
                ),
            ),
            (
                "builder_well_defined",
                project_obj_wd_proof(&proof.builder_well_defined, runtime),
            ),
        ],
    )
}

fn project_preimage_wd(
    obj: &Obj,
    kind: &str,
    children: &[Box<ObjWellDefinedProof>],
    requirements: &[crate::execute::execute_fact_stmt::VerifyFactResult],
    construction: &crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("type", string("by_def")),
            ("family", string("FunctionSpace")),
            ("kind", string(kind)),
            ("obj", string(obj.readable_string())),
            (
                "child_obj_well_defined",
                JsonValue::Array(
                    children
                        .iter()
                        .map(|proof| project_obj_wd_proof(proof, runtime))
                        .collect(),
                ),
            ),
            (
                "requirement_fact_verified",
                project_verify_facts(requirements, runtime),
            ),
            (
                "construction",
                project_preimage_construction(construction, runtime),
            ),
        ],
    )
}
