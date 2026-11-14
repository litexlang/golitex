//! The selected native entry expansions and the actual scalar verification.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::matrix_entry_normalization_proof::*;
use crate::prelude::*;
use crate::json_output::helper::{object_for,string};

pub(super) fn normalization(p: &MatrixEntryNormalizationProof, rt: &Runtime) -> JsonValue {
    let (kind, children) = match &p.step {
        MatrixEntryNormalizationStep::Unchanged => ("unchanged", vec![]),
        MatrixEntryNormalizationStep::NativeCall(call) => (
            "native_call",
            vec![
                (
                    "callable",
                    super::native_matrix::callable(&call.callable, rt),
                ),
                ("body", string(call.body.readable_string())),
                ("continuation", normalization(&call.continuation, rt)),
            ],
        ),
        MatrixEntryNormalizationStep::Add(a, b) => (
            "add",
            vec![
                ("left", normalization(a, rt)),
                ("right", normalization(b, rt)),
            ],
        ),
        MatrixEntryNormalizationStep::Subtract(a, b) => (
            "subtract",
            vec![
                ("left", normalization(a, rt)),
                ("right", normalization(b, rt)),
            ],
        ),
        MatrixEntryNormalizationStep::Multiply(a, b) => (
            "multiply",
            vec![
                ("left", normalization(a, rt)),
                ("right", normalization(b, rt)),
            ],
        ),
        MatrixEntryNormalizationStep::Conjugate(a) => {
            ("conjugate", vec![("argument", normalization(a, rt))])
        }
    };
    let mut fields = vec![
        ("step", string(kind)),
        (
            "source_wd",
            super::wd::project_obj_wd_proof(&p.source_wd, rt),
        ),
        ("value", string(p.value.readable_string())),
    ];
    fields.extend(children);
    object_for(rt, fields)
}
