//! Compiler definition object-type facts.

use super::super::*;

pub(in super::super) fn object_type_fact_for_compiler_definition(
    runtime: &Runtime,
    object: Obj,
    param_type: &ParamType,
    line_file: LineFile,
) -> Fact {
    match param_type {
        ParamType::Set(_) => runtime.new_is_set_fact(object, line_file).into(),
        ParamType::NonemptySet(_) => runtime.new_is_nonempty_set_fact(object, line_file).into(),
        ParamType::FiniteSet(_) => runtime.new_is_finite_set_fact(object, line_file).into(),
        ParamType::Obj(set) => runtime.new_in_fact(object, set.clone(), line_file).into(),
    }
}
