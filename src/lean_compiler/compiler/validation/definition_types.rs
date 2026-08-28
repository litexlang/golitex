//! Compiler definition object-type facts.

use super::super::*;

pub(in super::super) fn object_type_fact_for_compiler_definition(
    object: Obj,
    param_type: &ParamType,
    line_file: LineFile,
) -> Fact {
    match param_type {
        ParamType::Set(_) => IsSetFact::new(object, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(object, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(object, line_file).into(),
        ParamType::Obj(set) => InFact::new(object, set.clone(), line_file).into(),
    }
}
