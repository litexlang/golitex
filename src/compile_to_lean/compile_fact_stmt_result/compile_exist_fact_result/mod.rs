mod compile_exist_builtin_result;
mod compile_exist_formation;
mod compile_exist_known_forall;
mod compile_exist_unique_result;
mod compile_not_exist_result;
mod compile_verify_exist_result;
mod helper;
pub(in crate::compile_to_lean) use helper::exist_instance_matches;

#[cfg(test)]
#[path = "../../../../tests/unit/compile_to_lean/exist_formation/tests.rs"]
mod exist_formation_tests;
