//! Nested rational-normalization alignment.

use super::super::*;

pub(in super::super) fn facts_align_by_nested_rational_normalization_for_result_compiler(
    source: &Fact,
    target: &Fact,
) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return false;
    };
    if source.key() != target.key()
        || source.has_positive_polarity() != target.has_positive_polarity()
    {
        return false;
    }
    let source_arguments = source.args_ref();
    let target_arguments = target.args_ref();
    source_arguments.len() == target_arguments.len()
        && source_arguments
            .iter()
            .zip(target_arguments.iter())
            .all(|(source, target)| {
                objects_align_by_nested_rational_normalization_for_result_compiler(source, target)
            })
}

pub(in super::super) fn objects_align_by_nested_rational_normalization_for_result_compiler(
    source: &Obj,
    target: &Obj,
) -> bool {
    if objs_equal_by_rational_expression_evaluation(source, target) {
        return true;
    }
    let comparison: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
        source,
        target,
        &mut |source_argument, target_argument| {
            Ok(
                objects_align_by_nested_rational_normalization_for_result_compiler(
                    source_argument,
                    target_argument,
                ),
            )
        },
    );
    comparison.unwrap_or(false)
}
