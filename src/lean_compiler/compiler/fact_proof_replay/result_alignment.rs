//! Anonymous-function beta-normalized alignment for frozen proof results.

use super::super::*;

pub(in super::super) fn facts_align_by_anonymous_function_beta_normalization_for_result_compiler(
    source: &Fact,
    target: &Fact,
) -> Result<bool, String> {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return Ok(false);
    };
    if source.key() != target.key()
        || source.has_positive_polarity() != target.has_positive_polarity()
    {
        return Ok(false);
    }
    let source_args = source.args_ref();
    let target_args = target.args_ref();
    if source_args.len() != target_args.len() {
        return Ok(false);
    }
    let runtime = Runtime::default();
    for (source, target) in source_args.iter().zip(target_args.iter()) {
        if !objs_align_by_anonymous_function_beta_normalization_for_result_compiler(
            &runtime, source, target,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(in super::super) fn objs_align_by_anonymous_function_beta_normalization_for_result_compiler(
    runtime: &Runtime,
    source: &Obj,
    target: &Obj,
) -> Result<bool, String> {
    if objs_equal_with_nested_binder_alpha_equivalence(source, target) {
        return Ok(true);
    }
    if let Some(reduced) = runtime
        .beta_reduce_complete_anonymous_application_once(target)
        .map_err(|error| error.trace_message())?
    {
        if objs_align_by_anonymous_function_beta_normalization_for_result_compiler(
            runtime, source, &reduced,
        )? {
            return Ok(true);
        }
    }
    Runtime::same_shape_and_corresponding_args_match(source, target, &mut |source, target| {
        objs_align_by_anonymous_function_beta_normalization_for_result_compiler(
            runtime, source, target,
        )
    })
}
