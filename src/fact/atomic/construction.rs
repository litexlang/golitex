//! Atomic fact construction from predicate syntax.

use crate::prelude::*;
impl AtomicFact {
    pub fn to_atomic_fact(
        runtime: &Runtime,
        prop_name: AtomicName,
        positive_polarity: bool,
        args: Vec<Obj>,
        line_file: LineFile,
    ) -> Result<AtomicFact, RuntimeError> {
        let prop_name_as_string = prop_name.to_string();
        match prop_name_as_string.as_str() {
            EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", EQUAL, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_equal_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_equal_fact(a0, a1, line_file).into())
                }
            }
            NOT_EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", NOT_EQUAL, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_not_equal_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_equal_fact(a0, a1, line_file).into())
                }
            }
            LESS => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", LESS, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_less_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_less_fact(a0, a1, line_file).into())
                }
            }
            GREATER => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", GREATER, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_greater_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_greater_fact(a0, a1, line_file).into())
                }
            }
            LESS_EQUAL => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        LESS_EQUAL,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_less_equal_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_less_equal_fact(a0, a1, line_file).into())
                }
            }
            GREATER_EQUAL => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        GREATER_EQUAL,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_greater_equal_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_greater_equal_fact(a0, a1, line_file).into())
                }
            }
            IS_SET => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_SET, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_is_set_fact(a0, line_file).into())
                } else {
                    Ok(runtime.new_not_is_set_fact(a0, line_file).into())
                }
            }
            IS_NONEMPTY_SET => {
                if args.len() != 1 {
                    let msg = format!(
                        "{} requires 1 argument, but got {}",
                        IS_NONEMPTY_SET,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_is_nonempty_set_fact(a0, line_file).into())
                } else {
                    Ok(runtime.new_not_is_nonempty_set_fact(a0, line_file).into())
                }
            }
            IS_FINITE_SET => {
                if args.len() != 1 {
                    let msg = format!(
                        "{} requires 1 argument, but got {}",
                        IS_FINITE_SET,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_is_finite_set_fact(a0, line_file).into())
                } else {
                    Ok(runtime.new_not_is_finite_set_fact(a0, line_file).into())
                }
            }
            IN => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", IN, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_in_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_in_fact(a0, a1, line_file).into())
                }
            }
            IS_CART => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_CART, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_is_cart_fact(a0, line_file).into())
                } else {
                    Ok(runtime.new_not_is_cart_fact(a0, line_file).into())
                }
            }
            IS_TUPLE => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_TUPLE, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_is_tuple_fact(a0, line_file).into())
                } else {
                    Ok(runtime.new_not_is_tuple_fact(a0, line_file).into())
                }
            }
            SUBSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUBSET, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_subset_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_subset_fact(a0, a1, line_file).into())
                }
            }
            SUPERSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUPERSET, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if positive_polarity {
                    Ok(runtime.new_superset_fact(a0, a1, line_file).into())
                } else {
                    Ok(runtime.new_not_superset_fact(a0, a1, line_file).into())
                }
            }
            FN_EQ_IN => {
                if !positive_polarity {
                    let msg = format!("{} does not support `not`", FN_EQ_IN);
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                if args.len() != 3 {
                    let msg = format!(
                        "{} requires 3 arguments (f, g, set), but got {}",
                        FN_EQ_IN,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                let a2 = args.remove(0);
                Ok(runtime.new_fn_equal_in_fact(a0, a1, a2, line_file).into())
            }
            FN_EQ => {
                if !positive_polarity {
                    let msg = format!("{} does not support `not`", FN_EQ);
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments (f, g), but got {}",
                        FN_EQ,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                Ok(runtime.new_fn_equal_fact(a0, a1, line_file).into())
            }
            _ => {
                if positive_polarity {
                    Ok(runtime
                        .new_normal_atomic_fact(prop_name, args, line_file)
                        .into())
                } else {
                    Ok(runtime
                        .new_not_normal_atomic_fact(prop_name, args, line_file)
                        .into())
                }
            }
        }
    }
}
