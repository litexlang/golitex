use crate::prelude::*;

pub(super) fn impossible_proof_error_message(
    impossible_fact: &AtomicFact,
    option_case_fact_string: Option<String>,
) -> String {
    match option_case_fact_string {
        Some(case_fact) => format!(
            "failed to prove impossible `{}` under case `{}`",
            impossible_fact, case_fact
        ),
        None => format!("failed to prove impossible `{}`", impossible_fact),
    }
}
