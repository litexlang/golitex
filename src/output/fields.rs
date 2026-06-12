pub(crate) const JSON_KEY_RESULT: &str = "result";
pub(crate) const JSON_KEY_SUCCESS: &str = "success";
pub(crate) const JSON_KEY_EFFECTS: &str = "effects";
pub(crate) const JSON_KEY_VERIFICATION: &str = "verification";
pub(crate) const JSON_KEY_CONCLUSIONS_WITH_VERIFICATION: &str = "conclusions_with_verification";
pub(crate) const JSON_KEY_STEPS: &str = "steps";

pub(crate) const JSON_KEY_ERROR_TYPE: &str = "error_type";
pub(crate) const JSON_KEY_MESSAGE: &str = "message";
pub(crate) const JSON_KEY_LINE: &str = "line";
pub(crate) const JSON_KEY_SOURCE: &str = "source";
pub(crate) const JSON_KEY_STMT_TYPE: &str = "type";
pub(crate) const JSON_KEY_STMT: &str = "statement";
pub(crate) const JSON_KEY_INSIDE_RESULTS: &str = "inside_results";
pub(crate) const JSON_KEY_PREVIOUS_ERROR: &str = "previous_error";
pub(crate) const JSON_KEY_FAILED_STEP: &str = "failed_step";
pub(crate) const JSON_KEY_FAILED_GOAL: &str = "failed_goal";
pub(crate) const JSON_KEY_UNKNOWN_RESULT: &str = "unknown_result";
pub(crate) const JSON_VALUE_ERROR: &str = "error";

pub(crate) fn user_visible_stmt_or_msg_text(raw: &str) -> String {
    raw.to_string()
}
