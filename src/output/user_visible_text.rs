pub const JSON_KEY_RESULT: &str = "result";
pub const JSON_KEY_ERROR_TYPE: &str = "error_type";
pub const JSON_KEY_MESSAGE: &str = "message";
pub const JSON_KEY_LINE: &str = "line";
pub const JSON_KEY_SOURCE: &str = "source";
pub const JSON_KEY_STMT_TYPE: &str = "type";
pub const JSON_KEY_STMT: &str = "statement";
pub const JSON_KEY_INSIDE_RESULTS: &str = "inside_results";
pub const JSON_KEY_PREVIOUS_ERROR: &str = "previous_error";
pub const JSON_KEY_FAILED_STEP: &str = "failed_step";
pub const JSON_KEY_FAILED_GOAL: &str = "failed_goal";
pub const JSON_KEY_UNKNOWN_RESULT: &str = "unknown_result";
pub const JSON_VALUE_ERROR: &str = "error";

pub fn user_visible_stmt_or_msg_text(raw: &str) -> String {
    raw.to_string()
}
