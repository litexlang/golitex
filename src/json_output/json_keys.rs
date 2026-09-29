//! Localized JSON field names for Normal output.
//!
//! Code always authors English keys; `localize_key` remaps them when
//! `OutputLanguage::Chinese`. Type *values* (e.g. `builtin_rule`) stay English
//! stable tokens unless a dedicated value map is added later.

use crate::launch_command::OutputLanguage;

pub fn localize_key(english_key: &str, lang: OutputLanguage) -> String {
    match lang {
        OutputLanguage::English => english_key.to_string(),
        OutputLanguage::Chinese => chinese_key(english_key).to_string(),
    }
}

fn chinese_key(english_key: &str) -> &str {
    match english_key {
        // run envelope
        "kind" => "种类",
        "success" => "成功",
        "ok" => "成功",
        "target" => "目标",
        "path" => "路径",
        "detail" => "详细度",
        "language" => "语言",
        "statement_results" => "语句结果",
        "session_error" => "会话错误",
        // statement result
        "statement" => "语句",
        "why_verified" => "证明方法",
        "why_failed" => "失败原因",
        "stores" => "存储",
        "infers" => "推断",
        // why / cite
        "type" => "类型",
        "rule_name" => "规则名",
        "message" => "说明",
        "cite" => "引用",
        "line" => "行号",
        "phase" => "阶段",
        "goal" => "目标命题",
        "family" => "族",
        // fallback: keep English so unknown keys still work
        other => other,
    }
}
