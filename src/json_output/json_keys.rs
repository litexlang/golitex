//! Localized JSON field names for Normal / Compact output.
//!
//! Code always authors English keys; `localize_key` remaps them when
//! `OutputLanguage::Chinese`. Type / phase *values* are localized by explain
//! / helper match arms (not here).

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
        "shape" => "形状",
        "left_path" => "左侧路径",
        "bridge" => "连接证明",
        "right_path" => "右侧路径",
        "why_parameters_of_known_fact_are_equal_to_givens" => "已知事实参数与目标参数相等的证明",
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
        "proof_method" => "证明方法",
        "why_failed" => "失败原因",
        "fail_reason" => "失败原因",
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
        // Detailed IR fields
        "verify" => "验证",
        "store_and_infer" => "存储与推理",
        "fact" => "命题",
        "fact_id" => "命题编号",
        "well_defined" => "良定性",
        "searched_proof" => "搜索证明",
        "rule" => "规则",
        // fallback: keep English so unknown keys still work
        other => other,
    }
}
