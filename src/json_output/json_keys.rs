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
        // Induction stage/evidence fields
        "failure" => "失败详情",
        "result" => "结果",
        "goal_index" => "目标索引",
        "step_index" => "证明步骤索引",
        "case_index" => "分支索引",
        "left_case_index" => "左分支索引",
        "right_case_index" => "右分支索引",
        "from_in_z" => "起点整数证明",
        "goal_domain_stored" => "归纳域假设",
        "goals_wd" => "目标良定性",
        "body" => "证明体",
        "base" => "基例",
        "step" => "归纳步",
        "form" => "形式",
        "assumptions_stored" | "assumption_stored" => "存入假设",
        "proof_steps" => "证明步骤",
        "goals_verified" => "目标证明",
        "stored" => "已存入",
        "fn_set_well_defined" => "函数类型良定性",
        "measure_in_z" => "度量整数证明",
        "lower_in_z" => "下界整数证明",
        "measure_ge_lower" => "度量下界证明",
        "case_checks" => "分支检查",
        "coverage" => "覆盖证明",
        "disjoint" => "互斥证明",
        "cases" => "分支",
        "negated_component" => "否定条件证明",
        "in_ret_set" => "返回类型证明",
        // fallback: keep English so unknown keys still work
        other => other,
    }
}
