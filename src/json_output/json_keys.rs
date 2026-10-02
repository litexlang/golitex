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
        "evaluated_object" => "求值结果",
        "aggregate_evaluations" => "聚合计算",
        "function_evaluations" => "函数计算",
        "algo_evaluations" => "算法计算",
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
        "source_fact_id" => "来源命题编号",
        "definition_facts" => "定义事实",
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
        // Native theorem contracts and calculation / alpha evidence.
        "theorem" | "thm_name" => "定理名",
        "builtin" => "内置接口",
        "arguments" => "实参",
        "requirements" => "所需前提",
        "conclusions" => "结论",
        "provenance" => "来源",
        "type_proofs" => "参数类型证明",
        "dom_proofs" => "前提证明",
        "conclusions_wd" => "结论良定性",
        "expected" => "预期",
        "actual" => "实际",
        "index" => "下标",
        "mode" => "计算模式",
        "left_identity" => "左端同一性",
        "right_identity" => "右端同一性",
        "reversed" => "反向",
        // fallback: keep English so unknown keys still work
        other => other,
    }
}
