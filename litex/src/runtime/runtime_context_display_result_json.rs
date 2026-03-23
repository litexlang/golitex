use super::RuntimeContext;
use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::common::keywords::UNKNOWN_COLON;
use crate::result::NonErrStmtExecResult;

pub fn display_result_json_string(
    runtime_context: &RuntimeContext<'_>,
    result: &NonErrStmtExecResult,
) -> String {
    build_display_result_json_pretty(runtime_context, result, 0)
}

fn json_one_level_indent(unit_count: usize) -> String {
    let mut indent = String::new();
    for _ in 0..unit_count {
        indent.push_str("  ");
    }
    indent
}

fn json_string_literal(source_text: &str) -> String {
    let mut output = String::with_capacity(source_text.len() + 2);
    output.push('"');
    for ch in source_text.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            c if (c as u32) < 32 => {
                output.push_str(format!("\\u{:04x}", c as u32).as_str());
            }
            c => output.push(c),
        }
    }
    output.push('"');
    output
}

fn build_display_result_json_pretty(
    runtime_context: &RuntimeContext<'_>,
    result: &NonErrStmtExecResult,
    depth: usize,
) -> String {
    match result {
        NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_stmt_success_result) => {
            display_non_factual_stmt_success_json(
                runtime_context,
                non_factual_stmt_success_result,
                depth,
            )
        }
        NonErrStmtExecResult::FactVerifiedByFact(fact_verified_by_fact_result) => {
            display_fact_verified_by_fact_json(runtime_context, fact_verified_by_fact_result, depth)
        }
        NonErrStmtExecResult::FactVerifiedByBuiltinRules(fact_verified_by_builtin_rules_result) => {
            display_fact_verified_by_builtin_rules_json(
                runtime_context,
                fact_verified_by_builtin_rules_result,
                depth,
            )
        }
        NonErrStmtExecResult::StmtUnknown(_stmt_unknown_result) => display_stmt_unknown_json(depth),
    }
}

fn display_non_factual_stmt_success_json(
    runtime_context: &RuntimeContext<'_>,
    non_factual_stmt_success_result: &crate::result::NonFactualStmtSuccess,
    depth: usize,
) -> String {
    let indent_outer = json_one_level_indent(depth);
    let indent_inner = json_one_level_indent(depth + 1);
    let infer_block_formatted =
        RuntimeContext::format_infer_block(&non_factual_stmt_success_result.infers);
    let inside_results_plain_text_block = runtime_context
        .format_inside_results_block(&non_factual_stmt_success_result.inside_results);

    let mut field_lines: Vec<String> = Vec::new();
    field_lines.push(format!(
        "{}\"type\": {}",
        indent_inner,
        json_string_literal("non_factual_stmt_success")
    ));
    field_lines.push(format!(
        "{}\"stmt_type\": {}",
        indent_inner,
        json_string_literal("stmt")
    ));
    field_lines.push(format!(
        "{}\"line\": {}",
        indent_inner, non_factual_stmt_success_result.line_file.0
    ));
    field_lines.push(format!(
        "{}\"source\": {}",
        indent_inner,
        json_string_literal(
            runtime_context
                .module_manager
                .run_file_paths
                .get(non_factual_stmt_success_result.line_file.1)
                .unwrap_or(&String::new())
        )
    ));
    field_lines.push(format!(
        "{}\"location_display\": {}",
        indent_inner,
        json_string_literal(
            runtime_context
                .format_line_file(
                    non_factual_stmt_success_result.line_file.0,
                    non_factual_stmt_success_result.line_file.1
                )
                .as_str(),
        )
    ));
    field_lines.push(format!(
        "{}\"stmt\": {}",
        indent_inner,
        json_string_literal(&non_factual_stmt_success_result.stmt)
    ));

    let infer_indent = json_one_level_indent(depth + 2);
    let mut infer_elements: Vec<String> = Vec::new();
    for infer_fact in non_factual_stmt_success_result.infers.infer_facts.iter() {
        infer_elements.push(format!(
            "{}{}",
            infer_indent,
            json_string_literal(infer_fact.as_str())
        ));
    }
    let infer_facts_joined = infer_elements.join(",\n");
    field_lines.push(format!(
        "{}\"infer_facts\": [\n{}\n{}]",
        indent_inner, infer_facts_joined, indent_inner
    ));

    field_lines.push(format!(
        "{}\"infer_block_formatted\": {}",
        indent_inner,
        json_string_literal(&infer_block_formatted)
    ));
    field_lines.push(format!(
        "{}\"inside_results_plain_text_block\": {}",
        indent_inner,
        json_string_literal(&inside_results_plain_text_block)
    ));

    let mut inside_elements: Vec<String> = Vec::new();
    for inside_result in non_factual_stmt_success_result.inside_results.iter() {
        let nested_json =
            build_display_result_json_pretty(runtime_context, inside_result, depth + 2);
        inside_elements.push(nested_json);
    }
    let inside_joined = inside_elements.join(",\n");
    field_lines.push(format!(
        "{}\"inside_results\": [\n{}\n{}]",
        indent_inner, inside_joined, indent_inner
    ));

    format!("{{\n{}\n{}}}", field_lines.join(",\n"), indent_outer)
}

fn display_fact_verified_by_fact_json(
    runtime_context: &RuntimeContext<'_>,
    fact_verified_by_fact_result: &crate::result::FactVerifiedByFact,
    depth: usize,
) -> String {
    let indent_outer = json_one_level_indent(depth);
    let indent_inner = json_one_level_indent(depth + 1);
    let verified_by_reference_suffix =
        if fact_verified_by_fact_result.verified_by_line_file == DEFAULT_LINE_FILE {
            String::new()
        } else {
            format!(
                "fact known/verified/inferred {}",
                runtime_context.format_line_file(
                    fact_verified_by_fact_result.verified_by_line_file.0,
                    fact_verified_by_fact_result.verified_by_line_file.1,
                )
            )
        };

    let mut field_lines: Vec<String> = Vec::new();
    field_lines.push(format!(
        "{}\"type\": {}",
        indent_inner,
        json_string_literal("fact_verified_by_fact")
    ));
    field_lines.push(format!(
        "{}\"stmt_type\": {}",
        indent_inner,
        json_string_literal("fact")
    ));
    field_lines.push(format!(
        "{}\"line\": {}",
        indent_inner, fact_verified_by_fact_result.line_file.0
    ));
    field_lines.push(format!(
        "{}\"source\": {}",
        indent_inner,
        json_string_literal(
            runtime_context
                .module_manager
                .run_file_paths
                .get(fact_verified_by_fact_result.line_file.1)
                .unwrap_or(&String::new())
        )
    ));
    field_lines.push(format!(
        "{}\"fact\": {}",
        indent_inner,
        json_string_literal(&fact_verified_by_fact_result.fact)
    ));
    field_lines.push(format!(
        "{}\"verified_by_reference_suffix\": {}",
        indent_inner,
        json_string_literal(&verified_by_reference_suffix)
    ));
    field_lines.push(format!(
        "{}\"verified_by_line\": {}",
        indent_inner, fact_verified_by_fact_result.verified_by_line_file.0
    ));
    field_lines.push(format!(
        "{}\"verified_by_file_index\": {}",
        indent_inner, fact_verified_by_fact_result.verified_by_line_file.1
    ));
    field_lines.push(format!(
        "{}\"verified_by_location_display\": {}",
        indent_inner,
        json_string_literal(
            runtime_context
                .format_line_file(
                    fact_verified_by_fact_result.verified_by_line_file.0,
                    fact_verified_by_fact_result.verified_by_line_file.1,
                )
                .as_str(),
        )
    ));
    field_lines.push(format!(
        "{}\"verified_by\": {}",
        indent_inner,
        json_string_literal(&fact_verified_by_fact_result.verified_by)
    ));

    let infer_indent = json_one_level_indent(depth + 2);
    let mut infer_elements: Vec<String> = Vec::new();
    for infer_fact in fact_verified_by_fact_result.infers.infer_facts.iter() {
        infer_elements.push(format!(
            "{}{}",
            infer_indent,
            json_string_literal(infer_fact.as_str())
        ));
    }
    let infer_facts_joined = infer_elements.join(",\n");
    field_lines.push(format!(
        "{}\"infer_facts\": [\n{}\n{}]",
        indent_inner, infer_facts_joined, indent_inner
    ));
    format!("{{\n{}\n{}}}", field_lines.join(",\n"), indent_outer)
}

fn display_fact_verified_by_builtin_rules_json(
    runtime_context: &RuntimeContext<'_>,
    fact_verified_by_builtin_rules_result: &crate::result::FactVerifiedByBuiltinRules,
    depth: usize,
) -> String {
    let indent_outer = json_one_level_indent(depth);
    let indent_inner = json_one_level_indent(depth + 1);
    let mut field_lines: Vec<String> = Vec::new();
    field_lines.push(format!(
        "{}\"type\": {}",
        indent_inner,
        json_string_literal("fact_verified_by_builtin_rules")
    ));
    field_lines.push(format!(
        "{}\"stmt_type\": {}",
        indent_inner,
        json_string_literal("fact")
    ));
    field_lines.push(format!(
        "{}\"line\": {}",
        indent_inner, fact_verified_by_builtin_rules_result.line_file.0
    ));
    field_lines.push(format!(
        "{}\"source\": {}",
        indent_inner,
        json_string_literal(
            match runtime_context
                .module_manager
                .run_file_paths
                .get(fact_verified_by_builtin_rules_result.line_file.1)
            {
                Some(source_path) => source_path,
                None => "",
            }
        )
    ));
    field_lines.push(format!(
        "{}\"fact\": {}",
        indent_inner,
        json_string_literal(&fact_verified_by_builtin_rules_result.fact)
    ));
    field_lines.push(format!(
        "{}\"verified_by\": {}",
        indent_inner,
        json_string_literal(&fact_verified_by_builtin_rules_result.verified_by)
    ));

    let infer_indent = json_one_level_indent(depth + 2);
    let mut infer_elements: Vec<String> = Vec::new();
    for infer_fact in fact_verified_by_builtin_rules_result
        .infers
        .infer_facts
        .iter()
    {
        infer_elements.push(format!(
            "{}{}",
            infer_indent,
            json_string_literal(infer_fact.as_str())
        ));
    }
    let infer_facts_joined = infer_elements.join(",\n");
    field_lines.push(format!(
        "{}\"infer_facts\": [\n{}\n{}]",
        indent_inner, infer_facts_joined, indent_inner
    ));

    format!("{{\n{}\n{}}}", field_lines.join(",\n"), indent_outer)
}

fn display_stmt_unknown_json(depth: usize) -> String {
    let indent_outer = json_one_level_indent(depth);
    let indent_inner = json_one_level_indent(depth + 1);
    let mut field_lines: Vec<String> = Vec::new();
    field_lines.push(format!(
        "{}\"kind\": {}",
        indent_inner,
        json_string_literal("stmt_unknown")
    ));
    field_lines.push(format!(
        "{}\"message\": {}",
        indent_inner,
        json_string_literal(UNKNOWN_COLON)
    ));
    format!("{{\n{}\n{}}}", field_lines.join(",\n"), indent_outer)
}
