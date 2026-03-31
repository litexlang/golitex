use crate::prelude::*;

const JSON_KEY_RESULT: &str = "result";
const JSON_KEY_SUCCESS: &str = "success";
const JSON_KEY_VERIFIED_BY_BUILTIN_RULE: &str = "verified_by_builtin_rule";
const JSON_KEY_VERIFIED_BY_KNOWN_FACT: &str = "verified_by_known_fact";
const JSON_KEY_INFER_FACTS: &str = "infer_facts";
const JSON_KEY_SOURCE: &str = "source";

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

fn json_array_field_line(
    indent_inner: &str,
    json_key: &str,
    json_elements: &Vec<String>,
) -> String {
    if json_elements.is_empty() {
        format!("{}\"{}\": []", indent_inner, json_key)
    } else {
        let joined_elements = json_elements.join(",\n");
        format!(
            "{}\"{}\": [\n{}\n{}]",
            indent_inner, json_key, joined_elements, indent_inner
        )
    }
}

impl Runtime {
    pub fn display_result_json_string(&self, result: &NonErrStmtExecResult) -> String {
        self.build_display_result_json(result, 0)
    }

    fn build_display_result_json(&self, result: &NonErrStmtExecResult, depth: usize) -> String {
        match result {
            NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_stmt_success_result) => {
                self.display_non_factual_stmt_success_json(non_factual_stmt_success_result, depth)
            }
            NonErrStmtExecResult::FactualStmtSuccess(factual_stmt_success_result) => self
                .display_factual_stmt_success_json(factual_stmt_success_result, depth),
            NonErrStmtExecResult::StmtUnknown(_stmt_unknown_result) => unreachable!(),
        }
    }

    fn display_non_factual_stmt_success_json(
        &self,
        non_factual_stmt_success_result: &crate::result::NonFactualStmtSuccess,
        depth: usize,
    ) -> String {
        let indent_outer = json_one_level_indent(depth);
        let indent_inner = json_one_level_indent(depth + 1);
        let mut field_lines: Vec<String> = Vec::new();
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_RESULT,
            json_string_literal(JSON_KEY_SUCCESS)
        ));
        field_lines.push(format!(
            "{}\"stmt_type\": {}",
            indent_inner,
            json_string_literal(
                non_factual_stmt_success_result
                    .stmt
                    .stmt_type_name()
                    .as_str()
            )
        ));
        let stmt_line_file = non_factual_stmt_success_result.stmt.line_file();
        field_lines.push(format!("{}\"line\": {}", indent_inner, stmt_line_file.0));
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_SOURCE,
            json_string_literal(&self.get_file_name_empty_if_default(stmt_line_file))
        ));
        field_lines.push(format!(
            "{}\"stmt\": {}",
            indent_inner,
            json_string_literal(&{
                let stmt_display_string = non_factual_stmt_success_result.stmt.to_string();
                match &non_factual_stmt_success_result.stmt {
                    Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
                    _ => stmt_display_string,
                }
            })
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
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            JSON_KEY_INFER_FACTS,
            &infer_elements,
        ));

        let mut inside_elements: Vec<String> = Vec::new();
        for inside_result in non_factual_stmt_success_result.inside_results.iter() {
            let nested_json = self.build_display_result_json(inside_result, depth + 2);
            inside_elements.push(nested_json);
        }
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            "inside_results",
            &inside_elements,
        ));

        format!(
            "{}{{\n{}\n{}}}",
            indent_outer,
            field_lines.join(",\n"),
            indent_outer
        )
    }

    fn display_factual_stmt_success_json(
        &self,
        factual_stmt_success_result: &crate::result::FactualStmtSuccess,
        depth: usize,
    ) -> String {
        if factual_stmt_success_result.is_verified_by_builtin_rules_only() {
            return self.display_factual_success_verified_by_builtin_rules_json(
                factual_stmt_success_result,
                depth,
            );
        }
        self.display_factual_success_verified_by_known_fact_json(
            factual_stmt_success_result,
            depth,
        )
    }

    fn display_factual_success_verified_by_builtin_rules_json(
        &self,
        factual_stmt_success_result: &crate::result::FactualStmtSuccess,
        depth: usize,
    ) -> String {
        let indent_outer = json_one_level_indent(depth);
        let indent_inner = json_one_level_indent(depth + 1);
        let mut field_lines: Vec<String> = Vec::new();
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_RESULT,
            json_string_literal(JSON_KEY_VERIFIED_BY_BUILTIN_RULE)
        ));
        field_lines.push(format!(
            "{}\"stmt_type\": {}",
            indent_inner,
            json_string_literal("Fact")
        ));
        let fact_line_file = factual_stmt_success_result.stmt.line_file();
        field_lines.push(format!("{}\"line\": {}", indent_inner, fact_line_file.0));
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_SOURCE,
            json_string_literal(&self.get_file_name_empty_if_default(fact_line_file))
        ));
        field_lines.push(format!(
            "{}\"stmt\": {}",
            indent_inner,
            json_string_literal(&factual_stmt_success_result.stmt.to_string())
        ));
        field_lines.push(format!(
            "{}\"verified_by\": {}",
            indent_inner,
            json_string_literal(factual_stmt_success_result.msg.as_str())
        ));

        let infer_indent = json_one_level_indent(depth + 2);
        let mut infer_elements: Vec<String> = Vec::new();
        for infer_fact in factual_stmt_success_result.infers.infer_facts.iter() {
            infer_elements.push(format!(
                "{}{}",
                infer_indent,
                json_string_literal(infer_fact.as_str())
            ));
        }
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            JSON_KEY_INFER_FACTS,
            &infer_elements,
        ));

        let mut inside_elements: Vec<String> = Vec::new();
        for inside_result in factual_stmt_success_result.inside_results.iter() {
            let nested_json = self.build_display_result_json(inside_result, depth + 2);
            inside_elements.push(nested_json);
        }
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            "inside_results",
            &inside_elements,
        ));

        format!(
            "{}{{\n{}\n{}}}",
            indent_outer,
            field_lines.join(",\n"),
            indent_outer
        )
    }

    fn display_factual_success_verified_by_known_fact_json(
        &self,
        factual_stmt_success_result: &crate::result::FactualStmtSuccess,
        depth: usize,
    ) -> String {
        let indent_outer = json_one_level_indent(depth);
        let indent_inner = json_one_level_indent(depth + 1);
        let known_fact_line_file =
            factual_stmt_success_result.line_file_for_verified_by_known_fact_in_json();

        let mut field_lines: Vec<String> = Vec::new();
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_RESULT,
            json_string_literal(JSON_KEY_VERIFIED_BY_KNOWN_FACT)
        ));
        field_lines.push(format!(
            "{}\"stmt_type\": {}",
            indent_inner,
            json_string_literal("Fact")
        ));
        let stmt_line_file = factual_stmt_success_result.stmt.line_file();
        field_lines.push(format!("{}\"line\": {}", indent_inner, stmt_line_file.0));
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_SOURCE,
            json_string_literal(&self.get_file_name_empty_if_default(stmt_line_file))
        ));
        field_lines.push(format!(
            "{}\"stmt\": {}",
            indent_inner,
            json_string_literal(&factual_stmt_success_result.stmt.to_string())
        ));
        field_lines.push(format!(
            "{}\"verified_by_fact_known_on_line\": {}",
            indent_inner, known_fact_line_file.0
        ));
        field_lines.push(format!(
            "{}\"verified_by_fact_known_from_source\": {}",
            indent_inner,
            json_string_literal(&self.get_file_name_empty_if_default(known_fact_line_file))
        ));
        field_lines.push(format!(
            "{}\"verified_by\": {}",
            indent_inner,
            json_string_literal(factual_stmt_success_result.msg.as_str())
        ));

        let infer_indent = json_one_level_indent(depth + 2);
        let mut infer_elements: Vec<String> = Vec::new();
        for infer_fact in factual_stmt_success_result.infers.infer_facts.iter() {
            infer_elements.push(format!(
                "{}{}",
                infer_indent,
                json_string_literal(infer_fact.as_str())
            ));
        }
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            JSON_KEY_INFER_FACTS,
            &infer_elements,
        ));

        let mut inside_elements: Vec<String> = Vec::new();
        for inside_result in factual_stmt_success_result.inside_results.iter() {
            let nested_json = self.build_display_result_json(inside_result, depth + 2);
            inside_elements.push(nested_json);
        }
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            "inside_results",
            &inside_elements,
        ));

        format!(
            "{}{{\n{}\n{}}}",
            indent_outer,
            field_lines.join(",\n"),
            indent_outer
        )
    }
}

impl Runtime {
    pub(in crate::runtime) fn get_location_string_of_line_file(
        &self,
        line: usize,
        file_index: usize,
    ) -> String {
        if (line, file_index) == DEFAULT_LINE_FILE {
            return String::new();
        }

        let path = match self.module_manager.run_file_paths.get(file_index) {
            Some(path) => path.as_ref().to_string(),
            None => String::new(),
        };

        if path.is_empty() {
            format!("on line {}", line)
        } else if file_index == FILE_INDEX_FOR_BUILTIN + 1 {
            format!("on line {}", line)
        } else {
            format!(
                "on line {}, file {}",
                line,
                self.get_file_name_empty_if_default((line, file_index))
            )
        }
    }
}
