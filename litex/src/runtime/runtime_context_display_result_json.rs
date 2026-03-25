use super::RuntimeContext;
use crate::common::keywords::{COLON, PROVE};
use crate::result::NonErrStmtExecResult;
use crate::stmt::Stmt;

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

impl<'a> RuntimeContext<'a> {
    pub fn display_result_json_string(&self, result: &NonErrStmtExecResult) -> String {
        self.build_display_result_json(result, 0)
    }

    fn build_display_result_json(&self, result: &NonErrStmtExecResult, depth: usize) -> String {
        match result {
            NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_stmt_success_result) => {
                self.display_non_factual_stmt_success_json(non_factual_stmt_success_result, depth)
            }
            NonErrStmtExecResult::FactVerifiedByFact(fact_verified_by_fact_result) => {
                self.display_fact_verified_by_fact_json(fact_verified_by_fact_result, depth)
            }
            NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                fact_verified_by_builtin_rules_result,
            ) => self.display_fact_verified_by_builtin_rules_json(
                fact_verified_by_builtin_rules_result,
                depth,
            ),
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
            json_string_literal(
                &self.get_source_file_by_line_file_return_empty_when_default(stmt_line_file)
            )
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

    fn display_fact_verified_by_fact_json(
        &self,
        fact_verified_by_fact_result: &crate::result::FactVerifiedByFact,
        depth: usize,
    ) -> String {
        let indent_outer = json_one_level_indent(depth);
        let indent_inner = json_one_level_indent(depth + 1);

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
        let fact_line_file = fact_verified_by_fact_result.fact.line_file();
        field_lines.push(format!("{}\"line\": {}", indent_inner, fact_line_file.0));
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_SOURCE,
            json_string_literal(
                &self.get_source_file_by_line_file_return_empty_when_default(fact_line_file)
            )
        ));
        field_lines.push(format!(
            "{}\"stmt\": {}",
            indent_inner,
            json_string_literal(&fact_verified_by_fact_result.fact.to_string())
        ));
        field_lines.push(format!(
            "{}\"verified_by_fact_known_on_line\": {}",
            indent_inner, fact_verified_by_fact_result.verified_by_line_file.0
        ));
        field_lines.push(format!(
            "{}\"verified_by_fact_known_from_source\": {}",
            indent_inner,
            json_string_literal(
                &self.get_source_file_by_line_file_return_empty_when_default(
                    fact_verified_by_fact_result.verified_by_line_file
                )
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
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            JSON_KEY_INFER_FACTS,
            &infer_elements,
        ));

        format!(
            "{}{{\n{}\n{}}}",
            indent_outer,
            field_lines.join(",\n"),
            indent_outer
        )
    }

    fn display_fact_verified_by_builtin_rules_json(
        &self,
        fact_verified_by_builtin_rules_result: &crate::result::FactVerifiedByBuiltinRules,
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
        let fact_line_file = fact_verified_by_builtin_rules_result.fact.line_file();
        field_lines.push(format!("{}\"line\": {}", indent_inner, fact_line_file.0));
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_SOURCE,
            json_string_literal(
                &self.get_source_file_by_line_file_return_empty_when_default(fact_line_file)
            )
        ));
        field_lines.push(format!(
            "{}\"stmt\": {}",
            indent_inner,
            json_string_literal(&fact_verified_by_builtin_rules_result.fact.to_string())
        ));
        field_lines.push(format!(
            "{}\"verified_by\": {}",
            indent_inner,
            json_string_literal(
                format!("{}", &fact_verified_by_builtin_rules_result.verified_by).as_str()
            )
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
        field_lines.push(json_array_field_line(
            indent_inner.as_str(),
            JSON_KEY_INFER_FACTS,
            &infer_elements,
        ));

        format!(
            "{}{{\n{}\n{}}}",
            indent_outer,
            field_lines.join(",\n"),
            indent_outer
        )
    }
}
