//! Read-only syntax hints from the original AST and native lexical spans.
//!
//! Token matching establishes a location, never a mathematical meaning. An
//! absent match or inconsistent AST/source multiplicity is omitted; no nearby
//! expression is borrowed.
use super::*;
use std::sync::Arc;

// (owning line, normalized expression, semantic key) ->
// (original AST occurrence count, candidate source byte ranges).
type HintCandidates = BTreeMap<(usize, Vec<String>, String), (usize, Vec<(usize, usize)>)>;

#[derive(Default)]
pub(super) struct SourceHints {
    source: Option<Arc<str>>,
    lines: BTreeMap<usize, Vec<(String, usize, usize)>>,
    children: BTreeMap<usize, Vec<usize>>,
}

impl SourceHints {
    pub(super) fn from_block(block: &TokenBlock) -> Self {
        let mut lines = BTreeMap::new();
        collect_tokens(block, &mut lines);
        let mut children = BTreeMap::new();
        collect_block_children(block, &mut children);
        Self {
            source: block.source.clone(),
            lines,
            children,
        }
    }

    pub(super) fn block_anchors(
        &self,
        syntax: &JsonValue,
        line: usize,
        rendered: &str,
    ) -> Vec<JsonValue> {
        if field_text(syntax, "type") == "DefStructStmt" {
            return self.struct_field_anchors(syntax, line);
        }
        if !matches!(
            field_text(syntax, "type").as_str(),
            "ByInducStmt" | "ByStrongInducStmt"
        ) || !self.line_matches(rendered, line)
        {
            return Vec::new();
        }
        let Some(fields) = field(syntax, "fields") else {
            return Vec::new();
        };
        if !matches!(field(fields, "base_proof"), Some(JsonValue::Array(_)))
            || !matches!(field(fields, "step_proof"), Some(JsonValue::Array(_)))
        {
            return Vec::new();
        }
        let mut anchors = BTreeMap::new();
        for child in self.children.get(&line).into_iter().flatten() {
            let Some(tokens) = self.lines.get(child) else {
                continue;
            };
            let words = tokens
                .iter()
                .map(|(token, _, _)| token.as_str())
                .collect::<Vec<_>>();
            let role = match words.as_slice() {
                ["?", "from", ..] if words.last() == Some(&":") => "induction_base",
                ["?", "induc" | "strong_induc", ":"] => "induction_step",
                _ => continue,
            };
            let (Some(first), Some(last)) = (tokens.first(), tokens.last()) else {
                continue;
            };
            let Some(original) = self
                .source
                .as_ref()
                .and_then(|source| source.get(first.1..last.2))
            else {
                return Vec::new();
            };
            let anchor = object(vec![
                ("role", text(role)),
                ("line", JsonValue::Number(*child as f64)),
                ("start_byte", JsonValue::Number(first.1 as f64)),
                ("end_byte", JsonValue::Number(last.2 as f64)),
                ("source_text", text(original)),
            ]);
            if anchors.insert(role, anchor).is_some() {
                return Vec::new();
            }
        }
        if anchors.len() != 2 {
            return Vec::new();
        }
        anchors.into_values().collect()
    }

    /// Source syntax only: these conditions are not stored hypotheses or
    /// execution-scope certificates. Retain the already captured original AST.
    pub(super) fn case_contexts(
        &self,
        original: &crate::ast::stmt::ByCasesStmt,
        syntax: &JsonValue,
        source_id: &str,
        spans: &BTreeMap<usize, (usize, usize)>,
    ) -> Vec<JsonValue> {
        let Some(fields) = field(syntax, "fields") else {
            return Vec::new();
        };
        let (Some(cases), Some(proofs)) = (
            field(fields, "cases").and_then(|value| value.as_array().ok()),
            field(fields, "proofs").and_then(|value| value.as_array().ok()),
        ) else {
            return Vec::new();
        };
        if field_text(syntax, "type") != "ByCasesStmt"
            || cases.len() != original.cases.len()
            || proofs.len() != cases.len()
            || original.proofs.len() != cases.len()
            || original.impossible_facts.len() != cases.len()
            || !self.line_matches(&original.readable_string(), original.line_file.line)
        {
            return Vec::new();
        }
        let mut contexts = Vec::new();
        for (index, condition) in original.cases.iter().enumerate() {
            let fact = crate::ast::fact::and_chain_as_fact(condition);
            let Some(location) = crate::json_output::reading_fact_source_line(&fact) else {
                return Vec::new();
            };
            let Some(tokens) = self.lines.get(&location.line) else {
                return Vec::new();
            };
            if !self
                .children
                .get(&original.line_file.line)
                .is_some_and(|lines| lines.contains(&location.line))
                || tokens.first().map(|token| token.0.as_str()) != Some("case")
                || tokens.last().map(|token| token.0.as_str()) != Some(":")
                || !syntax_location_matches(&cases[index], source_id, location.line)
            {
                return Vec::new();
            }
            let Some(header) = self.source_span(location.line, source_id, None) else {
                return Vec::new();
            };
            let Some(steps) = proofs[index].as_array().ok() else {
                return Vec::new();
            };
            if steps.len() != original.proofs[index].len() {
                return Vec::new();
            }
            let mut body = Vec::new();
            for (step, captured) in original.proofs[index].iter().zip(steps) {
                let Some(at) = crate::json_output::reading_statement_source_line(step) else {
                    return Vec::new();
                };
                if field_text(captured, "type") != "Stmt"
                    || field_text(captured, "text") != step.readable_string()
                    || !syntax_location_matches(captured, source_id, at.line)
                    || !self
                        .children
                        .get(&location.line)
                        .is_some_and(|lines| lines.contains(&at.line))
                {
                    return Vec::new();
                }
                let Some(mut span) =
                    self.source_span(at.line, source_id, spans.get(&at.line).copied())
                else {
                    return Vec::new();
                };
                if let JsonValue::Object(fields) = &mut span {
                    fields.insert("statement_text".into(), text(&step.readable_string()));
                }
                body.push(span);
            }
            let impossible = match original.impossible_facts[index].as_ref() {
                None => JsonValue::Null,
                Some(atomic) => {
                    let fact = Fact::AtomicFact(atomic.clone());
                    let Some(at) = crate::json_output::reading_fact_source_line(&fact) else {
                        return Vec::new();
                    };
                    if !self
                        .children
                        .get(&location.line)
                        .is_some_and(|lines| lines.contains(&at.line))
                        || self
                            .lines
                            .get(&at.line)
                            .and_then(|tokens| tokens.first())
                            .map(|token| token.0.as_str())
                            != Some("impossible")
                    {
                        return Vec::new();
                    }
                    let Some(span) = self.source_span(at.line, source_id, None) else {
                        return Vec::new();
                    };
                    span
                }
            };
            contexts.push(object(vec![
                ("index", JsonValue::Number(index as f64)),
                ("condition", cases[index].clone()),
                (
                    "condition_text",
                    text(&crate::display_and_ir::readable_string_from_ir_text(
                        condition.ir().as_str(),
                    )),
                ),
                ("header", header),
                ("proof_steps", JsonValue::Array(body)),
                ("impossible", impossible),
            ]));
        }
        contexts
    }

    fn source_span(
        &self,
        line: usize,
        source_id: &str,
        span: Option<(usize, usize)>,
    ) -> Option<JsonValue> {
        let tokens = self.lines.get(&line)?;
        let (start, end) = span.unwrap_or((tokens.first()?.1, tokens.last()?.2));
        let source = self.source.as_ref()?;
        let original = source.get(start..end)?;
        if start >= end
            || source
                .get(..start)?
                .bytes()
                .filter(|byte| *byte == b'\n')
                .count()
                + 1
                != line
        {
            return None;
        }
        Some(object(vec![
            ("source_id", text(source_id)),
            ("line", JsonValue::Number(line as f64)),
            ("start_byte", JsonValue::Number(start as f64)),
            ("end_byte", JsonValue::Number(end as f64)),
            ("source_text", text(original)),
        ]))
    }

    fn struct_field_anchors(&self, syntax: &JsonValue, line: usize) -> Vec<JsonValue> {
        // Struct rendering retains the header only. Retokenizing that header
        // as a whole block rejects its absent body. Validate the original
        // lexical header against the typed declaration instead.
        let name = field(syntax, "fields")
            .and_then(|fields| field(fields, "name"))
            .map(|value| field_text(value, "name"))
            .unwrap_or_default();
        let Some(header) = self.lines.get(&line) else {
            return Vec::new();
        };
        if header.first().map(|t| t.0.as_str()) != Some("struct")
            || header.get(1).map(|t| t.0.as_str()) != Some(name.as_str())
            || header.last().map(|t| t.0.as_str()) != Some(":")
        {
            return Vec::new();
        }
        let Some(fields) = field(syntax, "fields")
            .and_then(|fields| field(fields, "fields"))
            .and_then(|value| value.as_array().ok())
        else {
            return Vec::new();
        };
        // The parser consumes one direct child per field, in declaration
        // order, followed by an optional <=>: block. Resolved field types can
        // acquire module qualifiers absent from the source; their rendered
        // text is therefore not a source-location key.
        let Some(children) = self.children.get(&line) else {
            return Vec::new();
        };
        if children.len() != fields.len()
            && !(children.len() == fields.len() + 1
                && self
                    .lines
                    .get(&children[fields.len()])
                    .is_some_and(|tokens| {
                        tokens.len() == 2 && tokens[0].0 == "<=>" && tokens[1].0 == ":"
                    }))
        {
            return Vec::new();
        }
        let mut anchors = Vec::new();
        let mut names = BTreeSet::new();
        for (index, definition) in fields.iter().enumerate() {
            let Some(definition) = field(definition, "fields") else {
                return Vec::new();
            };
            let Some(binding) = field(definition, "binding") else {
                return Vec::new();
            };
            let name = field_text(binding, "name");
            let symbol = field_text(binding, "symbol_id");
            let type_text = field(definition, "field_type")
                .map(|value| field_text(value, "text"))
                .unwrap_or_default();
            if name.is_empty()
                || symbol.is_empty()
                || type_text.is_empty()
                || !names.insert(name.clone())
            {
                return Vec::new();
            }
            let child = children[index];
            let Some(tokens) = self.lines.get(&child) else {
                return Vec::new();
            };
            if tokens.len() < 2
                || tokens[0].0 != name
                || self
                    .children
                    .get(&child)
                    .is_some_and(|body| !body.is_empty())
            {
                return Vec::new();
            }
            let start = tokens[0].1;
            let end = tokens.last().unwrap().2;
            let Some(original) = self
                .source
                .as_ref()
                .and_then(|source| source.get(start..end))
            else {
                return Vec::new();
            };
            anchors.push(object(vec![
                ("role", text("structure_field")),
                ("index", JsonValue::Number(index as f64)),
                ("symbol_id", text(&symbol)),
                ("line", JsonValue::Number(child as f64)),
                ("start_byte", JsonValue::Number(start as f64)),
                ("end_byte", JsonValue::Number(end as f64)),
                ("source_text", text(original)),
            ]));
        }
        anchors
    }

    pub(super) fn for_syntax(
        &self,
        syntax: &JsonValue,
        line: usize,
        source_id: &str,
        rendered: &str,
    ) -> Vec<JsonValue> {
        if !self.line_matches(rendered, line) {
            return Vec::new();
        }
        let mut candidates = BTreeMap::new();
        self.visit(syntax, line, source_id, true, &mut candidates);
        let mut hints = BTreeMap::new();
        for ((_, _, key), (ast_count, spans)) in candidates {
            // Identical source spellings may have different syntax roles:
            // fn_range(fn(x R) R {1}) = {1} contains only one list-set Obj.
            // Publish repeated locations only when every candidate is accounted
            // for by the original AST. These are semantic cards, never symbol
            // or fact identities.
            if ast_count != spans.len() {
                continue;
            }
            for (start, end) in spans {
                if let Some(text_value) = self
                    .source
                    .as_ref()
                    .and_then(|source| source.get(start..end))
                {
                    hints.insert(
                        (start, end, key.clone()),
                        object(vec![
                            ("start_byte", JsonValue::Number(start as f64)),
                            ("end_byte", JsonValue::Number(end as f64)),
                            ("reference_key", text(&key)),
                            ("source_text", text(text_value)),
                        ]),
                    );
                }
            }
        }
        hints.into_values().collect()
    }

    fn visit(
        &self,
        node: &JsonValue,
        inherited_line: usize,
        source_id: &str,
        root: bool,
        hints: &mut HintCandidates,
    ) {
        match node {
            JsonValue::Array(values) => {
                for child in values {
                    self.visit(child, inherited_line, source_id, false, hints);
                }
            }
            JsonValue::Object(_) => {
                // Nested statements are indexed by their own capture callbacks.
                if !root && field_text(node, "type") == "Stmt" {
                    return;
                }
                let Some(fields) = field(node, "fields").and_then(|value| value.as_object().ok())
                else {
                    return;
                };
                let mut line = inherited_line;
                if matches!(field_text(node, "type").as_str(), "Fact" | "AtomicFact") {
                    let mut subject = node;
                    while let Some(next) = child(subject) {
                        subject = next;
                    }
                    if let Some(location) =
                        field(subject, "fields").and_then(|fields| field(fields, "line_file"))
                    {
                        let own_line = field(location, "line")
                            .and_then(|value| value.as_u64().ok())
                            .unwrap_or(0) as usize;
                        if own_line != 0 && own_line != inherited_line {
                            if field_text(location, "source_id") != source_id
                                || !self.line_matches(&field_text(node, "text"), own_line)
                            {
                                return;
                            }
                            line = own_line;
                        }
                    }
                }
                if let Some(location) = fields
                    .get("line_file")
                    .filter(|value| !matches!(value, JsonValue::Null))
                {
                    if field_text(location, "source_id") != source_id {
                        return;
                    }
                    line = field(location, "line")
                        .and_then(|value| value.as_u64().ok())
                        .unwrap_or(0) as usize;
                }
                if let Some(key) = reference_key(node) {
                    if let Some((pattern, spans)) =
                        self.matching_spans(&field_text(node, "text"), line)
                    {
                        let entry = hints
                            .entry((line, pattern, key.into()))
                            .or_insert((0, spans));
                        entry.0 += 1;
                    }
                }
                for (_, child) in fields.iter() {
                    self.visit(child, line, source_id, false, hints);
                }
            }
            _ => {}
        }
    }

    fn matching_spans(
        &self,
        expression: &str,
        line: usize,
    ) -> Option<(Vec<String>, Vec<(usize, usize)>)> {
        if expression.is_empty() {
            return None;
        }
        // Use the language tokenizer, including Unicode normalization. This
        // does not parse, execute, instantiate or allocate mathematical ids.
        let blocks = Tokenizer::new()
            .tokenize(expression, crate::runtime::CodeSource::Eval)
            .ok()?;
        if blocks.len() != 1 || !blocks[0].body.is_empty() {
            return None;
        }
        let pattern_tokens = blocks[0]
            .header
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let pattern = grouped_indices(&pattern_tokens)
            .into_iter()
            .map(|i| pattern_tokens[i])
            .collect::<Vec<_>>();
        let tokens = self.lines.get(&line)?;
        let source_tokens = tokens
            .iter()
            .map(|(token, _, _)| token.as_str())
            .collect::<Vec<_>>();
        let source_indices = grouped_indices(&source_tokens);
        if pattern.is_empty() || pattern.len() > source_indices.len() {
            return None;
        }
        let mut found = Vec::new();
        for window in source_indices.windows(pattern.len()) {
            if window
                .iter()
                .zip(&pattern)
                .all(|(i, expected)| source_tokens[*i] == *expected)
            {
                found.push((tokens[*window.first()?].1, tokens[*window.last()?].2));
            }
        }
        if found.is_empty() {
            None
        } else {
            Some((pattern.into_iter().map(str::to_owned).collect(), found))
        }
    }

    fn line_matches(&self, rendered: &str, line: usize) -> bool {
        let Ok(blocks) = Tokenizer::new().tokenize(rendered, crate::runtime::CodeSource::Eval)
        else {
            return false;
        };
        let (Some(block), Some(source)) = (blocks.first(), self.lines.get(&line)) else {
            return false;
        };
        let expected = block.header.iter().map(String::as_str).collect::<Vec<_>>();
        let actual = source
            .iter()
            .map(|(token, _, _)| token.as_str())
            .collect::<Vec<_>>();
        let expected = grouped_indices(&expected)
            .into_iter()
            .map(|i| expected[i])
            .collect::<Vec<_>>();
        let actual = grouped_indices(&actual)
            .into_iter()
            .map(|i| actual[i])
            .collect::<Vec<_>>();
        actual == expected || actual.first() == Some(&"?") && actual[1..] == expected
    }
}

fn syntax_location_matches(mut node: &JsonValue, source_id: &str, line: usize) -> bool {
    loop {
        let Some(fields) = field(node, "fields") else {
            return false;
        };
        if let Some(location) = field(fields, "line_file") {
            return field_text(location, "source_id") == source_id
                && field(location, "line").and_then(|value| value.as_u64().ok())
                    == Some(line as u64);
        }
        let Some(child) = field(fields, "0") else {
            return false;
        };
        node = child;
    }
}

fn collect_block_children(block: &TokenBlock, children: &mut BTreeMap<usize, Vec<usize>>) {
    children.insert(
        block.line,
        block.body.iter().map(|child| child.line).collect(),
    );
    for child in &block.body {
        collect_block_children(child, children);
    }
}

// Ignore redundant grouping in both the retained rendering and the source.
// Intrinsic call/signature, tuple and interval delimiters remain significant.
// This lexical normalization supplies locations only; the AST supplies kinds.
fn grouped_indices(tokens: &[&str]) -> Vec<usize> {
    let mut stack: Vec<(usize, &str, bool, bool)> = Vec::new();
    let mut removed = BTreeSet::new();
    for (i, token) in tokens.iter().copied().enumerate() {
        match token {
            "(" | "[" | "{" => {
                let previous = i.checked_sub(1).map(|n| tokens[n]).unwrap_or("");
                let intrinsic = previous == "'"
                    || previous
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_alphanumeric() || c == '_')
                    || [")", "]", "}", ">"].contains(&previous);
                stack.push((i, token, intrinsic, false));
            }
            "," => {
                if let Some(top) = stack.last_mut() {
                    top.3 = true;
                }
            }
            ")" | "]" | "}" => {
                if let Some((start, opening, intrinsic, comma)) = stack.pop() {
                    if opening == "(" && token == ")" && !intrinsic && !comma {
                        removed.extend([start, i]);
                    }
                }
            }
            _ => {}
        }
    }
    (0..tokens.len()).filter(|i| !removed.contains(i)).collect()
}

fn field<'a>(node: &'a JsonValue, key: &str) -> Option<&'a JsonValue> {
    node.as_object().ok()?.get(key)
}

fn child(node: &JsonValue) -> Option<&JsonValue> {
    field(field(node, "fields")?, "0")
}

fn reference_key(node: &JsonValue) -> Option<&'static str> {
    if field_text(node, "type") != "Obj" {
        return None;
    }
    let inner = child(node)?;
    match field_text(node, "variant").as_str() {
        "FnObj" => Some("obj:call"),
        "InstantiatedTemplateObj" => Some("obj:template"),
        "ProductShape" if field_text(inner, "variant") == "Tuple" => Some("tuple"),
        "FunctionSpace" => match field_text(inner, "variant").as_str() {
            "FnSet" => Some("fn"),
            "AnonymousFn" => Some("obj:anonymous_fn"),
            _ => None,
        },
        "StructAndFieldAccessObj" => match field_text(inner, "variant").as_str() {
            "StructObj" => Some("obj:struct_type"),
            "FieldAccess" => Some("obj:field"),
            _ => None,
        },
        "SetFormer" => match field_text(inner, "variant").as_str() {
            "ListSet" => Some("obj:list_set"),
            "SetBuilder" => Some("obj:set_builder"),
            "IntervalObj" => match field_text(child(inner)?, "variant").as_str() {
                "LeftOpenRightOpen" => Some("obj:interval:open_open"),
                "LeftOpenRightClosed" => Some("obj:interval:open_closed"),
                "LeftClosedRightOpen" => Some("obj:interval:closed_open"),
                "LeftClosedRightClosed" => Some("obj:interval:closed_closed"),
                _ => None,
            },
            "OneSideInfinityIntervalObj" => match field_text(child(inner)?, "variant").as_str() {
                "LowerOpen" => Some("obj:ray:lower_open"),
                "LowerClosed" => Some("obj:ray:lower_closed"),
                "UpperOpen" => Some("obj:ray:upper_open"),
                "UpperClosed" => Some("obj:ray:upper_closed"),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn index(source: &str) -> SourceHints {
        let blocks = Tokenizer::new()
            .tokenize(source, crate::runtime::CodeSource::Eval)
            .unwrap();
        SourceHints::from_block(&blocks[0])
    }
    #[test]
    fn normalized_tokens_keep_exact_original_bytes() {
        let source = "let 区间 = '[ 0, 1 ) # '[9,10)\n";
        let hints = index(source);
        let (_, spans) = hints.matching_spans("'[0, 1)", 1).unwrap();
        assert_eq!(spans.len(), 1);
        let (start, end) = spans[0];
        assert_eq!(&source[start..end], "'[ 0, 1 )");
        assert!(hints.matching_spans("'[9, 10)", 1).is_none());
        let unicode = index("let s = {x ℝ: x ≥ 0}\n");
        assert!(unicode.matching_spans("{x R: x >= 0}", 1).is_some());
    }
    #[test]
    fn candidate_search_keeps_all_locations_without_selecting_one() {
        let hints = index("let f = fn(x R) R {1} + {1}\n");
        assert_eq!(hints.matching_spans("{1}", 1).unwrap().1.len(), 2);
        assert!(hints.matching_spans("{1}", 2).is_none());
        assert!(hints.matching_spans("{2}", 1).is_none());
        let grouped = index("let f = fn(x R) R {1} + {(1)}\n");
        assert_eq!(grouped.matching_spans("{1}", 1).unwrap().1.len(), 2);
        let call = index("f(2) = 1 / 2\n");
        assert!(call.line_matches("f(2) = (1 / 2)", 1));
        assert!(call.matching_spans("f(2)", 1).is_some());
        assert!(!call.line_matches("g(2) = (1 / 2)", 1));
    }
}
