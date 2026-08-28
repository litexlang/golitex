//! Topology, trust, identities, template dependencies, and Mermaid shapes.

use super::*;

pub(super) fn definition_graph_module_is_descendant(
    runtime: &Runtime,
    module_id: ModuleId,
    ancestor_module_id: ModuleId,
) -> bool {
    let mut current = Some(module_id);
    while let Some(current_module_id) = current {
        if current_module_id == ancestor_module_id {
            return true;
        }
        current = runtime
            .module_manager
            .module(current_module_id)
            .and_then(|module| module.parent_module_id);
    }
    false
}

pub(super) fn definition_semantic_role(kind: &str, definition_kind: &str) -> &'static str {
    match kind {
        "identifier" => "object",
        "prop" => "property",
        "fn" | "algorithm" => "function",
        "struct" => "structure",
        "template" => "parameterized_declaration",
        "theorem" | "certificate" => "fact",
        "strategy" => "proof_rule",
        "source" => "external_source",
        _ if definition_kind == "selection_certificate" => "fact",
        _ => "unknown",
    }
}

pub(super) fn definition_litex_form(kind: &str, definition_kind: &str) -> &'static str {
    match definition_kind {
        "abstract_prop" => "abstract_prop",
        "axiom" => "axiom",
        "selection_certificate" => "exist_unique_certificate",
        "axiom_source" => "axiom",
        "trust_source" => "trust",
        "unverified_import" => "import",
        _ => match kind {
            "identifier" => "have",
            "prop" => "prop",
            "fn" => "have_fn",
            "algorithm" => "have_algo",
            "struct" => "struct",
            "template" => "template",
            "theorem" => "thm",
            "strategy" => "strategy",
            "certificate" => "exist_unique_certificate",
            "source" => "trust",
            _ => "unknown",
        },
    }
}

pub(super) fn default_definition_knowledge_status(
    definition_kind: &str,
) -> (&'static str, Option<&'static str>) {
    match definition_kind {
        "axiom" | "axiom_source" => ("axiom", Some("direct")),
        "trust_source" | "unverified_import" => ("trust", Some("direct")),
        _ => ("checked", None),
    }
}

pub(super) fn stmt_results_contain_direct_trust(results: &[StmtResult]) -> bool {
    for result in results {
        let Some(success) = result.non_factual_success() else {
            continue;
        };
        if matches!(
            &success.statement(),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_))
                | Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_))
        ) {
            return true;
        }
        if success_children_contain_direct_trust(success) {
            return true;
        }
    }
    false
}

pub(super) fn success_children_contain_direct_trust(success: &SuccessStmtResult) -> bool {
    let mut contains_trust = false;
    success.visit_child_results(&mut |child| {
        if !contains_trust && stmt_results_contain_direct_trust(std::slice::from_ref(child)) {
            contains_trust = true;
        }
    });
    success.visit_success_child_results(&mut |child| {
        if !contains_trust && success_result_contains_direct_trust(child) {
            contains_trust = true;
        }
    });
    contains_trust
}

pub(super) fn success_result_contains_direct_trust(success: &SuccessStmtResult) -> bool {
    if matches!(
        &success.statement(),
        Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_)) | Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_))
    ) {
        return true;
    }
    success_children_contain_direct_trust(success)
}

pub(super) fn trust_source_id(kind: &str, name: Option<&str>, line_file: &LineFile) -> String {
    format!(
        "source:{}:{}:{}",
        kind,
        name.unwrap_or("anonymous"),
        definition_line_key(line_file)
    )
}

pub(super) fn selection_certificate_id(function_name: &str, line_file: &LineFile) -> String {
    format!(
        "certificate:exist_unique:{}:{}",
        function_name,
        definition_line_key(line_file)
    )
}

pub(super) fn definition_line_key(line_file: &LineFile) -> String {
    let path = Path::new(line_file.1.as_ref());
    let mut source_label = None;
    let mut ancestor = path.parent();
    while let Some(directory) = ancestor {
        if directory.join("litex.config").is_file() {
            source_label = path
                .strip_prefix(directory)
                .ok()
                .map(|relative| relative.to_string_lossy().into_owned());
            break;
        }
        ancestor = directory.parent();
    }
    let source_label = source_label
        .or_else(|| {
            path.file_name()
                .map(|name| name.to_string_lossy().into_owned())
        })
        .unwrap_or_else(|| "source".to_string());
    format!("{}:{}", source_label, line_file.0)
}

pub(super) fn definition_line_label(line_file: &LineFile) -> String {
    if *line_file == default_line_file() {
        "unknown".to_string()
    } else {
        line_file.0.to_string()
    }
}

pub(super) fn sorted_count_object(counts: HashMap<String, usize>) -> JsonValue {
    let mut entries = counts.into_iter().collect::<Vec<_>>();
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    JsonValue::Object(
        entries
            .into_iter()
            .map(|(kind, count)| (kind, JsonValue::Number(count)))
            .collect(),
    )
}

pub(super) fn node_is_in_cycle(
    start: &str,
    outgoing: &HashMap<String, Vec<String>>,
    unresolved: &HashSet<String>,
) -> bool {
    let mut stack = outgoing.get(start).cloned().unwrap_or_default();
    let mut visited = HashSet::new();
    while let Some(node_id) = stack.pop() {
        if node_id == start {
            return true;
        }
        if !unresolved.contains(&node_id) || !visited.insert(node_id.clone()) {
            continue;
        }
        if let Some(next_nodes) = outgoing.get(&node_id) {
            stack.extend(next_nodes.iter().cloned());
        }
    }
    false
}

pub(super) fn collect_template_definition_dependencies(
    collector: &mut DepCollector,
    definition: &TemplateDefEnum,
) {
    match definition {
        TemplateDefEnum::HaveObjInNonemptySetStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
        }
        TemplateDefEnum::HaveObjEqualStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
            for value in &statement.objs_equal_to {
                collector.collect_obj(value);
            }
        }
        TemplateDefEnum::HaveObjByExistFactsStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
            for fact in &statement.facts {
                collector.collect_quantifier_free_fact(fact);
            }
        }
        TemplateDefEnum::TrustHaveStmt(statement) => {
            collector.collect_param_def_with_type_deps(&statement.param_def);
            collector.add_param_def_with_type(&statement.param_def);
            for fact in &statement.facts {
                collector.collect_fact(fact);
            }
        }
        TemplateDefEnum::ObtainObjFromExistFact(statement) => {
            collector.collect_exist_fact(&statement.fact);
        }
        TemplateDefEnum::ObtainObjFromAtomicFact(statement) => {
            let fact: AtomicFact = statement.fact.clone().into();
            collector.collect_atomic_fact(&fact);
        }
        TemplateDefEnum::ObtainObjFromThm(statement) => {
            for argument in &statement.args {
                collector.collect_obj(argument);
            }
        }
        TemplateDefEnum::HaveFnEqualStmt(statement) => {
            collector.add_local_name(statement.name());
            collector.collect_anonymous_fn(&statement.equal_to_anonymous_fn);
        }
        TemplateDefEnum::HaveFnEqualCaseByCaseStmt(statement) => {
            collector.add_local_name(statement.name());
            collector.collect_fn_set_clause(&statement.fn_set_clause);
            for condition in &statement.cases {
                collector.collect_and_chain_atomic_fact(condition);
            }
            for value in &statement.equal_tos {
                collector.collect_obj(value);
            }
        }
        TemplateDefEnum::HaveFnByInducStmt(statement) => {
            collector.add_local_name(statement.name());
            collector.collect_fn_set_clause(&statement.fn_set_clause);
            collector.collect_obj(&statement.measure);
            collector.collect_obj(&statement.lower_bound);
            for case in &statement.cases {
                collector.collect_have_fn_by_induc_case(case);
            }
        }
        TemplateDefEnum::HaveFnByForallExistUniqueStmt(statement) => {
            collector.add_local_name(statement.fn_name());
            collector.collect_forall_fact(&statement.forall);
        }
        TemplateDefEnum::HaveTupleStmt(statement) => {
            collector.add_local_name(statement.index_name());
            collector.collect_obj(&statement.dimension);
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveCartStmt(statement) => {
            collector.add_local_name(statement.index_name());
            collector.collect_obj(&statement.dimension);
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveSeqStmt(statement) => {
            collector.add_local_name(statement.index_name());
            collector.collect_obj(&statement.seq_set.clone().into());
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveFiniteSeqStmt(statement) => {
            collector.add_local_name(statement.index_name());
            collector.collect_obj(&statement.finite_seq_set.clone().into());
            collector.collect_obj(&statement.bound);
            collector.collect_obj(&statement.value);
        }
        TemplateDefEnum::HaveMatrixStmt(statement) => {
            collector.add_local_name(statement.row_index_name());
            collector.add_local_name(statement.col_index_name());
            collector.collect_obj(&statement.matrix_set.clone().into());
            collector.collect_obj(&statement.row_bound);
            collector.collect_obj(&statement.col_bound);
            collector.collect_obj(&statement.value);
        }
    }
}

pub(super) fn definition_id(kind: &str, name: &str) -> String {
    format!("definition:{}:{}", kind, name)
}

pub(super) fn mermaid_id(id: &str) -> String {
    let mut out = String::from("n_");
    for ch in id.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    out
}

pub(super) fn mermaid_node_shape(node: &DefinitionGraphNode) -> String {
    let label = node.label.replace('"', "'");
    match node.kind.as_str() {
        "prop" => format!("([\"{}\"])", label),
        "fn" => format!("{{\"{}\"}}", label),
        "theorem" => format!("[/\"{}\"/]", label),
        _ => format!("[\"{}\"]", label),
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/graph/definition_graph/tests.rs"]
mod tests;
