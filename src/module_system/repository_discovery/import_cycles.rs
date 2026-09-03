//! Module import cycle detection.

use super::*;

pub(super) fn reject_cyclic_module_imports(
    runtime: &Runtime,
    edges: &HashMap<ModuleId, Vec<ModuleId>>,
) -> Result<(), RuntimeError> {
    let mut visited = HashSet::new();
    let mut visiting = HashSet::new();
    let mut stack = vec![];
    for module_id in edges.keys().copied().collect::<Vec<ModuleId>>() {
        if let Some(cycle) =
            find_module_import_cycle(module_id, edges, &mut visited, &mut visiting, &mut stack)
        {
            let names = cycle
                .iter()
                .map(|cycle_id| {
                    runtime
                        .module_manager
                        .module(*cycle_id)
                        .map(|module| {
                            if module.module_name.is_empty() {
                                "<root>".to_string()
                            } else {
                                module.module_name.clone()
                            }
                        })
                        .unwrap_or_else(|| format!("module#{}", cycle_id.0))
                })
                .collect::<Vec<String>>();
            let source_path = runtime
                .module_manager
                .module(module_id)
                .map(ModuleRunner::main_source_label)
                .unwrap_or_default();
            return Err(repository_error(
                format!("cyclic module import: {}", names.join(" -> ")),
                source_path.as_str(),
                0,
            ));
        }
    }
    Ok(())
}

pub(super) fn find_module_import_cycle(
    module_id: ModuleId,
    edges: &HashMap<ModuleId, Vec<ModuleId>>,
    visited: &mut HashSet<ModuleId>,
    visiting: &mut HashSet<ModuleId>,
    stack: &mut Vec<ModuleId>,
) -> Option<Vec<ModuleId>> {
    if visited.contains(&module_id) {
        return None;
    }
    if visiting.contains(&module_id) {
        let start = stack
            .iter()
            .position(|item| *item == module_id)
            .unwrap_or(0);
        let mut cycle = stack[start..].to_vec();
        cycle.push(module_id);
        return Some(cycle);
    }

    visiting.insert(module_id);
    stack.push(module_id);
    if let Some(dependencies) = edges.get(&module_id) {
        for dependency in dependencies {
            if let Some(cycle) =
                find_module_import_cycle(*dependency, edges, visited, visiting, stack)
            {
                return Some(cycle);
            }
        }
    }
    stack.pop();
    visiting.remove(&module_id);
    visited.insert(module_id);
    None
}
