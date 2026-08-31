use crate::output::json_value::{
    json_one_level_indent, line_file_line_json_value, render_json_value, JsonValue,
};
use crate::output::messages::translate_json_messages;
use crate::prelude::*;
use std::path::Path;
use std::rc::Rc;

use super::fields::{JSON_KEY_LINE, JSON_KEY_SOURCE, JSON_KEY_STMT, JSON_KEY_STMT_TYPE};

const SOURCE_KIND: &str = "source_kind";
const SOURCE_KIND_MODULE: &str = "module";
const SOURCE_KIND_FILE: &str = "file";

fn line_files_have_same_source(left: &LineFile, right: &LineFile) -> bool {
    Rc::ptr_eq(&left.1, &right.1) || left.1.as_ref() == right.1.as_ref()
}

fn line_file_is_root_source(line_file: &LineFile, mm: &ModuleManager) -> bool {
    mm.module(ModuleId::ROOT)
        .is_some_and(|module| line_file.1.as_ref() == module.main_file_path)
}

fn display_source_label_for_line_file(
    runtime: &Runtime,
    line_file: &LineFile,
) -> Option<(Option<String>, String)> {
    if is_default_line_file(line_file) {
        return None;
    }

    let path = line_file.1.as_ref();

    for module in runtime.module_manager.modules.values() {
        for file in module.files.iter() {
            if file.source_path == path {
                if file.is_virtual_source {
                    return Some((None, file.source_path.clone()));
                }
                let source = if file.canonical_name.is_empty() {
                    file_name_for_display(path)
                } else {
                    file.canonical_name.clone()
                };
                return Some((Some(SOURCE_KIND_FILE.to_string()), source));
            }
        }
    }

    if let Some(label) = imported_module_source_label_for_path(runtime, path) {
        return Some(label);
    }

    Some((
        Some(SOURCE_KIND_FILE.to_string()),
        file_name_for_display(path),
    ))
}

fn imported_module_source_label_for_path(
    runtime: &Runtime,
    source_path: &str,
) -> Option<(Option<String>, String)> {
    let source_path = Path::new(source_path);
    let module_manager = &runtime.module_manager;
    let mut best_match: Option<(usize, String, String)> = None;

    for imported_module in module_manager.modules.values() {
        if imported_module.id == ModuleId::ROOT {
            continue;
        }
        let module_root = Path::new(imported_module.module_root_path.as_str());
        if !source_path.starts_with(module_root) {
            continue;
        }

        let source_kind = SOURCE_KIND_MODULE.to_string();
        let root_path = module_manager
            .module(ModuleId::ROOT)
            .map(|module| module.main_file_path.as_str())
            .unwrap_or_default();
        let source = module_display_path(module_root, root_path);
        let score = imported_module.module_root_path.len();

        if best_match
            .as_ref()
            .map_or(true, |(best_score, _, _)| score > *best_score)
        {
            best_match = Some((score, source_kind, source));
        }
    }

    best_match.map(|(_, source_kind, source)| (Some(source_kind), source))
}

fn module_display_path(module_root: &Path, root_path: &str) -> String {
    let root_path = Path::new(root_path);
    if let Some(root_dir) = root_path.parent() {
        if !root_dir.as_os_str().is_empty() {
            if let Ok(relative_path) = module_root.strip_prefix(root_dir) {
                return relative_path.to_string_lossy().into_owned();
            }
        }
    }

    match module_root.file_name() {
        Some(file_name) => file_name.to_string_lossy().into_owned(),
        None => module_root.to_string_lossy().into_owned(),
    }
}

fn file_name_for_display(source_path: &str) -> String {
    Path::new(source_path)
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| SOURCE_KIND_FILE.to_string())
}

pub fn source_ref_json_fields(
    runtime: &Runtime,
    source_line_file: &LineFile,
    current_line_file: Option<&LineFile>,
    output_detail: OutputDetail,
) -> Vec<(String, JsonValue)> {
    let mut fields = vec![(
        JSON_KEY_LINE.to_string(),
        line_file_line_json_value(source_line_file),
    )];

    let same_source = match current_line_file {
        Some(current_line_file) => line_files_have_same_source(source_line_file, current_line_file),
        None => line_file_is_root_source(source_line_file, &runtime.module_manager),
    };

    if !same_source {
        if let Some((source_kind, source)) =
            display_source_label_for_line_file(runtime, source_line_file)
        {
            if let Some(source_kind) = source_kind {
                fields.push((SOURCE_KIND.to_string(), JsonValue::JsonString(source_kind)));
            }
            fields.push((JSON_KEY_SOURCE.to_string(), JsonValue::JsonString(source)));
            if output_detail.is_detailed() {
                fields.push((
                    "path".to_string(),
                    JsonValue::JsonString(source_line_file.1.as_ref().to_string()),
                ));
            }
        }
    }

    fields
}

pub fn stmt_text_for_json(stmt: &Stmt) -> String {
    stmt.to_string()
}

pub fn stmt_json_field_lines(runtime: &Runtime, indent_inner: &str, stmt: &Stmt) -> Vec<String> {
    let value = translate_json_messages(runtime, stmt_json_value(stmt));
    let JsonValue::Object(fields) = value else {
        return vec![];
    };
    let field_depth = indent_inner.len() / json_one_level_indent(1).len();
    let object_depth = field_depth.saturating_sub(1);
    let rendered = render_json_value(&JsonValue::Object(fields), object_depth);
    let mut lines = rendered.lines().collect::<Vec<_>>();
    if lines.len() < 3 {
        return vec![];
    }
    lines.remove(0);
    lines.pop();
    lines
        .into_iter()
        .map(|line| line.strip_suffix(',').unwrap_or(line).to_string())
        .collect()
}

pub fn stmt_json_value(stmt: &Stmt) -> JsonValue {
    JsonValue::Object(vec![
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(stmt.output_type_string()),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_text_for_json(stmt)),
        ),
    ])
}
