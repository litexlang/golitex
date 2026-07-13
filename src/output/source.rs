use crate::common::json_value::{
    json_one_level_indent, line_file_line_json_value, render_json_value, JsonValue,
};
use crate::prelude::*;
use std::path::Path;
use std::rc::Rc;

use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_LINE, JSON_KEY_SOURCE, JSON_KEY_STMT,
    JSON_KEY_STMT_TYPE,
};
use super::language::localize_json_value;

const SOURCE_KIND: &str = "source_kind";
const SOURCE_KIND_ENTRY: &str = "entry";
const SOURCE_KIND_BUILTIN: &str = "builtin";
const SOURCE_KIND_MODULE: &str = "module";
const SOURCE_KIND_FILE: &str = "file";

fn line_files_have_same_source(left: &LineFile, right: &LineFile) -> bool {
    Rc::ptr_eq(&left.1, &right.1) || left.1.as_ref() == right.1.as_ref()
}

fn line_file_is_entry_source(line_file: &LineFile, mm: &ModuleManager) -> bool {
    Rc::ptr_eq(&line_file.1, &mm.entry_path_rc) || line_file.1.as_ref() == mm.entry_path_rc.as_ref()
}

fn display_source_label_for_line_file(
    runtime: &Runtime,
    line_file: &LineFile,
) -> Option<(String, String)> {
    if is_default_line_file(line_file) {
        return None;
    }

    let path = line_file.1.as_ref();
    if path == BUILTIN_CODE_PATH {
        return Some((
            SOURCE_KIND_BUILTIN.to_string(),
            BUILTIN_CODE_PATH.to_string(),
        ));
    }

    if line_file_is_entry_source(line_file, &runtime.module_manager) {
        return Some((SOURCE_KIND_ENTRY.to_string(), SOURCE_KIND_ENTRY.to_string()));
    }

    for module in runtime.module_manager.modules.values() {
        for file in module.files.iter() {
            if file.source_path == path {
                return Some((SOURCE_KIND_FILE.to_string(), file.canonical_name.clone()));
            }
        }
    }

    if let Some(label) = imported_module_source_label_for_path(runtime, path) {
        return Some(label);
    }

    Some((SOURCE_KIND_FILE.to_string(), SOURCE_KIND_FILE.to_string()))
}

fn imported_module_source_label_for_path(
    runtime: &Runtime,
    source_path: &str,
) -> Option<(String, String)> {
    let source_path = Path::new(source_path);
    let module_manager = &runtime.module_manager;
    let mut best_match: Option<(usize, String, String)> = None;

    for imported_module in module_manager.modules.values() {
        if Some(imported_module.id) == module_manager.entry_module_id {
            continue;
        }
        let module_root = Path::new(imported_module.module_root_path.as_str());
        if !source_path.starts_with(module_root) {
            continue;
        }

        let source_kind = SOURCE_KIND_MODULE.to_string();
        let source = module_display_path(module_root, &module_manager.entry_path_rc);
        let score = imported_module.module_root_path.len();

        if best_match
            .as_ref()
            .map_or(true, |(best_score, _, _)| score > *best_score)
        {
            best_match = Some((score, source_kind, source));
        }
    }

    best_match.map(|(_, source_kind, source)| (source_kind, source))
}

fn module_display_path(module_root: &Path, entry_path: &Rc<str>) -> String {
    let entry_path = Path::new(entry_path.as_ref());
    if let Some(entry_dir) = entry_path.parent() {
        if !entry_dir.as_os_str().is_empty() {
            if let Ok(relative_path) = module_root.strip_prefix(entry_dir) {
                return relative_path.to_string_lossy().into_owned();
            }
        }
    }

    match module_root.file_name() {
        Some(file_name) => file_name.to_string_lossy().into_owned(),
        None => module_root.to_string_lossy().into_owned(),
    }
}

pub(crate) fn source_ref_json_fields(
    runtime: &Runtime,
    source_line_file: &LineFile,
    current_line_file: Option<&LineFile>,
) -> Vec<(String, JsonValue)> {
    let mut fields = vec![(
        JSON_KEY_LINE.to_string(),
        line_file_line_json_value(source_line_file),
    )];

    let same_source = match current_line_file {
        Some(current_line_file) => line_files_have_same_source(source_line_file, current_line_file),
        None => line_file_is_entry_source(source_line_file, &runtime.module_manager),
    };

    if !same_source {
        if let Some((source_kind, source)) =
            display_source_label_for_line_file(runtime, source_line_file)
        {
            fields.push((
                SOURCE_KIND.to_string(),
                JsonValue::JsonString(source_kind.clone()),
            ));
            fields.push((JSON_KEY_SOURCE.to_string(), JsonValue::JsonString(source)));
            if runtime.detail_output && source_kind != SOURCE_KIND_BUILTIN {
                fields.push((
                    "path".to_string(),
                    JsonValue::JsonString(source_line_file.1.as_ref().to_string()),
                ));
            }
        }
    }

    fields
}

pub(crate) fn source_ref_json_value(
    runtime: &Runtime,
    source_line_file: &LineFile,
    current_line_file: Option<&LineFile>,
) -> JsonValue {
    JsonValue::Object(source_ref_json_fields(
        runtime,
        source_line_file,
        current_line_file,
    ))
}

pub(crate) fn stmt_text_for_json(_runtime: &Runtime, stmt: &Stmt) -> String {
    user_visible_stmt_or_msg_text(&stmt.to_string())
}

pub(crate) fn stmt_json_field_lines(
    runtime: &Runtime,
    indent_inner: &str,
    stmt: &Stmt,
) -> Vec<String> {
    let value = localize_json_value(runtime, stmt_json_value(runtime, stmt));
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

pub(crate) fn stmt_json_value(runtime: &Runtime, stmt: &Stmt) -> JsonValue {
    JsonValue::Object(vec![
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(stmt.output_type_string()),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_text_for_json(runtime, stmt)),
        ),
    ])
}
