use crate::ast::names::AtomicName;
use crate::ast::obj::IdentifierObj;
use crate::module_manager::GlobalModuleManager;
use crate::runtime::{RuntimeError, RuntimeResult};

pub(super) fn escape_text(text: &str) -> String {
    let mut out = String::new();
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str(r"\textbackslash{}"),
            '{' => out.push_str(r"\{"),
            '}' => out.push_str(r"\}"),
            '$' | '&' | '#' | '%' | '_' => {
                out.push('\\');
                out.push(ch);
            }
            '^' => out.push_str(r"\textasciicircum{}"),
            '~' => out.push_str(r"\textasciitilde{}"),
            _ => out.push(ch),
        }
    }
    out
}

pub(super) fn ident(text: &str) -> String {
    if text.len() == 1 && text.chars().all(|c| c.is_ascii_alphabetic()) {
        text.to_string()
    } else {
        format!(r"\mathit{{{}}}", escape_text(text))
    }
}

pub(super) fn name(name: &AtomicName, modules: &GlobalModuleManager) -> RuntimeResult<String> {
    let config = modules
        .current_litex_config()
        .map_err(RuntimeError::Unsupported)?;
    let text = match name {
        AtomicName::Plain { name } => name.clone(),
        AtomicName::WithExportFileId {
            export_file_id,
            name,
        } => {
            let file = config.exports.get(*export_file_id).ok_or_else(|| {
                RuntimeError::Unsupported(format!(
                    "LaTeX: missing export name for index {export_file_id}"
                ))
            })?;
            format!("{}::{name}", file.name)
        }
        AtomicName::WithModAndExportFileId {
            global_mod_id,
            export_file_id,
            name,
        } => {
            let module = modules.imports().get(*global_mod_id).ok_or_else(|| {
                RuntimeError::Unsupported(format!(
                    "LaTeX: missing module name for index {global_mod_id}"
                ))
            })?;
            let file = module
                .litex_config
                .exports
                .get(*export_file_id)
                .ok_or_else(|| {
                    RuntimeError::Unsupported(format!(
                        "LaTeX: missing export name for index {export_file_id}"
                    ))
                })?;
            format!("{}::{}::{name}", module.name, file.name)
        }
    };
    Ok(ident(&text))
}

pub(super) fn identifier(
    value: &IdentifierObj,
    modules: &GlobalModuleManager,
) -> RuntimeResult<String> {
    match value {
        IdentifierObj::Plain { name, .. } => Ok(ident(name)),
        IdentifierObj::WithExportFileId {
            export_file_id,
            name: local,
        } => name(
            &AtomicName::WithExportFileId {
                export_file_id: *export_file_id,
                name: local.clone(),
            },
            modules,
        ),
        IdentifierObj::WithModAndExportFileId {
            global_mod_id,
            export_file_id,
            name: local,
        } => name(
            &AtomicName::WithModAndExportFileId {
                global_mod_id: *global_mod_id,
                export_file_id: *export_file_id,
                name: local.clone(),
            },
            modules,
        ),
    }
}

pub(super) fn parens(text: &str) -> String {
    format!(r"\left({text}\right)")
}

pub(super) fn call_parens(text: &str) -> String {
    format!("({text})")
}

pub(super) fn predicate_or_fn_call(head: &str, args: &str) -> String {
    if args.is_empty() {
        head.to_string()
    } else {
        format!("{head}{}", call_parens(args))
    }
}

pub(super) fn needs_group(text: &str) -> bool {
    text.contains(r"\land")
        || text.contains(r"\lor")
        || text.contains(r"\Rightarrow")
        || text.contains(r"\Longleftrightarrow")
        || text.contains(r"\forall")
        || text.contains(r"\exists")
}

pub(super) fn group_if_compound(text: &str) -> String {
    if needs_group(text) {
        parens(text)
    } else {
        text.to_string()
    }
}

pub(super) fn join_land(items: Vec<String>) -> String {
    join_connective(items, r" \land ")
}

pub(super) fn join_lor(items: Vec<String>) -> String {
    join_connective(items, r" \lor ")
}

fn join_connective(items: Vec<String>, sep: &str) -> String {
    if items.len() <= 1 {
        return items.into_iter().next().unwrap_or_default();
    }
    items
        .into_iter()
        .map(|x| group_if_compound(&x))
        .collect::<Vec<_>>()
        .join(sep)
}

pub(super) fn inline(text: &str) -> String {
    // Prefer $...$ over \(...\): lost backslashes would turn \(...\) into visible ( ... ).
    format!("${text}$")
}
pub(super) fn display(text: &str) -> String {
    format!("\\[\n{text}\n\\]\n")
}

pub(super) fn multiline_conjunction(items: Vec<String>) -> String {
    if items.len() <= 1 {
        return group_if_compound(&items.into_iter().next().unwrap_or_default());
    }
    let mut rows = Vec::new();
    for (index, item) in items.into_iter().enumerate() {
        let connective = if index == 0 { "" } else { r"{}\land\ " };
        rows.push(format!("&{connective}{}", group_if_compound(&item)));
    }
    format!(
        "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
        rows.join(" \\\\[0.2em]\n")
    )
}

pub(super) fn quantified_layout(quantifier: &str, parameters: &str, body: &str) -> String {
    if parameters.is_empty() {
        return body.to_string();
    }
    format!("\\begin{{gathered}}\n{quantifier} {parameters}:\\\\[0.4em]\n{body}\n\\end{{gathered}}")
}

pub(super) fn chain_relation(name: &AtomicName) -> Option<&str> {
    let AtomicName::Plain { name } = name else {
        return None;
    };
    match name.as_str() {
        "=" => Some("="),
        "!=" => Some(r"\ne"),
        "<" => Some("<"),
        ">" => Some(">"),
        "<=" => Some(r"\leq"),
        ">=" => Some(r"\geq"),
        "in" => Some(r"\in"),
        "subset" => Some(r"\subseteq"),
        "superset" => Some(r"\supseteq"),
        "proper_subset" => Some(r"\subsetneq"),
        "proper_superset" => Some(r"\supsetneq"),
        _ => None,
    }
}

pub(super) fn operator(operator: &str, args: &[String]) -> String {
    format!(
        r"\operatorname{{{}}}({})",
        escape_text(operator),
        args.join(", ")
    )
}

// A bracketed subscript records explicit source size parameters, not entry access.
pub(super) fn dimensioned(text: String, dimensions: &[String]) -> String {
    format!(r"\left({text}\right)_{{[{}]}}", dimensions.join(","))
}
