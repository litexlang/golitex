//! Compiler-owned statement boundaries. Markers exist only during composition;
//! the final content is ordinary LaTeX with UTF-8 byte spans, never marker text.
use crate::prelude::*;

pub(crate) struct LatexStatementSpan {
    pub statement_id: String,
    pub start_byte: usize,
    pub end_byte: usize,
}

pub(crate) struct MappedLatex {
    pub content: String,
    pub statements: Vec<LatexStatementSpan>,
}

impl LatexStatementSpan {
    fn new(statement_id: String, start_byte: usize, end_byte: usize) -> Self {
        Self {
            statement_id,
            start_byte,
            end_byte,
        }
    }
}

impl MappedLatex {
    fn new(content: String, statements: Vec<LatexStatementSpan>) -> Self {
        Self {
            content,
            statements,
        }
    }
}

pub(super) struct StatementAnnotations<'a> {
    resolve: &'a mut dyn FnMut(&Stmt) -> Option<String>,
    hints: &'a std::collections::BTreeMap<String, ReadingLatexHint>,
    ids: Vec<String>,
}

/// Presentation of a single, recorded execution, supplied only by Reading.
#[derive(Default)]
pub(crate) struct ReadingLatexHint {
    pub assumption: Option<String>,
    pub release: Vec<String>,
    pub follows_previous: bool,
}

impl<'a> StatementAnnotations<'a> {
    fn new(
        resolve: &'a mut dyn FnMut(&Stmt) -> Option<String>,
        hints: &'a std::collections::BTreeMap<String, ReadingLatexHint>,
    ) -> Self {
        Self {
            resolve,
            hints,
            ids: Vec::new(),
        }
    }

    pub(super) fn hint(&self, index: usize) -> Option<&ReadingLatexHint> {
        self.hints.get(&self.ids[index])
    }
    pub(super) fn has_reading_hints(&self) -> bool {
        !self.hints.is_empty()
    }

    pub fn record(&mut self, statement: &Stmt) -> Option<usize> {
        let id = (self.resolve)(statement)?;
        let index = self.ids.len();
        self.ids.push(id);
        Some(index)
    }

    pub fn wrap(index: usize, content: &str) -> String {
        // Keep the original terminal newline visible to the ordinary paragraph
        // composer. The statement span excludes only this final whitespace.
        let (body, newline) = content
            .strip_suffix('\n')
            .map_or((content, ""), |body| (body, "\n"));
        format!("\u{1e}b{index}\u{1f}{body}\u{1e}e{index}\u{1f}{newline}")
    }

    pub fn finish(self, marked: &str) -> RuntimeResult<MappedLatex> {
        let mut content = String::new();
        let mut statements = Vec::new();
        let mut stack = Vec::new();
        let mut pending = marked;
        while let Some(start) = pending.find('\u{1e}') {
            content.push_str(&pending[..start]);
            pending = &pending[start + 1..];
            let end = pending.find('\u{1f}').ok_or_else(invalid_marker)?;
            let marker = &pending[..end];
            let index: usize = marker
                .get(1..)
                .and_then(|s| s.parse().ok())
                .ok_or_else(invalid_marker)?;
            if index >= self.ids.len() {
                return Err(invalid_marker());
            }
            match marker.as_bytes().first() {
                Some(b'b') => stack.push((index, content.len())),
                Some(b'e') => {
                    let (opened, start_byte) = stack.pop().ok_or_else(invalid_marker)?;
                    if opened != index {
                        return Err(invalid_marker());
                    }
                    statements.push(LatexStatementSpan::new(
                        self.ids[index].clone(),
                        start_byte,
                        content.len(),
                    ));
                }
                _ => return Err(invalid_marker()),
            }
            pending = &pending[end + 1..];
        }
        content.push_str(pending);
        if !stack.is_empty() || content.contains('\u{1f}') || statements.len() != self.ids.len() {
            return Err(invalid_marker());
        }
        statements.sort_by_key(|span| (span.start_byte, std::cmp::Reverse(span.end_byte)));
        Ok(MappedLatex::new(content, statements))
    }
}

#[cfg(test)]
pub(crate) fn to_latex_with_statement_ids(
    statements: &[Stmt],
    modules: &crate::module_manager::GlobalModuleManager,
    language: OutputLanguage,
    resolve: &mut dyn FnMut(&Stmt) -> Option<String>,
) -> RuntimeResult<MappedLatex> {
    to_latex_for_reading(statements, modules, language, resolve, &Default::default())
}

pub(crate) fn to_latex_for_reading(
    statements: &[Stmt],
    modules: &crate::module_manager::GlobalModuleManager,
    language: OutputLanguage,
    resolve: &mut dyn FnMut(&Stmt) -> Option<String>,
    hints: &std::collections::BTreeMap<String, ReadingLatexHint>,
) -> RuntimeResult<MappedLatex> {
    let mut annotations = Some(StatementAnnotations::new(resolve, hints));
    let marked = super::stmt::render_statements(statements, modules, language, &mut annotations)?;
    annotations
        .expect("annotation owner is retained")
        .finish(&marked)
}

fn invalid_marker() -> RuntimeError {
    RuntimeError::Unsupported("LaTeX: inconsistent compiler statement boundaries".into())
}
