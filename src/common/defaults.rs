use std::rc::Rc;

pub type LineFile = (usize, Rc<str>);

pub const FILE_INDEX_FOR_BUILTIN: usize = 0;

/// `fn` 集与内涵集 `{ x S : ... }` 在 AST 中存放的形参名前缀（与用户符面拼接）。
pub const DEFAULT_MANGLED_FN_PARAM_PREFIX: &str = "__";

pub fn default_line_file() -> LineFile {
    (0, Rc::from(""))
}

pub fn is_default_line_file(line_file: &LineFile) -> bool {
    line_file.0 == 0 && line_file.1.is_empty()
}
