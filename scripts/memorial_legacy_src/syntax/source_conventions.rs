use std::rc::Rc;

pub type LineFile = (usize, Rc<str>); // (line number, file path)

pub const INTERNAL_SYMBOL_PREFIX: &str = "__";
pub const INTERNAL_BINDER_PREFIX: &str = "____binder_";
pub const DEFAULT_MANGLED_FN_PARAM_PREFIX: &str = INTERNAL_SYMBOL_PREFIX;

pub fn default_line_file() -> LineFile {
    (0, Rc::from(""))
}

pub fn is_default_line_file(line_file: &LineFile) -> bool {
    line_file.0 == 0 && line_file.1.is_empty()
}
