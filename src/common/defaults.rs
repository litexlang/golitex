use std::rc::Rc;

pub type LineFile = (usize, Rc<str>);

pub const FILE_INDEX_FOR_BUILTIN: usize = 0;

pub fn default_line_file() -> LineFile {
    (0, Rc::from(""))
}

pub fn is_default_line_file(line_file: &LineFile) -> bool {
    line_file.0 == 0 && line_file.1.is_empty()
}
