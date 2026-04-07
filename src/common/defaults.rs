use std::rc::Rc;

pub type LineFile = (usize, Rc<str>);

pub const FILE_INDEX_FOR_BUILTIN: usize = 0;

/// `fn` 集与内涵集 `{ x S : ... }` 在 AST 中存放的形参名前缀（与用户符面拼接）。这是必要的，因为 {x R: x > 0} 在 x 在外部被定义后，{x R: x > 0} 就不能被写出来了（参数和外部参数冲突），为了避免这种情况就添加了这个前缀。这个前缀也可以让 set_builder和fnset这样内涵自由变量的obj能更好的工作。
/// 以下是不允许的

// fn(x R: x $in fn(x R)R) R = fn(x R: x $in fn(x R)R) R

// fn(x R: x $in {x R: x > 0}) = fn(x R: x $in {x R: x > 0})

pub const DEFAULT_MANGLED_FN_PARAM_PREFIX: &str = "__";

pub fn default_line_file() -> LineFile {
    (0, Rc::from(""))
}

pub fn is_default_line_file(line_file: &LineFile) -> bool {
    line_file.0 == 0 && line_file.1.is_empty()
}
