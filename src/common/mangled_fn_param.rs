use crate::obj::Obj;
use std::collections::HashMap;

/// 将用户写的形参名转为带前缀的存储名（如 `x` → `__x`）。
pub fn mangled_fn_param_names(user_written_names: &[String], prefix: &str) -> Vec<String> {
    user_written_names
        .iter()
        .map(|u| format!("{}{}", prefix, u))
        .collect()
}

/// `user_name -> Identifier(mangled)`，供 `inst_obj` / `inst_*` 替换。
pub fn fn_param_substitution_map(
    user_written_names: &[String],
    mangled_names: &[String],
) -> HashMap<String, Obj> {
    debug_assert_eq!(user_written_names.len(), mangled_names.len());
    let mut map = HashMap::with_capacity(user_written_names.len());
    for (u, m) in user_written_names.iter().zip(mangled_names.iter()) {
        map.insert(u.clone(), m.clone().into());
    }
    map
}

/// 生成存储名列表与替换表；`prefix` 通常取 `crate::common::defaults::DEFAULT_MANGLED_FN_PARAM_PREFIX`.
pub fn mangled_fn_param_binding(
    user_written_names: &[String],
    prefix: &str,
) -> (Vec<String>, HashMap<String, Obj>) {
    let mangled = mangled_fn_param_names(user_written_names, prefix);
    let map = fn_param_substitution_map(user_written_names, &mangled);
    (mangled, map)
}
