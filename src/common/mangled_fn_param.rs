use crate::obj::Obj;
use std::collections::HashMap;

/// Turn user-written parameter names into prefixed storage names (e.g. `x` -> `__x`).
pub fn mangled_fn_param_names(user_written_names: &[String], prefix: &str) -> Vec<String> {
    user_written_names
        .iter()
        .map(|u| format!("{}{}", prefix, u))
        .collect()
}

/// `user_name -> Identifier(mangled)` for `inst_obj` / `inst_*` substitution.
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

/// Build mangled names and substitution map; `prefix` is usually `DEFAULT_MANGLED_FN_PARAM_PREFIX`.
pub fn mangled_fn_param_binding(
    user_written_names: &[String],
    prefix: &str,
) -> (Vec<String>, HashMap<String, Obj>) {
    let mangled = mangled_fn_param_names(user_written_names, prefix);
    let map = fn_param_substitution_map(user_written_names, &mangled);
    (mangled, map)
}
