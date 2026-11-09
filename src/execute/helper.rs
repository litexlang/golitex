use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn published_parameter_substitution(
    runtime: &Runtime,
    parameters: &TypedParameterList,
) -> HashMap<IdentifierId, Obj> {
    parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .filter_map(|p| {
            let mention = runtime.identifier_obj_for_stored_mention(p);
            if mention == IdentifierObj::from_bound_name(p) {
                None
            } else {
                Some((p.id, Obj::Identifier(mention)))
            }
        })
        .collect()
}

pub(super) fn publish_parameter_type(
    runtime: &mut Runtime,
    ty: &ParamType,
    substitution: &HashMap<IdentifierId, Obj>,
) -> RuntimeResult<ParamType> {
    let ParamType::Obj(obj) = ty else {
        return Ok(ty.clone());
    };
    let mut free = std::collections::HashSet::new();
    crate::instantiate::collect_free_plain_ids(obj, &std::collections::HashSet::new(), &mut free);
    if !substitution.keys().any(|id| free.contains(id)) {
        return Ok(ty.clone());
    }
    runtime
        .inst_param_type(ty, substitution)
        .map_err(|e| RuntimeError::InternalBug(format!("parameter publication: {e}")))
}

pub(super) fn published_parameter_list(
    runtime: &mut Runtime,
    parameters: &TypedParameterList,
) -> RuntimeResult<TypedParameterList> {
    let substitution = published_parameter_substitution(runtime, parameters);
    let mut result = parameters.clone();
    for group in &mut result.groups {
        group.param_type = publish_parameter_type(runtime, &group.param_type, &substitution)?;
    }
    Ok(result)
}

pub(crate) fn parameter_substitution_for_surface(
    released: &IdentifierObj,
    param_def: &TypedParameterList,
) -> HashMap<IdentifierId, Obj> {
    let released_plain = match released {
        IdentifierObj::Plain { name, .. }
        | IdentifierObj::WithExportFileId { name, .. }
        | IdentifierObj::WithModAndExportFileId { name, .. } => name,
    };
    let mut subst = HashMap::new();
    for group in &param_def.groups {
        for param in &group.params {
            let surface = if &param.name == released_plain {
                released.clone()
            } else {
                match released {
                    IdentifierObj::Plain { .. } => IdentifierObj::from_bound_name(param),
                    IdentifierObj::WithExportFileId { export_file_id, .. } => {
                        IdentifierObj::with_export_file_id(*export_file_id, param.name.clone())
                    }
                    IdentifierObj::WithModAndExportFileId {
                        global_mod_id,
                        export_file_id,
                        ..
                    } => IdentifierObj::with_mod_and_export_file_id(
                        *global_mod_id,
                        *export_file_id,
                        param.name.clone(),
                    ),
                }
            };
            subst.insert(param.id, Obj::Identifier(surface));
        }
    }
    subst
}
