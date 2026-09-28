//! Look up `StoredIdentifierDefinition` for a possibly qualified identifier.

use crate::ast::obj::IdentifierObj;
use crate::exec_env::StoredIdentifierDefinition;
use crate::runtime::Runtime;

impl Runtime {
    // Plain → live stack. Qualified → finished export ExecEnv; if that export is
    // the file currently running, fall back to the live stack by plain name.
    pub(super) fn lookup_stored_identifier_definition_for_release(
        &self,
        name: &IdentifierObj,
    ) -> Option<StoredIdentifierDefinition> {
        let plain = identifier_plain_name(name);
        match name {
            IdentifierObj::Plain { .. } => self
                .stored_identifier_definition_visible_in_stack(plain)
                .cloned(),
            IdentifierObj::WithExportFileId { export_file_id, .. } => self
                .finished_export_exec_env(None, *export_file_id)
                .and_then(|env| env.definitions.identifiers.get(plain).cloned())
                .or_else(|| {
                    if self.code_source.is_live_root_export(*export_file_id) {
                        self.stored_identifier_definition_visible_in_stack(plain)
                            .cloned()
                    } else {
                        None
                    }
                }),
            IdentifierObj::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                ..
            } => self
                .finished_export_exec_env(Some(*global_mod_id), *export_file_id)
                .and_then(|env| env.definitions.identifiers.get(plain).cloned())
                .or_else(|| {
                    if self
                        .code_source
                        .is_live_imported_export(*global_mod_id, *export_file_id)
                    {
                        self.stored_identifier_definition_visible_in_stack(plain)
                            .cloned()
                    } else {
                        None
                    }
                }),
        }
    }
}

fn identifier_plain_name(name: &IdentifierObj) -> &str {
    match name {
        IdentifierObj::Plain { name, .. }
        | IdentifierObj::WithExportFileId { name, .. }
        | IdentifierObj::WithModAndExportFileId { name, .. } => name.as_str(),
    }
}
