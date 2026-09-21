//! Look up `StoredIdentifierDefinition` for a possibly qualified identifier.

use crate::new_pipeline::ast::obj::IdentifierObj;
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::runtime::Runtime;

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
                .lookup_in_export_env(None, *export_file_id, plain)
                .or_else(|| {
                    if *export_file_id == self.current_export_file_id {
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
                .lookup_in_export_env(Some(*global_mod_id), *export_file_id, plain)
                .or_else(|| {
                    if self.global_module_manager.current_mod_id() == Some(*global_mod_id)
                        && *export_file_id == self.current_export_file_id
                    {
                        self.stored_identifier_definition_visible_in_stack(plain)
                            .cloned()
                    } else {
                        None
                    }
                }),
        }
    }

    fn lookup_in_export_env(
        &self,
        global_mod_id: Option<usize>,
        export_file_id: usize,
        plain: &str,
    ) -> Option<StoredIdentifierDefinition> {
        let exports = match global_mod_id {
            None => self.global_module_manager.root_exports(),
            Some(mod_id) => self
                .global_module_manager
                .imports()
                .get(mod_id)?
                .export_files_and_their_env
                .as_slice(),
        };
        let export = exports.get(export_file_id)?;
        export
            .exec_env
            .definitions
            .identifiers
            .get(plain)
            .cloned()
    }
}

fn identifier_plain_name(name: &IdentifierObj) -> &str {
    match name {
        IdentifierObj::Plain { name, .. }
        | IdentifierObj::WithExportFileId { name, .. }
        | IdentifierObj::WithModAndExportFileId { name, .. } => name.as_str(),
    }
}
