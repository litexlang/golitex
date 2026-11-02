//! Borrowed file scope over original module executions.
use super::source_position::{SourceOwner, SourcePosition};
use super::LeanCompileError;
use crate::prelude::*;
use crate::run_module::LeanSourceClosure;
use crate::runtime::CodeSource;

impl<'a> SourcePosition<'a> {
    pub(super) fn module_file(closure: &'a LeanSourceClosure, file: usize, before: usize) -> Self {
        Self::new(
            None,
            SourceOwner::ModuleFile {
                closure,
                file,
                run: &closure.files[file].run,
            },
            before,
        )
    }

    pub(super) fn module_file_number(&self) -> Option<usize> {
        self.module_context().map(|(_, file, _)| file)
    }

    fn module_context(&self) -> Option<(&'a LeanSourceClosure, usize, usize)> {
        let mut cursor = Some(self);
        while let Some(site) = cursor {
            if let SourceOwner::ModuleFile { closure, file, run } = site.owner {
                if std::ptr::eq(run, &closure.files.get(file)?.run) {
                    return Some((closure, file, site.before));
                }
                return None;
            }
            cursor = site.parent;
        }
        None
    }

    /// Ordinary fact/WD ID resolution reads this file's completed environment.
    /// Visibility still comes from this file's original result prefix.
    pub(super) fn module_env(&self, runtime: &'a Runtime) -> Option<&'a crate::exec_env::ExecEnv> {
        let (closure, file, _) = self.module_context()?;
        let recorded = match &closure.files[file].source {
            CodeSource::RootExport { export_file_id, .. } => runtime
                .global_module_manager
                .root_exports()
                .get(*export_file_id),
            CodeSource::ImportedExport {
                global_mod_id,
                export_file_id,
                ..
            } => runtime
                .global_module_manager
                .imports()
                .get(*global_mod_id)?
                .export_files_and_their_env
                .get(*export_file_id),
            CodeSource::Real(path) => runtime
                .global_module_manager
                .root_exports()
                .iter()
                .find(|export| export.path == *path),
            _ => None,
        }?;
        (recorded.path == closure.files[file].source.display_path())
            .then_some(recorded.exec_env.as_ref())
    }

    /// Resolve a qualified declaration in the caller's original configuration,
    /// never in the final Runtime.current_mod_id or a concatenated fact scope.
    pub(super) fn qualified_file_scope(
        &self,
        name: &AtomicName,
        runtime: &Runtime,
    ) -> Result<Self, LeanCompileError> {
        let (closure, current, before) = self
            .module_context()
            .ok_or_else(|| LeanCompileError::unsupported("Module/SourceContext"))?;
        let (target_mod, export) = match name {
            AtomicName::WithExportFileId { export_file_id, .. } => (None, *export_file_id),
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                ..
            } => (Some(*global_mod_id), *export_file_id),
            _ => return Err(LeanCompileError::unsupported("Module/QualifiedName")),
        };
        let current_mod = match closure.files[current].source {
            CodeSource::ImportedExport { global_mod_id, .. } => Some(global_mod_id),
            _ => None,
        };
        let manager = &runtime.global_module_manager;
        let config = match current_mod {
            Some(id) => {
                &manager
                    .imports()
                    .get(id)
                    .ok_or_else(|| LeanCompileError::unsupported("Module/Caller"))?
                    .litex_config
            }
            None => manager.litex_config(),
        };
        if target_mod != current_mod {
            let imported = target_mod.is_some_and(|id| {
                config.imports.iter().any(|import| {
                    let path = import
                        .path
                        .canonicalize()
                        .unwrap_or_else(|_| import.path.clone());
                    manager.mod_id_for_path(&path) == Some(id)
                })
            });
            if !imported {
                return Err(LeanCompileError::unsupported(
                    "Module/DeclarationVisibility",
                ));
            }
        }
        let producer = closure
            .files
            .iter()
            .take(current + 1)
            .position(|file| match &file.source {
                CodeSource::RootExport { export_file_id, .. } => {
                    target_mod.is_none() && *export_file_id == export
                }
                CodeSource::ImportedExport {
                    global_mod_id,
                    export_file_id,
                    ..
                } => target_mod == Some(*global_mod_id) && *export_file_id == export,
                _ => false,
            })
            .ok_or_else(|| LeanCompileError::unsupported("Module/DeclarationProducer"))?;
        Ok(Self::module_file(
            closure,
            producer,
            if producer == current {
                before
            } else {
                closure.files[producer].run.statement_results.len()
            },
        ))
    }
}

impl<'a> SourcePosition<'a> {
    /// Public qualification preserves the original declaration's bound ID;
    /// local binders retain Plain, even when an enclosing file promotes names.
    pub(super) fn defining_identifier(
        &self,
        parameter: &BoundName,
        runtime: &Runtime,
    ) -> Result<IdentifierObj, LeanCompileError> {
        if self.is_local() {
            return Ok(IdentifierObj::from_bound_name(parameter));
        }
        let mut cursor = Some(self);
        while let Some(site) = cursor {
            if let SourceOwner::Statement(ExecStmtResult::Definition(definition)) = site.owner {
                if let Some(parent) = site.parent {
                    if let SourceOwner::ModuleFile { closure, file, .. } = parent.owner {
                        let identifier = match closure.files[file].source {
                            CodeSource::RootExport { export_file_id, .. } => {
                                IdentifierObj::WithExportFileId {
                                    export_file_id,
                                    name: parameter.name.clone(),
                                }
                            }
                            CodeSource::ImportedExport {
                                global_mod_id,
                                export_file_id,
                                ..
                            } => IdentifierObj::WithModAndExportFileId {
                                global_mod_id,
                                export_file_id,
                                name: parameter.name.clone(),
                            },
                            _ => return Ok(IdentifierObj::from_bound_name(parameter)),
                        };
                        let env = parent.module_env(runtime).ok_or_else(|| {
                            LeanCompileError::unsupported("Identifier/OriginalEnvironment")
                        })?;
                        let captured = env
                            .definitions
                            .identifiers
                            .get(&parameter.name)
                            .ok_or_else(|| {
                                LeanCompileError::unsupported("Identifier/OriginalBinding")
                            })?;
                        if captured_binding(captured, &parameter.name) != Some(parameter)
                            || !super::helper::captured_identifier_definition_matches(
                                captured,
                                definition,
                                &parameter.name,
                            )
                        {
                            return Err(LeanCompileError::unsupported(
                                "Identifier/DeclarationCapture",
                            ));
                        }
                        return Ok(identifier);
                    }
                }
            }
            cursor = site.parent;
        }
        Ok(IdentifierObj::from_bound_name(parameter))
    }

    /// Resolve definition metadata only; the original source prefix must still
    /// expose the introducing result and completed constructor publication.
    pub(super) fn qualified_identifier_scope(
        &self,
        identifier: &IdentifierObj,
        runtime: &'a Runtime,
    ) -> Result<
        (
            &'a BoundName,
            Self,
            &'a crate::exec_env::StoredIdentifierDefinition,
        ),
        LeanCompileError,
    > {
        let name = match identifier {
            IdentifierObj::WithExportFileId {
                export_file_id,
                name,
            } => AtomicName::WithExportFileId {
                export_file_id: *export_file_id,
                name: name.clone(),
            },
            IdentifierObj::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => AtomicName::WithModAndExportFileId {
                global_mod_id: *global_mod_id,
                export_file_id: *export_file_id,
                name: name.clone(),
            },
            _ => return Err(LeanCompileError::unsupported("Identifier/QualifiedName")),
        };
        let original = self.qualified_file_scope(&name, runtime)?;
        let captured = original
            .module_env(runtime)
            .and_then(|env| env.definitions.identifiers.get(name.local_name()))
            .ok_or_else(|| LeanCompileError::unsupported("Identifier/OriginalBinding"))?;
        let bound = captured_binding(captured, name.local_name())
            .ok_or_else(|| LeanCompileError::unsupported("Identifier/DefinitionKind"))?;
        let scope = if original.module_file_number() == self.module_file_number() {
            *self
        } else {
            original
        };
        Ok((bound, scope, captured))
    }
}

fn captured_binding<'a>(
    definition: &'a crate::exec_env::StoredIdentifierDefinition,
    name: &str,
) -> Option<&'a BoundName> {
    use crate::exec_env::StoredIdentifierDefinition as D;
    let parameters = match definition {
        D::LetObj((_, p)) => return (&p.name.name == name).then_some(&p.name),
        D::HaveFnEqual((_, p)) => return (&p.name.name == name).then_some(&p.name),
        D::HaveObjEqual((_, p)) => &p.param_def,
        D::HaveObjInNonemptySetOrParamType((_, p)) => &p.param_def,
        D::HaveObjByExistFacts((_, p)) => &p.param_def,
        _ => return None,
    };
    parameters
        .groups
        .iter()
        .flat_map(|group| &group.params)
        .find(|bound| bound.name == name)
}
