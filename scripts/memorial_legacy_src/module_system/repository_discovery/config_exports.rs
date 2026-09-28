//! Configured export discovery.

use super::*;

pub(super) fn discover_config_export(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    export: ProjectExport,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ImportTarget, RuntimeError> {
    let (owner_root, owner_name) = {
        let owner = runtime
            .module_manager
            .module(owner_module_id)
            .expect("manifest owner module should exist");
        (
            owner
                .root_directory_path()
                .map(|path| path.as_path().to_path_buf())
                .unwrap_or_default(),
            owner.module_name.clone(),
        )
    };
    if runtime
        .module_manager
        .module(owner_module_id)
        .expect("manifest owner module should exist")
        .exports
        .contains_key(&export.name)
    {
        return Err(repository_error(
            format!("duplicate export name `{}` in [export]", export.name),
            &config_path.to_string_lossy(),
            export.line,
        ));
    }

    let child_name_on_disk = direct_child_name(
        export.path.as_str(),
        &config_path.to_string_lossy(),
        export.line,
        "[export]",
    )?;
    let target_path = owner_root.join(child_name_on_disk);
    if target_path.is_file() {
        let canonical_path =
            canonical_file(&target_path, &config_path.to_string_lossy(), export.line)?;
        if canonical_path.parent() != Some(owner_root.as_path()) {
            return Err(repository_error(
                "[export] file target must remain inside its containing folder".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        if canonical_path
            .extension()
            .and_then(|extension| extension.to_str())
            != Some("lit")
        {
            return Err(repository_error(
                "[export] file targets must point to a .lit file".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        let source_path =
            path_string(&canonical_path, &config_path.to_string_lossy(), export.line)?;
        let canonical_name = join_module_name(&owner_name, &export.name);
        let source_id = runtime
            .module_manager
            .module_mut(owner_module_id)
            .expect("manifest owner module should exist")
            .create_exported_source(source_path.clone(), canonical_name.clone());
        let target = ImportTarget::File {
            module_id: owner_module_id,
            source_id,
        };
        runtime
            .module_manager
            .register_exported_file(canonical_name, target)
            .map_err(|message| {
                repository_error(message, &config_path.to_string_lossy(), export.line)
            })?;
        runtime
            .module_manager
            .module_mut(owner_module_id)
            .expect("manifest owner module should exist")
            .exports
            .insert(
                export.name.clone(),
                ExportEntry::File {
                    name: export.name.clone(),
                    source_id,
                },
            );
        return Ok(target);
    } else if target_path.is_dir() {
        let canonical_root = canonical_directory(
            &target_path.to_string_lossy(),
            &config_path.to_string_lossy(),
            export.line,
        )?;
        if canonical_root.parent() != Some(owner_root.as_path()) {
            return Err(repository_error(
                "[export] folder target must remain inside its containing folder".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        let child_config_path =
            require_project_config(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_config = read_project_config(&child_config_path)?;
        if child_config.hierarchy != ProjectHierarchy::Submodule {
            return Err(repository_error(
                "[export] folder target must declare `submodule` under [hierarchy]".to_string(),
                &child_config_path.to_string_lossy(),
                child_config.hierarchy_line,
            ));
        }
        let child_name = join_module_name(&owner_name, &export.name);
        let child_root_string =
            path_string(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_config_string = path_string(
            &child_config_path,
            &config_path.to_string_lossy(),
            export.line,
        )?;
        reject_active_mount_cycle(
            runtime,
            mount_stack,
            child_root_string.as_str(),
            child_name.as_str(),
            "cyclic package export",
            config_path,
            export.line,
        )?;
        let child_module_id = runtime
            .module_manager
            .create_discovered_module(
                child_name,
                RealDirectoryPath::new(child_root_string),
                RealFilePath::new(child_config_string),
                ProjectHierarchy::Submodule,
                Some(owner_module_id),
            )
            .map_err(|message| {
                repository_error(message, &config_path.to_string_lossy(), export.line)
            })?;
        let target = ImportTarget::Module(child_module_id);
        runtime
            .module_manager
            .module_mut(owner_module_id)
            .expect("manifest owner module should exist")
            .exports
            .insert(
                export.name.clone(),
                ExportEntry::Module {
                    name: export.name.clone(),
                    module_id: child_module_id,
                },
            );
        mount_stack.push(child_module_id);
        let discovery = discover_module_config(
            runtime,
            child_module_id,
            &child_config_path,
            child_config,
            mount_stack,
        );
        mount_stack.pop();
        discovery?;
        return Ok(target);
    } else {
        return Err(repository_error(
            format!(
                "[export] target `{}` does not exist",
                target_path.to_string_lossy()
            ),
            &config_path.to_string_lossy(),
            export.line,
        ));
    }
}
