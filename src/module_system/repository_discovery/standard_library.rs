//! Standard-library roots, module discovery, and configured imports.

use super::*;

pub fn discover_terminal_std_import(
    runtime: &mut Runtime,
    package_name: &str,
    line_file: LineFile,
) -> Result<ModuleId, RuntimeError> {
    let importing_module_id = runtime.current_module_id();
    let source_path = line_file.1.as_ref();
    let std_root = resolve_std_root()
        .map_err(|message| repository_error(message, source_path, line_file.0))?;
    let mut mount_stack = vec![importing_module_id];
    let module_id = discover_std_module_with_mount_stack(
        runtime,
        importing_module_id,
        &std_root,
        package_name,
        &mut mount_stack,
    )?;
    reject_unauthorized_project_references(runtime)?;
    let import_edges = config_import_edges(runtime);
    reject_cyclic_module_imports(runtime, &import_edges)?;
    Ok(module_id)
}

pub fn resolve_std_root() -> Result<PathBuf, String> {
    let configured_root = env::var("LITEX_STD_PATH").ok().map(PathBuf::from);
    let current_dir = env::current_dir().ok();
    let executable = env::current_exe().ok();
    for root in standard_library_root_candidates(configured_root, current_dir, executable) {
        if root.is_dir() {
            return Ok(root);
        }
    }
    Err("standard library was not found; searched LITEX_STD_PATH, ./std, and the executable installation paths".to_string())
}

pub(super) fn discover_std_module_with_mount_stack(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    std_root: &Path,
    package_name: &str,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ModuleId, RuntimeError> {
    let canonical_std_root =
        canonical_directory(&std_root.to_string_lossy(), &std_root.to_string_lossy(), 0)?;
    let single_file_path = canonical_std_root.join(format!("{}.lit", package_name));
    if single_file_path.is_file() {
        return discover_std_single_file_module(
            runtime,
            owner_module_id,
            &canonical_std_root,
            &single_file_path,
            package_name,
            mount_stack,
        );
    }
    let package_root = canonical_std_root.join(package_name);
    let canonical_package_root = canonical_directory(
        &package_root.to_string_lossy(),
        &canonical_std_root.to_string_lossy(),
        0,
    )?;
    let config_path = require_project_config(
        &canonical_package_root,
        &canonical_std_root.to_string_lossy(),
        0,
    )?;
    let config = read_project_config(&config_path)?;
    if config.hierarchy != ProjectHierarchy::Module {
        return Err(repository_error(
            format!(
                "standard package `{}` must declare `module` under [hierarchy]",
                package_name
            ),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    let package_root_string =
        path_string(&canonical_package_root, &config_path.to_string_lossy(), 0)?;
    let config_path_string = path_string(&config_path, &config_path.to_string_lossy(), 0)?;
    let owner_name = runtime
        .module_manager
        .module(owner_module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    let local_name = package_name.to_string();
    let module_name = join_module_name(owner_name.as_str(), local_name.as_str());
    reject_active_mount_cycle(
        runtime,
        mount_stack,
        package_root_string.as_str(),
        module_name.as_str(),
        "cyclic standard package import",
        &config_path,
        0,
    )?;
    if let Some(existing_module_id) = runtime
        .module_manager
        .module_id_by_root_path(&RealDirectoryPath::new(package_root_string.clone()))
    {
        return Ok(existing_module_id);
    }
    let std_module_id = runtime
        .module_manager
        .create_discovered_standard_module(
            module_name,
            RealDirectoryPath::new(package_root_string),
            RealFilePath::new(config_path_string),
            ProjectHierarchy::Module,
            None,
        )
        .map_err(|message| repository_error(message, &config_path.to_string_lossy(), 0))?;
    mount_stack.push(std_module_id);
    let discovery =
        discover_module_config(runtime, std_module_id, &config_path, config, mount_stack);
    mount_stack.pop();
    discovery?;
    Ok(std_module_id)
}

pub(super) fn discover_std_single_file_module(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    std_root: &Path,
    source_path: &Path,
    package_name: &str,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ModuleId, RuntimeError> {
    let canonical_source_path = canonical_file(source_path, &std_root.to_string_lossy(), 0)?;
    let source_path_string = path_string(&canonical_source_path, &std_root.to_string_lossy(), 0)?;
    let owner_name = runtime
        .module_manager
        .module(owner_module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    let local_name = package_name.to_string();
    let module_name = join_module_name(owner_name.as_str(), local_name.as_str());
    reject_active_mount_cycle(
        runtime,
        mount_stack,
        source_path_string.as_str(),
        module_name.as_str(),
        "cyclic standard package import",
        &canonical_source_path,
        0,
    )?;
    if let Some(existing_module_id) = runtime
        .module_manager
        .module_id_by_root_path(&RealDirectoryPath::new(source_path_string.clone()))
    {
        return Ok(existing_module_id);
    }
    let module_id = runtime
        .module_manager
        .create_discovered_standard_module(
            module_name,
            RealDirectoryPath::new(source_path_string.clone()),
            RealFilePath::new(source_path_string),
            ProjectHierarchy::Module,
            None,
        )
        .map_err(|message| {
            repository_error(message, &canonical_source_path.to_string_lossy(), 0)
        })?;
    Ok(module_id)
}

pub(super) fn discover_config_std_import(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    import: ProjectStdImport,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ConfigImport, RuntimeError> {
    let std_root = resolve_std_root().map_err(|message| {
        repository_error(message, &config_path.to_string_lossy(), import.line)
    })?;
    let std_module_id = discover_std_module_with_mount_stack(
        runtime,
        owner_module_id,
        &std_root,
        &import.name,
        mount_stack,
    )?;
    Ok(ConfigImport {
        name: import.name,
        module_id: std_module_id,
        kind: ConfigImportKind::Standard,
        line_file: (
            import.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        ),
    })
}

pub(super) fn standard_library_root_candidates(
    configured_root: Option<PathBuf>,
    current_dir: Option<PathBuf>,
    executable: Option<PathBuf>,
) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Some(root) = configured_root {
        roots.push(root);
    }
    if let Some(dir) = current_dir {
        roots.push(dir.join("std"));
    }
    if let Some(parent) = executable.as_deref().and_then(Path::parent) {
        roots.push(parent.join("std"));
        roots.push(parent.join("..").join("std"));
        roots.push(parent.join("..").join("share").join("litex").join("std"));
        roots.push(
            parent
                .join("..")
                .join("..")
                .join("share")
                .join("litex")
                .join("std"),
        );
    }
    roots
}
