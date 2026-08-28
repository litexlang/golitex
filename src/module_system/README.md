# Modules, imports, and ordered files

This `litex.config` example defines one module whose `main.lit` runs before `theorem.lit`:

```toml
[hierarchy]
module

[export]
main = "./main.lit"
theorem = "./theorem.lit"
```

```text
discover litex.config
  -> parse hierarchy/import/export tables
  -> assign ModuleId and FileId values
  -> resolve imports and recursive child modules
  -> run [export] entries in source order
  -> mark each file/module Loading, Loaded, or Stopped
  -> reject a cycle when a Loading target is entered again
```

## Examples and boundaries

| Configuration | Behavior |
| --- | --- |
| `[export] main = "./main.lit"` | Registers one ordered source file. |
| `[import]`<br>`MILAlternative = "../textbook2"` | Resolves the sibling module under the local alias `MILAlternative`. |
| Two exports with the same name `main` | Rejected as a duplicate config name. |
| An export path outside the recursive tree | Rejected instead of running an unregistered file as a project prefix. |
| `A` imports `B` and `B` imports `A` | Rejected through `Loading` cycle state. |

Start with [`project_config.rs`](project_config.rs) for the TOML-like tables,
[`registry.rs`](registry.rs) for the per-run module registry, and
[`module_records.rs`](module_records.rs) for the execution graph.

Repository discovery is a concept directory rather than a single mixed file.
Start with
[`repository_discovery/repository_entry.rs`](repository_discovery/repository_entry.rs)
for the requested entry point,
[`repository_discovery/module_config.rs`](repository_discovery/module_config.rs)
for recursive module loading, and
[`repository_discovery/config_imports.rs`](repository_discovery/config_imports.rs)
or
[`repository_discovery/config_exports.rs`](repository_discovery/config_exports.rs)
for the two config edge types. Filesystem authorization, standard-library
selection, import cycles, and terminal imports each have their own named file
in [`repository_discovery/`](repository_discovery).
