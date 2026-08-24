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
[`manager_state.rs`](manager_state.rs) for the per-run module registry, and
[`module_runner.rs`](module_runner.rs) for the execution graph.
