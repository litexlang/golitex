# new_pipeline module management

Design target for `new_pipeline` module loading. This supersedes the older
module / submodule tree for the new pipeline. Legacy `module_system` and public
CLI docs may still describe the old shape until migration catches up.

## Goal

Keep one flat unit of composition: a **module**. Nesting is done by **importing
modules**, not by exporting child module folders. There is no hierarchy
keyword and no submodule.

## Core rules

1. There is **no `submodule`** and **no `[hierarchy]`** section.
2. A maintained directory is a **module** when it has a `litex.config`.
3. **`[export]` may name only `.lit` files** (ordered, explicit selection list).
   It must not export a child directory / nested config node.
4. **`[import]` may mount another module** (a directory whose config is a
   module). Import targets modules, not individual `.lit` files.
5. **`[import std]`** mounts an installed standard package, same as before.
6. Source `.lit` files still reject `import` as a statement. Reproducible
   dependencies stay in `litex.config`. Interactive REPL import remains a
   terminal command only.

## Manifest shape (target)

```ini
[import]
Algebra = "../Algebra"

[import std]
basics

[export]
chap1 = "./chapter01.lit"
chap2 = "./chapter02.lit"
chap3 = "./chapter03.lit"
```

Invalid under the new design:

```ini
[export]
# child folder / nested config — not allowed
Part2 = "./Part2"
```

```ini
[hierarchy]
submodule
```

```ini
[hierarchy]
module
```

## Asymmetry: export vs import

| Direction | Allowed target | Meaning |
|---|---|---|
| export | `.lit` file only | Ordered public file surface of this module |
| import | another module | Mount that module's completed world under an alias |
| import std | installed std package | Mount a standard library package |

So: you cannot export a module folder into your export table, but you can
import a sibling or external module and cite it by its mount alias.

## How larger projects compose

Old model: one root module exported a mix of `.lit` files and submodule
folders; submodules could re-export further children.

New model:

- Each independently runnable / importable package is its own module.
- A consumer module lists those packages under `[import]`.
- Inside one module, the public file list is a flat ordered `[export]` of
  `.lit` paths only.
- Unlisted files and folders remain sidecars: not parsed, not executed, not
  in the module namespace, unless some other module mounts them.

Canonical names follow the mount alias and export name, for example
`Algebra::chap1::name` or `basics::name` after `[import std] basics`.

## Run order (conceptual; not wired in new_pipeline yet)

Within one module:

1. Resolve and run each `[import]` / `[import std]` mount (each imported module
   runs under its own rules).
2. Run this module's `[export]` `.lit` files left to right.
3. `litex -f <file>` on a registered export runs the same prefix through that
   file, then that file.
4. `litex -r <module>` runs the full ordered export list of that module after
   its imports.

There is no “trace back through a submodule parent chain” path, because there
are no submodules. Cross-package dependency is only via import of modules.
`new_pipeline` does not implement `-r` / project `-f` mount yet.

## Ownership in `ModuleManager` (code-facing)

Current shape:

- `export_files_and_their_env` — completed export `.lit` files and their envs
- `import_repos` — mounted imported modules (`ModuleManager` instances)
- `import_std` — mounted std packages

Completed environments stay on the node that executed them; imported modules
are not merged into the importer’s export list. Import alias / path wrappers
may be added later; they are intentionally deferred.

## Explicit non-goals / not carried forward

- No `submodule`.
- No `[hierarchy]` section.
- No exporting a configured child directory from `[export]`.
- No importing a single `.lit` file as a package.
- `flatten` is not part of this design.
- `-r` / project `-f` wiring is deferred.
