# Module-manager examples

Small projects exercise config mount and LaunchCommand under the release CLI.
Current contracts: [module management](../../src/module_manager/README.md)
and [launch flow](../../src/run/README.md).

## Layout

| Project | Contract |
| --- | --- |
| `repo/` and `lib_pkg/` | Import a sibling module as `Lib`; use its qualified definitions and theorems. |
| `export_order_repo/` | Import `A` before ordered root exports; preserve canonical module/export names. |
| `trusted_template_prefix/` | Load an earlier checked generic template, then instantiate it from the later export. |
| `import_alias_qualified_arithmetic/` | Qualified arithmetic using the `gf` import alias. |
| `qualified_struct_views/` | Full and flattened qualified struct carriers, generic arguments, function returns and nested field types. |
| `identifier_resolution/` | Distinct same-named exports and unknown-name rejection. |
| `file_prefix/` | Selecting `a.lit` stops before the deliberately false `b.lit`. |
| `file_extra/` | An unlisted `scratch.lit` requested with `-f` runs after all exports. It is not an export namespace. |
| `cwd_eval/` | `-e` mounts the directory-local config first. |
| `isolated/` | Run a file with no config. |

Legacy `[hierarchy]` headers were removed. Config directory dependencies belong
in `[import]`; `[export]` contains ordered `.lit` files only. Within imported
`A`, `chap2::x` refers to that module's own export; from the root, the same
symbol is `A::chap2::x`.

## Acceptance

Run from the Git root. Every positive requires exit `0`, JSON `success: true`,
and no session error. Use an absolute binary path for changed-directory runs.

```bash
BIN="$PWD/target/release/litex"
"$BIN" -strict -r examples/module_manager/repo
"$BIN" -strict -r examples/module_manager/export_order_repo
"$BIN" -strict -f examples/module_manager/trusted_template_prefix/main.lit
"$BIN" -strict -f examples/module_manager/qualified_template_names/main.lit
"$BIN" -strict -f examples/module_manager/qualified_struct_views/main.lit
"$BIN" -strict -f examples/module_manager/file_prefix/a.lit
"$BIN" -strict -f examples/module_manager/file_extra/scratch.lit
"$BIN" -strict -f examples/module_manager/isolated/alone.lit
(cd examples/module_manager/cwd_eval && "$BIN" -strict -e '1 = 1')
```

Negative checks require exit `1` and JSON `success: false`:

```bash
"$BIN" -strict -f examples/module_manager/file_prefix/b.lit
(cd examples/module_manager/file_prefix && "$BIN" -strict -e '1 = 1')
(cd examples/module_manager/export_order_repo && "$BIN" -strict -e 'unlisted_sidecar::unlisted_sidecar_value = 2')
```

The last check executes the old `try:` assertion as a real subprocess negative.
Unlisted `notes/` and `unlisted_sidecar.lit` remain in place; they never become
exports merely because they exist beside the config. An explicit extra-file
launch and an exported namespace are different operations.

## Qualified definition publication

The arithmetic consumer explicitly publishes imported object definitions before
using their scalar types, tuple coordinates and cart dimension:

```litex
release obj def gf::main::a
release obj def gf::main2::b
release obj def gf::main::pair
release obj def gf::main2::pair
release obj def gf::main::ProductSet
gf::main::a + gf::main::a = gf::main2::b
```

The original assertions and configured dependency owner are preserved. The
strict configured `-r` gate now passes; the file gate is
`-strict -f examples/module_manager/import_alias_qualified_arithmetic/main.lit`.
The release steps are checked authoring, not a module lookup or cache change.

[`eval_mount_failure/check.py`](eval_mount_failure/check.py) checks that failed
cwd mounts emit a structured `FailToImport` result without executing requested
eval code, and that the healthy cwd-eval control still succeeds.

`struct_law_publication/main.lit` checks definition-local universal laws, followed
by existential consumption of an imported instance after `release struct def`.
Imported facts do not automatically become ambient root facts. Structs with laws
use source fallback until definitions-only KB products can restore the published
foralls. Qualified carrier syntax such as `&L::base::RightZero<R>` uses the same canonical
owner lookup as template names. The dedicated
[qualified struct fixture](qualified_struct_views/README.md) verifies current-export,
full import and single-export paths with their type and path rejection controls.
