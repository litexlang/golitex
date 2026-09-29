# module-manager examples

Small projects that exercise **config mount + LaunchCommand** under
the Litex CLI. Design write-up:
[`src/run/README.md`](../../src/run/README.md).

## Layout

```text
repo/                 -r <this-dir>
  litex.config        imports sibling ../lib_pkg as Lib
  main.lit            root export

lib_pkg/              external module imported by repo/
  litex.config
  base.lit

export_order_repo/    -r ordered exports + submodule A (former 08_*)
trusted_template_prefix/  -r trusted prefix then instantiate template (former 09_*)
import_alias_qualified_arithmetic/  -f main with gf import alias

file_prefix/          -f a.lit  (listed export; later export must not run)
  litex.config
  a.lit
  b.lit               intentionally failing if ever run

file_extra/           intended: -f unlisted scratch after full mount
  litex.config        (current binary requires export; see Known debt)
  a.lit
  scratch.lit

cwd_eval/             cd here, then -e '1 = 1'
  litex.config
  main.lit

isolated/             -f alone.lit with no litex.config
  alone.lit
```

## Acceptance

```bash
export BIN=target/debug/litex   # or target/release/litex

$BIN -r examples/module_manager/repo
$BIN -r examples/module_manager/export_order_repo
$BIN -r examples/module_manager/trusted_template_prefix
$BIN -f examples/module_manager/import_alias_qualified_arithmetic/main.lit
$BIN -f examples/module_manager/file_prefix/a.lit
$BIN -f examples/module_manager/isolated/alone.lit
(cd examples/module_manager/cwd_eval && ../../../$BIN -e '1 = 1')
```

Each command above should exit `0`.

Negative checks (expect non-zero):

```bash
$BIN -f examples/module_manager/file_prefix/b.lit
(cd examples/module_manager/file_prefix && ../../../$BIN -e '1 = 1')
```

## Known debt

`file_extra/scratch.lit` is intentionally **not** listed in `[export]`. Design
in `src/run/README.md` says `-f` should run all exports then the extra file;
the current binary requires the `-f` target to be exported. Keep the fixture;
do not treat it as a green acceptance case until that path is restored.

## Run all positive cases

```bash
export PATH="/usr/bin:/bin:$PATH"
BIN="${BIN:-target/debug/litex}"
fail=0
$BIN -r examples/module_manager/repo || fail=1
$BIN -r examples/module_manager/export_order_repo || fail=1
$BIN -r examples/module_manager/trusted_template_prefix || fail=1
$BIN -f examples/module_manager/import_alias_qualified_arithmetic/main.lit || fail=1
$BIN -f examples/module_manager/file_prefix/a.lit || fail=1
$BIN -f examples/module_manager/isolated/alone.lit || fail=1
(cd examples/module_manager/cwd_eval && ../../../$BIN -e '1 = 1') || fail=1
exit $fail
```
