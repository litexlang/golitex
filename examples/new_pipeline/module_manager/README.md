# new_pipeline module-manager examples

Small projects that exercise **config mount + LaunchCommand** under
`LITEX_NEW_PIPELINE=1`. Design write-up:
[`src/new_pipeline/run/README.md`](../../src/new_pipeline/run/README.md).

## Layout

```text
repo/                 -r <this-dir>
  litex.config
  lib/                imported module
  main.lit            root export

file_prefix/          -f a.lit  (listed export; later export must not run)
  litex.config
  a.lit
  b.lit               intentionally failing if ever run

file_extra/           -f scratch.lit  (not in [export]; after full mount)
  litex.config
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
export LITEX_NEW_PIPELINE=1
BIN=target/debug/litex   # or target/release/litex

$BIN -r examples/new_pipeline/module_manager/repo
# repo/main.lit also checks cross-mod `release thm` / `by thm` / `by def`
$BIN -f examples/new_pipeline/module_manager/file_prefix/a.lit
$BIN -f examples/new_pipeline/module_manager/file_extra/scratch.lit
$BIN -f examples/new_pipeline/module_manager/isolated/alone.lit
(cd examples/new_pipeline/module_manager/cwd_eval && ../../../../$BIN -e '1 = 1')
```

Each command above should exit `0`.

Negative checks (expect non-zero):

```bash
# b.lit is 1 = 2; -f a.lit must not reach it (exit 0). Running b alone fails:
$BIN -f examples/new_pipeline/module_manager/file_prefix/b.lit
# mount soft-fail for -e when cwd export fails:
(cd examples/new_pipeline/module_manager/file_prefix && ../../../../$BIN -e '1 = 1')
```

## Run all positive cases

```bash
export LITEX_NEW_PIPELINE=1 PATH="/usr/bin:/bin:$PATH"
BIN="${BIN:-target/debug/litex}"
fail=0
$BIN -r examples/new_pipeline/module_manager/repo || fail=1
$BIN -f examples/new_pipeline/module_manager/file_prefix/a.lit || fail=1
$BIN -f examples/new_pipeline/module_manager/file_extra/scratch.lit || fail=1
$BIN -f examples/new_pipeline/module_manager/isolated/alone.lit || fail=1
(cd examples/new_pipeline/module_manager/cwd_eval && ../../../../$BIN -e '1 = 1') || fail=1
exit $fail
```
