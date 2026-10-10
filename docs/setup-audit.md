# Setup and CLI verification — 2026-10-10

This audit checks `setup.md`, `setup_zh.md`, `cli.md`, and `cli_zh.md`.
It is not an acceptance of every platform installer or the published release.

## Observed behavior and documentation correction

The current macOS ARM source build reports `Litex 1.0.6-beta`.
`cargo build --release` succeeded. A task-local installation layout copied the
current executable and standard library into `bin/litex` and `bin/std`.
Its smoke project ran from a separate directory with no local `std/`.
This was an empty compatibility-module loading check: `quot` and `$dvd` are
native vocabulary and do not depend on declarations in std. Ordinary use
without `[import std]` needs no std path configuration.

`litex.config`:

```ini
[import std]
basics
[export]
smoke = "./smoke.lit"
```

`smoke.lit`:

```litex
quot(-7, 3) = -3
$dvd(12, 3)
```

Before configuring the standard-library path, `litex -f smoke.lit` exited 1
with `success: false` and `session_error: "failed to import project"`.
Setting `LITEX_STD_PATH` to the absolute copied `bin/std` path made
`litex -lang en -f smoke.lit` exit 0 with `kind: "run"`, `success: true`, and
`session_error: null`. The strict-mode run passed too.

The former setup guide tested only `litex -e '1 = 1'`, which does not import
std. Both setup languages now configure std for Homebrew, Debian, Scoop,
and manual Windows archives, and include the actual import smoke above.
The standard-library discovery contract is in
[`src/run_module/load_config.rs`](../src/run_module/load_config.rs).
The package layouts were inspected in
[the release workflow](../.github/workflows/deploy.yml); inspecting a workflow
is not proof that those packages were published or installed successfully.

The separately installed Homebrew binary reports
`Litex Kernel: litex 0.9.88-beta`. Its `-e '1 = 1'` succeeds, but its JSON
contains `result: "success"` rather than the current Normal run envelope.
Its installed formula places std under `share/litex/std`; the cached tap's
0.9.113-beta formula and the current workflow use `bin/std`.
The guides now explain version differences and the older layout fallback.
These cached versions do not establish the current remote tap version.

## Commands exercised on macOS ARM

27 checks covered the two binary versions, old installed eval, failed std
lookup, configured std import (normal and strict), quoted inline equality,
arithmetic and negative operands, trailing shared flags, standalone `-f`,
Chinese and French JSON, bare REPL, `-session -f`, `-session -e`, and these
checkout-relative commands:

```bash
litex -f examples/claim_obtain_scope.lit
litex -strict -f examples/claim_obtain_scope.lit
litex -r examples/module_manager/repo
litex -session -f examples/claim_obtain_scope.lit
litex -strict -lean -f lean/examples/real_is_complex/statement.lit
litex -extractpython '-2 < 0'
litex -extractc '1 = 1'
litex -latex -lang zh -e '1 = 1'
litex -latex -document -lang zh -f example.lit
litex -help
```

The checkout-relative commands used the current-source executable explicitly.
`example.lit` contained `1 + 1 = 2`. REPL checks submitted `1 = 1`, then `exit`.
Normal batch gates checked exit status, parsed JSON, and the success envelope;
localized gates checked localized success keys. Unsupported `-compact` was
also checked: launch rejection and exit 2. Lean emission was exercised, not
Lean kernel verification; LaTeX conversion was exercised, not TeX compilation.
The CLI command table now includes `-latex`, and the guides distinguish
checkout paths from files shipped with an installed package.

The Scoop path command was checked against the official
[Scoop command reference](https://github.com/ScoopInstaller/Scoop/wiki/Commands),
which defines `prefix` as returning an app's installation path. Its execution
and the Litex bucket's current remote contents were not verified here.

## Remaining installation acceptance

- Fresh Homebrew installation/upgrade and persistence in a new terminal.
  Homebrew cache writes are denied in this environment; direct downloads
  failed against the configured local proxy. No system installation or user
  shell startup file was changed.
- Debian/Ubuntu amd64 and arm64: download the selected release's actual `.deb`,
  install via `dpkg`, set `/usr/share/litex/std`, then run both executable and
  external-project std checks. Docker daemon access was denied on this host.
- Linux Homebrew amd64 and arm64: install from the tap and repeat those checks.
- Windows amd64: install via Scoop or extract the actual release archive,
  configure std and PATH, then repeat the checks in a new PowerShell terminal.
  No Windows or PowerShell runtime was available here.
- Intel macOS is outside the current workflow's native artifact matrix.
- Verify current remote release assets, hashes, tap, and Scoop manifest with
  working download access; cached browser release listings are insufficient.

The copied native layout establishes current executable/std behavior, not
Homebrew install hooks, Debian installation, Windows execution, release asset
availability, or persistent environment setup. No kernel or release workflow
code was changed for this audit.


## Follow-up: a real declaration imported from std

The follow-up used the user’s requested probe, not an empty-module arithmetic
check. Temporarily adding this line to the actual `std/basics/main.lit`:

```litex
let version = 1
```

made an external project with `[import std] basics` verify:

```litex
basics:::version = 1
basics::main::version = 1
```

The actual source file was restored byte-for-byte after that strict check.
The sustained session, clean runs, and packaging checks used an isolated
nonempty module copy under `tmp/2026-10-10/std-import-distribution/`.
Both qualified forms succeeded; `basics:::version = 2` failed normally, and
`basics:::version = 1` still succeeded in that same live session.

Nineteen clean CLI checks verified strict and normal imports, two successive
normal runs, both qualified forms, an alias (`B = basics`), cwd/project-local
std, environment override, declaration removal and restoration, and a native
archive round trip through the existing release archive writer/extractor.
Without the import, without the declaration, or with an invalid std path,
the declaration consumer failed. A bare `version = 1` did not acquire the
imported name. Normal-run source deletion also rejected the old declaration;
restoring source restored acceptance. This checks observable cache invalidation,
not whether any particular successful run was a cache hit.

The native archive and a copied Homebrew `bin/std` layout both retained and
exposed the new declaration when configured. From an external directory,
placing std beside the executable alone did not make discovery succeed.
These are native layout checks, not execution of `brew install` or a Windows
installer. WiX fragment generation included `std\basics\main.lit`, installed
std below `APPLICATIONFOLDER`, and linked `LitexStd` from the product feature.
Actual MSI compilation and installation were not executed.

### Runtime mechanism

std is a filesystem module tree, separate from the binary. `[import std]`
selects `<std_root>/<module-name>`; the selected module’s `litex.config`
orders its `.lit` exports. Imports follow ordinary module verification and
publication rules. `basics:::version` is shorthand for
`basics::main::version` because `basics` has exactly one export, named `main`.
The declaration is not imported as a global bare `version`.

[`resolve_std_root`](../src/run_module/load_config.rs) prioritizes
`LITEX_STD_PATH`, then cwd `std/`, then the target project’s `std/`.
A configured invalid environment path overrides valid local std; it does not
fall back. There is no executable-relative or system install-directory search.
[`run_import_module`](../src/run_module/run_import_module.rs) loads exports;
ordinary runs may reuse fingerprinted on-disk knowledge caches, whereas strict
imports re-execute source. The mathematical module source is distributable
with the corresponding binary; it is not embedded in that executable.

### Distribution configured in the current repository

| Channel | Binary and std placement | Boundary |
| --- | --- | --- |
| Unix tar.gz / Windows ZIP | Root `litex` / `litex.exe` and root `std/`, copied from the same release checkout | Current workflow structure; remote artifacts not downloaded here |
| Homebrew | Formula installs `bin/litex` and `bin/std/` from the Unix archive | Runtime discovery still needs local std or an explicit path |
| Debian .deb | `/usr/local/bin/litex` and `/usr/share/litex/std` | Install smoke explicitly supplies `LITEX_STD_PATH` |
| Scoop | Extracts the Windows ZIP with `litex.exe` and `std/`; provides the executable shim | Generated manifest does not persist the std environment variable |
| MSI | Binary under application `bin/`; std under application `std/` via WiX component group | Optional build; not attached to the current GitHub Release |
| Docker | `/usr/local/bin/litex` and `/usr/share/litex/std` | Image sets `LITEX_STD_PATH` |
| cargo install | Cargo installs the executable | There is no std installation hook; users must provide std separately if importing it |

Packaging and upload evidence is in
[deploy.yml](../.github/workflows/deploy.yml),
[generate_wix_std.py](../.github/scripts/release/generate_wix_std.py), and
[Dockerfile](../Dockerfile). The release upload job depends on build and .deb
jobs, downloads binary/deb artifacts, and lists only `.tar.gz`, `.zip`, and
`.deb`; it neither downloads the `msi` artifact nor attaches `.msi`.
The MSI job uses `continue-on-error: true`, so release success alone does not
establish MSI availability. No publishing configuration was changed here.

The setup and CLI guides now distinguish optional empty-module compatibility
imports from native mathematical vocabulary. Full fresh installation acceptance
on Linux and Windows remains outside this macOS audit’s evidence.
