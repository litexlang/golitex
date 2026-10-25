# Release packaging and installed std checks

Run the native release lane before pushing a version tag:

```bash
python3 .github/scripts/release/preflight.py
```

It builds with `--locked`, packages the binary and clean std source, extracts
the archive, checks `Litex <version>`, and imports a real std declaration from
an external project with `LITEX_STD_PATH` unset. The temporary declaration
`let litex_distribution_probe = 1` is appended to the extracted basics module
and restored byte-for-byte in a `finally` block. Read-only probe files (including
Homebrew's installed source) temporarily gain owner write permission; the
original permissions are restored as well. The consumer verifies
`basics::main::litex_distribution_probe = 1` in strict mode, so empty-module
loading or native arithmetic alone cannot satisfy the package check.
Tool-managed `private/release-preflight.*` directories are removed on success
and ordinary failure. Production `std/basics` remains an empty compatibility
module; native vocabulary does not require that module.

To check a previously built archive or an installed package:

```bash
python3 .github/scripts/release/preflight.py --archive <archive> --version <Cargo-version>
sudo python3 .github/scripts/release/preflight.py \
  --installed-binary /usr/local/bin/litex --std /usr/share/litex/std
```

The installed check temporarily writes the probe into its supplied std path;
run as the installation owner (or with the privileges needed to update that file).
The probe contents and permissions are restored even when verification or binary
launch fails. If the file cannot be opened for probing, its contents are left
untouched and any temporary permission change is reverted. `--std` locates the
file for inventory/probing, not a runtime environment override: the child process
must discover std itself.

## Runtime discovery and distribution

The runtime keeps the established precedence: explicit `LITEX_STD_PATH`, cwd
`std/`, then target-project `std/`. If none selects an existing local directory,
it follows the real executable through symlinks and searches these installed
layouts, in order:

1. executable-directory `std/` (archives, Scoop, current Homebrew);
2. installation-prefix `std/` (MSI's application `bin/` sibling);
3. prefix `share/litex/std/` (legacy Homebrew and `/usr/bin` layouts);
4. parent-prefix `share/litex/std/` (`/usr/local/bin` with Debian `/usr/share`).

An invalid explicit override remains an error. Installing std does not import
its names automatically; project manifests still select modules explicitly.
`package_std.py` is the shared source inventory for archive, Debian, Docker and
WiX packaging. It excludes knowledge caches, hidden drafts/metadata and local
`todo.md` files. Binary and std are taken from the same release checkout.

The Windows MSI is required. Its WiX fragment links every std file into the
product feature, and its installation must pass the same external-project
probe. The Release job depends on MSI success, downloads the MSI artifact,
attaches `.msi` alongside `.tar.gz`, `.zip` and `.deb`, and fails if an expected
asset class is missing. WiX 3.14.1 and cargo-wix 0.3.9 are pinned.

## Native gates and publishing boundary

The build matrix executes archive and installed-layout tests on macOS ARM,
Linux amd64/arm64, and Windows amd64 with `fail-fast: false`, so one platform
failure does not cancel the others. Both Debian architectures have a native
installation/probe job. Each Unix build also installs its archive through the
actual generated Homebrew formula, and the Windows build installs its ZIP
through the generated Scoop manifest. `package_manager_smoke.py` supplies the
archive via a loopback server, checks installed std, then removes only that
test installation; its Homebrew tap edits are restored. Cleanup queries actual manager state,
including an installation command that failed after creating the package.
Homebrew / Docker / web-server smokes assert the current run JSON contract
(`run_result`, `session_terminated`, `termination`, non-empty accepted
`statement_results`), not the retired `success` / `session_error` fields.
Repo-local Docker and examples smokes call `preflight.py --assert-run-json`
so that contract stays shared. No manifest is published. The Homebrew setup action is pinned to the official
2026.07.10.1 revision, rather than a moving branch. Linux uses Ubuntu 22.04 runners rather than building
against a newer Ubuntu libc than the Debian bookworm runtime.

`Deploy` supports `workflow_dispatch`: it derives the version from Cargo,
builds/packages/tests, and uploads Actions artifacts without publishing a
GitHub Release, crates.io package, tap, Scoop bucket, Docker image or web-server
installation. Tag pushes use the exact Cargo version without leading `v` and
perform publishing only after the required jobs succeed. This manual run is
the validation path for a proposed release, not a substitute for executing it.

`installed_std_cli` holds a mutex for each installation fixture's lifetime,
including copying, child-process execution and cleanup. This prevents parallel
fork/exec from inheriting another fixture's writable executable descriptor and
causing a transient Linux `ETXTBSY` at launch (Rust issue
[114554](https://github.com/rust-lang/rust/issues/114554)). All layout, symlink,
precedence and failure assertions still run; launch errors remain test failures.

Local quality gates:

```bash
cargo fmt --all -- --check
python3 .github/scripts/release/test_preflight.py
cargo test --release --all-targets --locked
cargo package --list --allow-dirty --locked --offline
```

The `reading_http` suite requires real loopback sockets. Its early-rejection
regression sends 64 KiB request bodies and checks complete HTTP error responses,
including their declared byte lengths. Run it repeatedly before release when
changing the reader's connection lifecycle; a single successful run can miss
packet-timing failures. Connection resets and truncated responses remain failures.

Run the registered real-Lean gates too before release. Cargo test names
alone do not establish their execution. Local textbook projects under `scripts/`
are optional and are not release prerequisites. Run them only when the user
explicitly requests textbook work or verification; their absence, failures, or
timeouts alone are not release blockers. The combined
`.github/scripts/predeploy_gate.py` includes those projects and must not be used
as a mandatory release gate. See the release-scope rule in `AGENTS.md`.

A native macOS check cannot establish
Windows MSI execution or Linux runtime compatibility. Remote publication also
needs `CRATES_IO_TOKEN`, `HOMEBREW_TAP_TOKEN`, `SCOOP_BUCKET_TOKEN`, and the
`WEB_DEPLOY_*` secrets; local CLI authentication does not prove those secrets.

Docker currently sets `LITEX_STD_PATH=/usr/share/litex/std` in its image and
checks the published amd64 image. Actual arm64 Docker execution remains a
separate gate. Intel macOS is outside the current artifact matrix.

## Historical audit records

The following observations apply to their named earlier snapshots, not the
current automatic-discovery and mandatory-MSI implementation.

On 2026-10-08 the local release audit passed Rust formatting, nine Python
preflight tests, 1,260 release-mode Rust tests at the 1.0.2-beta source snapshot,
native 1.0.2-beta archive checks with an invalid inherited std path,
installed-layout smoke with an explicit std path, five prerelease-tag cases,
YAML parsing, Bash syntax checks, and generated Ruby syntax checks. Package listing
contained no `scripts/`, `tmp/`, `private/`, or `todo/` paths. Removing the std
environment variable in an unrelated directory reproduced an import failure.
GitHub CLI was not authenticated; Docker daemon access was denied. Windows,
Linux runtime, remote secrets, and actual publishing were not verified locally.
Scoop updates skip an empty commit on rerun. Prerelease detection handles any
SemVer prerelease suffix, and ignores hyphens in build metadata.
Other work changed `src/prelude.rs` and `lean/Litex.lean` after the Rust test
gate. Those changes are outside this audit's acceptance; formatting was checked
again successfully. Run the quality gates against the final commit before tagging.

MSI linkage repair: the local 12-test Python suite passed on 2026-10-08.
The generated fragment includes all four currently shipped std files. Actual
WiX linking and MSI installation were not run on this macOS host; validate
the repaired workflow on Windows before calling the installer accepted.
Package boundary and diff whitespace checks passed. The current worktree's
broader release checks are not green: formatting reports pre-existing Rust
edits, and Rust compilation reports `EvalRational::zero()` as unavailable in
`src/compile_to_lean/compile_run.rs:309`. These files were already modified
before the MSI repair and were not edited as part of it.
