# Local release preflight

Run the native release lane before pushing a version tag:

```bash
python3 .github/scripts/release/preflight.py
```

The command reads the package version and Rust host target, builds the release
binary inside a unique `private/release-preflight.*` directory, packages the
binary together with `std/`, extracts that archive, checks the binary version,
and runs the same archive smoke test used by the GitHub release workflow. The
temporary directory is removed on both success and ordinary failure.

The version check requires exit code zero and the documented plain-text output
`Litex <version>` from `-version`; the smoke test requires Normal run JSON.
The extracted smoke project imports `basics` through `litex.config` and exports
`smoke.lit`; imports are not statements in Litex source.
The archive smoke overrides any inherited `LITEX_STD_PATH` with the extracted
standard library, so a local installation cannot mask a broken release archive.
Local builds use `--locked`, matching the workflow's dependency lockfile gate.

To check an archive that has already been built:

```bash
python3 .github/scripts/release/preflight.py \
  --archive litex_0.9.116-beta_darwin_arm64.tar.gz \
  --version 0.9.116-beta
```

Focused tests:

```bash
python3 .github/scripts/release/test_preflight.py
```

This is a native-lane preflight, not an emulator for every GitHub runner. A
macOS ARM host verifies the `darwin-arm64` artifact path; Linux and Windows
artifacts still require their native GitHub matrix jobs. Publishing to
crates.io, GitHub Releases, package repositories, and remote servers is not
performed locally.

## Release readiness and remaining boundaries

Use the exact `[package]` version as the tag, without a leading `v`, and commit
the workflow fixes before tagging. A tag points to a commit; rerunning an old
tag's workflow does not pick up uncommitted or later script changes.

Run the same local quality gates as the release workflow:

```bash
cargo fmt --all -- --check
python3 .github/scripts/release/test_preflight.py
cargo test --release --all-targets --locked
cargo package --list --allow-dirty --locked --offline
```

The release workflow also publishes to crates.io, updates the Homebrew tap and
Scoop bucket, pushes GHCR images, and installs the amd64 Debian package on the
web server. Check credentials and permissions for `CRATES_IO_TOKEN`,
`HOMEBREW_TAP_TOKEN`, `SCOOP_BUCKET_TOKEN`, and the `WEB_DEPLOY_*` secrets in the
repository settings. Local GitHub CLI authentication does not prove that those
Actions secrets are configured.

Installed standard libraries are currently discovered through `LITEX_STD_PATH`
or a project/current-directory `std/`. The CLI does not automatically find the
Debian `/usr/share/litex/std`, Homebrew `bin/std`, MSI application `std`, or Scoop
installation `std` directories. Installed-package smoke tests explicitly set
the path; users outside a project with `std/` need to set it too. Docker sets
`LITEX_STD_PATH=/usr/share/litex/std` in the image. For Debian installations:

```bash
export LITEX_STD_PATH=/usr/share/litex/std
```

The Linux arm64 archive is cross-built and has no execution smoke gate. Docker
currently pushes the multi-architecture image before its amd64 smoke test;
there is no arm64 execution smoke. Validate Linux binaries against the Debian
bookworm runtime and the actual web-server system before relying on compatibility.
These runtime checks cannot be replaced by a successful macOS preflight.

MSI is optional (`continue-on-error: true`) and is not downloaded or attached by
the GitHub Release job. Its WiX build and installation still need a Windows
runner. After `cargo wix init --force`, the workflow regenerates `wix/std.wxs`
with `.github/scripts/release/generate_wix_std.py` so `File/@Source` paths are
package-root relative (`std\...`). The script also inserts
`<ComponentGroupRef Id="LitexStd" />` into the generated `wix/main.wxs`
`Product/Feature[@Id="Binaries"]`. That explicit incoming reference links the
`LitexStd` component group and its entire std directory tree into the MSI.
Previously, a standalone `FeatureRef Id="Binaries"` fragment referenced the
product feature but the product never referenced that fragment; installation
could succeed with only the binary and license. Merely compiling `std.wxs` or
checking its source paths does not prove the std components are included.
The generator rejects missing or ambiguous product features and preserves WiX
preprocessor directives. Python tests exercise the CLI, resolve the product-to-group
and group-to-component references, check repeat runs, and reject unexpected
templates. The Windows install/import smoke remains the final runtime gate.
macOS artifacts cover ARM only; the generated Homebrew formula has no Intel macOS
artifact selection. Toolchain, runner, `cross`, and `cargo-wix` versions are
not all pinned, so a rerun may use newer build tools.

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
