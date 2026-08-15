# Local release preflight

Run the native release lane before pushing a version tag:

```bash
python3 tools/release/preflight.py
```

The command reads the package version and Rust host target, builds the release
binary inside a unique `private/release-preflight.*` directory, packages the
binary together with `std/`, extracts that archive, checks the binary version,
and runs the same archive smoke test used by the GitHub release workflow. The
temporary directory is removed on both success and ordinary failure.

To check an archive that has already been built:

```bash
python3 tools/release/preflight.py \
  --archive litex_0.9.116-beta_darwin_arm64.tar.gz \
  --version 0.9.116-beta
```

Focused tests:

```bash
python3 tools/release/test_preflight.py
```

This is a native-lane preflight, not an emulator for every GitHub runner. A
macOS ARM host verifies the `darwin-arm64` artifact path; Linux and Windows
artifacts still require their native GitHub matrix jobs. Publishing to
crates.io, GitHub Releases, package repositories, and remote servers is not
performed locally.
