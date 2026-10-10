# Installed std discovery

`std/basics/main.lit` exports `let version = 1`; the consumer verifies both
qualified spellings. This is an acceptance fixture, not the shipped std module.
The checked-in project uses a relative import so ordinary example collectors
can execute it from the repository root:

```bash
target/release/litex -lang en -strict -f examples/module_manager/installed_std/project/main.lit
```

The actual installation test replaces that relative manifest with
`[import std] basics`, copies the release executable into each package layout,
and launches it from an external project without `LITEX_STD_PATH` or local std:

```bash
cargo test --release --test installed_std_cli --locked
```

Before automatic discovery, that external run failed to import the project.
Now it consumes the declaration bundled with the executable. The tests cover
archives/Scoop, current and legacy Homebrew, MSI and Debian layouts, file/eval/
repository commands, and a Unix symlink into a versioned installation.
They reject a wrong value, a missing import, and an invalid explicit override;
explicit overrides and local std still take precedence over bundled std.
These native layout checks do not replace actual package-manager installation.
