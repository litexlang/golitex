# Same-name definitions and package-local import aliases

`left` and `right` each import `Common = "./dep"` from their own manifest.
Their dependency files and exported wrapper functions share the spelling
`ident`, but return 2 and 3 at input 2. Their same-name `ready` theorems preserve
these separate owners. Before the loader fix, this exact graph failed to mount
because the second Common alias was incorrectly treated as a global collision.

```sh
target/release/litex -strict -f examples/module_manager/cross_file_identity/target.lit
cargo test --release cross_file_identity_tests -- --test-threads=1
```

The CLI gate requires exit 0, JSON success true and no session_error. Rust
regressions also reject the wrong value after successful imports, verify real
cache hits and reordered module IDs, preserve same-path merging, reject alias
duplicates within one manifest, and check that unsupported qualified algo eval
cannot run a local same-name algorithm. Global display labels may receive a
suffix; source references retain the manifest's original aliases and paths.

The function-call wrappers in this CLI fixture use existing source fallback:
the cache codec does not serialize FnObj bodies. Cache regressions use qualified
object definitions supported by the codec. Reordered imports may rebuild some
existing caches; their values and owners must still be correct.
