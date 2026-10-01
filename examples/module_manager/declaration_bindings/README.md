# Local function and preimage binding identities

Run `target/release/litex -strict -f examples/module_manager/declaration_bindings/main.lit`.
Use `target/release/litex -strict -r examples/module_manager/declaration_bindings`
to exercise both root exports and the imported package together.
The root and imported files both use local functions and preimage witnesses,
then reuse their names at file root. The consumer releases the two exported
functions explicitly and checks their different values despite identical names.

The imported library's supported function definition is stored with its
declaration ID in KB ABI 2. A subsequent run can load that definition from
cache and remap its function and parameter IDs together. ABI 1 cache products
are rebuilt; a legacy standalone function record without an ID is rejected.
Cache JSON preserves UTF-8 paths, including this repository's Chinese path.

`cargo test --release declaration_binding_tests -- --nocapture` covers scope
reuse, local escape, duplicate visible names, false equations and rollback.
The import regression also requires a second run to use the cache, with only
the two root exports appearing in its executed file results.
The case/induction/unique-existence variants of `have fn` retain their existing
payloads and are outside this two-field repair.
