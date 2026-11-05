# Minimal compiler CLI fixtures

Only the CLI's small file-based inputs live here:

- `identity.lit` and its actual generated `identity.lean` test complete stdout.
- `failed_fact.lit` and `unsupported_constructor.lit` test failure diagnostics.

Core compiler regressions contain their own small source strings. Module
loader regressions construct temporary projects from the self-contained
`tests/unit/compile_to_lean/module_fixtures.rs` inputs. Each test retains the
project guard through compilation and cleans up its directory at scope exit.
They do not require the optional mathematical corpus.

`module_fixtures::project_survives_module_compilation_and_cleans_up_afterward`
checks both declaration visibility during real compilation and cleanup after
the guard leaves scope. The seven affected module test groups passed all 82
tests on 2026-11-05, with no failures or ignored tests.

Bulk example acceptance tests live with the ignored corpus under
`lean/examples/_acceptance/`. Run them separately when that corpus is present;
they are not a dependency of ordinary Cargo tests or the published package.

Refresh the identity baseline only through the actual compiler:

```sh
target/release/litex -strict -lean -f tests/fixtures/compile_to_lean/identity.lit > tests/fixtures/compile_to_lean/identity.lean
```
