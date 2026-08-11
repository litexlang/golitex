# Repository Module Example

This configured project demonstrates ordered exports, submodules, and
cross-file qualified names. Run the top-level module with the release runner:

```text
target/release/litex -compact -runner -r examples/08_module_repository
```

The root `litex.config` exports submodule `A` before `main.lit`.
`A/litex.config` exports `chap2.lit`, `chap3.lit`, and `main.lit` in order, so
`chap3.lit` can cite `A::chap2::x` directly.

The root also opts `A` into `[allow bare export]`. Once all of `A` has loaded,
its recursively public terminal symbols receive a one-time bare-name index for
later files. Thus `main.lit` checks both `A::chap3::z = 1` and `z = 1` against
the same canonical symbol. The opt-in does not expose private imports, does not
apply before `A` is loaded, and does not change explicit `A::...` resolution.

Running `-r examples/08_module_repository/A` traces back to the root module,
runs everything before `A`, and then runs all of `A`. Running an exported file
with `-f` follows the same recursive prefix order through that file.

The public result is `answer`, a checked real object equal to `1`. The example
contains no `trust`, axiom, or abstract proposition boundary.

For a focused prefix check through the final file, run:

```text
target/release/litex -compact -runner -f examples/08_module_repository/main.lit
```
