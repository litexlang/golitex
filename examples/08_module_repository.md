# Repository Module Example

Run the top-level module:

```bash
cargo run -- -r examples/08_module_repository
```

The root `litex.config` exports submodule `A` before `main.lit`.
`A/litex.config` exports `chap2.lit`, `chap3.lit`, and `main.lit` in order, so
`chap3.lit` can cite `A::chap2::x` directly.

Running `-r examples/08_module_repository/A` traces back to the root module,
runs everything before `A`, and then runs all of `A`. Running an exported file
with `-f` follows the same recursive prefix order through that file.
