# Repository Module Example

Run this directory in repository mode:

```bash
cargo run -- -r examples/08_module_repository
```

The root `litex.config` exports module `A`. `A/litex.config` exports `chap2.lit`
and `chap3.lit`, and `chap3.lit` binds `chap2` with `local import chap2`.

`litex.config` declares the project interface and entrance. Mathematical statements
live in each module's entrance `.lit` file and exported `.lit` files.
