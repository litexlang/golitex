# Repository Module Example

Run this directory in repository mode:

```bash
cargo run -- -r examples/08_module_repository
```

The root `litex.config` exports module `A`. `A/litex.config` lists `chap2.lit`
before `chap3.lit`, so `chap3.lit` can cite `A::chap2::x` directly.

`litex.config` is the ordered `[export]` table. Mathematical statements live
in its registered `.lit` files.
