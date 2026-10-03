# Cart alias diagnosis correction

Task: answer the user's proposed Obj builtin-rule and special-property designs.
Scope: current-source diagnostic probes and correction of the earlier audit;
no Rust, AST, state or mathematical contract change.

The earlier reduced reproduction used an unsuitable alias name:

```litex
let C = cart(R, Z)
cart_dim(C) = 2
```

Expression parsing resolves `C` to the builtin complex set before looking up a
bound identifier (`src/parse/object/primary.rs`). The assertion therefore asks
for the dimension of the builtin complex set. Its failure does not demonstrate
a missing cart-alias property consumer.

The unchanged intended alias behavior works with an ordinary name:

```litex
let product_space = cart(R, Z)
$is_cart(product_space)
cart_dim(product_space) = 2
```

The corresponding typed `have product_space set = cart(R,Z)` also works.
`cart_dim(R)=2` remains a rejection, and `C=cart(R,Z)` after the original
`let C` declaration also rejects. The successful build and all five exact
sources, process exits and JSON outputs are retained in
[the correction journal](../../proof_journals/cart_name_correction_2026-10-03.json).

Existing owners already provide the mechanism:

- `execute_let_stmt.rs` calls `store_fact_and_infer` for the defining equality.
- `exec_env/special_property.rs` indexes that fact as
  `SpecialProperty::Equality(EqualFact)` on both sides.
- `store_fact_and_infer/.../infer_equal_fact/cart_tuple_shape.rs` derives
  `$is_cart(product_space)` and `cart_dim(product_space)=2` from the equality.

No new `SpecialProperty::Cart` or Env/Runtime shape is needed for this example.
The preceding authoring follow-up had independently found the same naming
mistake and promoted `cart_dim-P04` with an ordinary name; its sources and
earlier verified binary remain in its own journal. This task preserves that
work and adds a current-source confirmation.

Release source SHA-256:
`42a8902208e27bf6d9edbb8996b729dc406db5b5a75610b592600e8bd3802ab9`.
Executable SHA-256:
`8a432ba8702ef567beea8a935fb31a679fd762499e658e0a8cfa38dbde89b204`.
Source and binary remained stable during the build/probes. This narrow gate
does not rerun or certify the whole corpus.

Commands: `cargo build --release`, followed by release `-e` probes in the
journal. Reusable lesson: verify resolved object identity and an ordinary-name
control before diagnosing missing state or equality transport. Reserved-name
declaration rejection/shadowing is a separate public syntax question; this
diagnosis does not change it.
