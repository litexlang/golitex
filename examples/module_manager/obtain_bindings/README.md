# Obtain bindings across proof scopes and modules

Run `target/release/litex -strict -f examples/module_manager/obtain_bindings/main.lit`.
This executes local proof witnesses in both root and imported exports, then
checks actual published witnesses from another file/module. Run
`target/release/litex -strict -f examples/module_manager/obtain_bindings/library/witnesses.lit`
to cover the same library as a root module.

The consumer explicitly releases the exported theorems before using their
equalities. Direct automatic lookup of stored equalities across finished files
fails for both ordinary let and obtain in the before/after diagnostic controls;
this fixture does not claim to widen that separate search boundary.

`local.lit` preserves the former failure as comments and as an active proof.
It also checks `obtain k from exist k Z st {k > 0}`: the quantified k has
already left scope before the witness k is declared. The two IDs differ.

`cargo test --release obtain_binding_tests -- --nocapture` covers the negative
boundaries: duplicate visible bindings, escaping local witnesses, wrong
equations, failure rollback, and the formerly accepted false `0 = 1`.
