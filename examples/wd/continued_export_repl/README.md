# Continued export REPL lookup

Run `target/release/litex -strict -lang en -f examples/wd/continued_export_repl/prefix.lit -session` and enter:

```litex
thm session_member_has_property:
    ? forall X set, S \Subsets<X>:
        $lies_in(X, S)
```

The registered prefix stays open. Its predicate remains visible through its original publication owner while new diagnostics use `<repl>`. This session step previously terminated with `inferred fact ... failed well-definedness check`. The ordinary file gate checks the prefix; the dedicated Rust session regression and the recorded release CLI dialogue check the transition into the REPL. Distinct root and imported export owners remain distinct.
