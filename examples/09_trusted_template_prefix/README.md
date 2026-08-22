# Trusted Template Prefix

This configured example checks the boundary between a trusted earlier export
and a verified target file. `prefix.lit` declares a generic template, while
`main.lit` instantiates it after the prefix has been replayed.

Run the focused tracer with:

```console
target/release/litex -compact -runner -f examples/09_trusted_template_prefix/main.lit
```

The trusted load must retain the template's checked generic result rather than
rejecting the declaration or storing syntax without verification evidence.
