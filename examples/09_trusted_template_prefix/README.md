# Trusted Template Prefix

This configured example checks the boundary between a trusted earlier export
and a verified target file. `prefix.lit` declares a generic template, while
`main.lit` instantiates it after the prefix has been replayed.

`main.lit` is the executable target of this configured example.

The trusted load must retain the template's checked generic result rather than
rejecting the declaration or storing syntax without verification evidence.
