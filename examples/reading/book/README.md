# Three-chapter reading tracer

This small strict project uses existing Litex named-interface semantics:
definitions and a theorem in the first file, qualified uses in the second,
and a local hypothesis/conclusion proof in the third. Ambient facts are not
implicitly merged across files.

```sh
target/release/litex -reading -strict -lang zh -r examples/reading/book
target/release/litex -reading -strict -r examples/reading/book -export book-site
```

Use the contents to switch chapters, follow a named definition back to chapter
one, or search for `Chapter 3` and select the local proof. In the local proof,
`t = 2` is a hypothesis and `t + 1 = 3` is a checked conclusion. Static export
keeps portable `reading.json` alongside the manifest and source/proof parts.
