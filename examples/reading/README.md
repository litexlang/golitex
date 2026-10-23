# Interactive reading examples

For real mathematics, open the [homepage collection](homepage/README.md):
least squares, sets, Newton iteration, irrationality of √2 and Cantor's theorem.

```sh
target/release/litex -reading -strict -lang zh -r examples/reading/homepage
```

For the proposed detail-pane design for every statement type, build the
[statement presentation gallery](statement-gallery/README.md): 52 statement
leaves, 61 checked examples, and curated mathematical layouts. This gallery
is a design preview; it does not claim all layouts are wired into Reading yet.

The real even-power and addition rules connect the declaration of a real
object to a nonnegative square and a shifted lower bound in
[`linked_facts.lit`](linked_facts.lit). Use it to compare source locations,
actual proof citations and rule applications in the reading exporter.

[`mathematical_meaning.lit`](mathematical_meaning.lit) exercises mathematical
explanations: a set parameter with a dependent element range, a two-condition
predicate, a complete equality-chain clause, a function equation and an abstract
predicate without an invented definition. In the reader, click a source
statement for its mathematical meaning and its type tag for syntax help.

The implementation and its current acceptance status are documented in
[`src/reading/README.md`](../../src/reading/README.md).
