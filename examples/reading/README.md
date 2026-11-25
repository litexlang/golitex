# Interactive reading examples

**Read the source: it is the textbook.** Definitions, mathematical statements
and proofs are expressed directly in Litex. The reader displays inferred facts
beside the statements that produce them; hovering or clicking the source gives
access to definitions, parameter domains and proof references in context.
There is no separate Info View that readers must open to follow the mathematics.
Explanations and proof grounds open beside the relevant source only when
requested; there is no standing explanation pane. Close the popup to continue
reading the unobstructed source.

For a guided first reading, use the [bilingual source lessons](lessons/README.md).
Six passing arguments focus on different mathematical reading moves, from
individual equalities and cited premises to definitions, witnesses and an
optimum. Three deliberately failing sources invite a concrete repair. Their
prompts live in the `.lit` source, alongside the mathematics.

For real mathematics, open the [homepage collection](homepage/README.md):
least squares, sets, Newton iteration, irrationality of √2 and Cantor's theorem.
It also includes seven longer branch chapters: number theory, sequence limits,
groups/homomorphisms, linear algebra, topology, finite probability and geometry
(IMO1966P6). Complete source files or complete opening chapters retain their
showcase proofs and add Chinese introductory reading notes.

```sh
target/release/litex -reading -strict -lang zh -r examples/reading/homepage
```
