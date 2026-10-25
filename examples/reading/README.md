# Interactive reading examples

**Read the source: it is the textbook.** Definitions, mathematical statements
and proofs are expressed directly in Litex. The reader displays inferred facts
beside the statements that produce them; hovering or clicking the source gives
access to definitions, parameter domains and proof references in context.
There is no separate Info View that readers must open to follow the mathematics.
The explanation panel provides optional elaboration on what they are already
reading in the source.

For real mathematics, open the [homepage collection](homepage/README.md):
least squares, sets, Newton iteration, irrationality of √2 and Cantor's theorem.
It also includes seven longer branch chapters: number theory, sequence limits,
groups/homomorphisms, linear algebra, topology, finite probability and geometry
(IMO1966P6). Complete source files or complete opening chapters retain their
showcase proofs and add Chinese introductory reading notes.

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

## Edit the examples locally

With a checking host, all examples open directly in an editable IDE, retaining
checked semantic hover and quiet inline inference. Use **Check** or Cmd/Ctrl+Enter; **Restore original** restores the page's initial
source without modifying the actual textbook. For an existing exported gallery:

```sh
target/release/litex -reading -strict -no-browser -port 49186
python3 examples/reading/serve_gallery.py /path/to/gallery --port 49187
```

The second command serves static examples and forwards checking to the native
local service. Independent files and closed single-configuration books such as
Mechanics are supported. Checks use the selected registered file and its real
ordered prefix; later chapters remain editable but show **Chapter not checked**.
Nested/external imports require a host that supplies the complete project rather
than this first shell reconstruction. Static exports without a checking host
remain readable.

Browser acceptance (2026-10-24): changing `sqrt(4) = 2` to `1 + 1 = 3` clears the
old verdict immediately, then produces a rejected red source line. This checked
replacement shows new citations to the declaration:

```litex
have x R = 2
x + 1 = 3
```

Restore, undefined-name diagnostics, keyboard checking, Tab/newline indentation,
editing during an in-flight check, chapter-prefix checking and source-only later
chapters were exercised in the real browser. Reading/export/HTTP compatibility
checks pass with `cargo test --release --test reading --test reading_http
--test reading_site` (29 tests). The live editor uses the shared reader; draft
colors carry no proof or resolved-symbol authority. See
[the editing contract](../../docs/reading.md#editing-and-checking).

Unified IDE acceptance (2026-10-24): the existing `43-checking-03-2.lit`
example opens with its editable source and four real inline consequences of
`by def $is_unit_pair(1, 1)`. Moving over parameter `x` shows its declaration
on line 1 and declared domain `R`; clicking an inferred result still selects
its actual fact and proof grounds. Changing the instance to `(1, 2)` removes
old inference/help immediately and checking selects the rejected fifth line.
Restoring and checking brings back fresh results without leaving the IDE.
The six authored source lines remain six display rows. Both static-site
integration tests pass; release-embedded viewer assets match maintained source.
This changes the view, not the proof records or verifier.
