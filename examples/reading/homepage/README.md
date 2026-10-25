# Interactive mathematics: short examples and longer lectures

Fifty-seven strictly checked source chapters for the interactive reader: fifty
distinct homepage/shared public examples and the seven longer branch chapters.
The homepage sources are copied from the sibling `litex-webpage` checkout;
only line endings and the final newline are normalized. The mathematical code
is unchanged. The original five short examples remain in place. This is a
checked snapshot, independent of later edits to the sibling homepage.
They use builtin mathematics and contain no user trust or axioms.
The original three longer lectures are complete existing golitex showcases, with
Chinese introductory reading comments added. The number-theory example also
uses single-line `by def` for its eight definition folds without proof bodies.
They develop a chain of definitions,
lemmas, proofs and applications rather than unrelated syntax examples.
Four further branch chapters add linear algebra through unique standard coordinates,
topology through the two-point swap homeomorphism, finite probability through
Bayes calculations, and a complete IMO1966P6 geometry proof. The first two
are complete source prefixes; the latter two retain the complete source files.
The checked-in `.lit` files are the runnable inputs; that sibling checkout is
provenance only and is not required to run the collection.

The imported homepage material now includes the full orthogonal projection proof
(orthogonal residual, distance decomposition, minimum and uniqueness), the
ellipse point set and focal separation, the age word problem, group left
cancellation, two Newton developments, piecewise functions, reciprocal domains,
and Cauchy–Schwarz. Short language examples cover definitions, quantifiers,
theorem use, cases, induction, contradiction, templates and unique existence.
See [the complete example directory](homepage_examples.md) and the exact
[source/hash/verification catalogue](homepage_sources.json).

The homepage's two explicit `trust` demonstrations live separately in
[assumptions/](assumptions/README.md). Its four deliberately ill-defined calls
live in [boundaries/](boundaries/README.md), with expected rejection recorded.
They are excluded from the strict main collection. The actual two-file
Newton reuse example is preserved with its original configuration in
[reuse/](reuse/README.md). Recorded terminal/JSON output, Lean/Python output and
incomplete illustrative syntax are not imported as executable Litex proofs.

From the golitex root:

```sh
target/release/litex -reading -strict -lang zh -r examples/reading/homepage
target/release/litex -strict -lang en -r examples/reading/homepage
target/release/litex -reading -strict -lang zh -r examples/reading/homepage -export homepage-reading
```

The collection opens with the irrationality of √2. Use the top-right example
menu to switch examples. In `01-mean-squared-error.lit`,
select `prop is_least_squares_center` to see its domains and complete quantified
defining condition typeset in LaTeX. Click the source keyword `prop` for the construct's purpose,
semantics and a short checked example. Select `mean(72, 84, 96) = 84` and the
following predicate instance to follow a real application and its inferred
conditions. Facts in local proofs retain their own scopes.

| File | Mathematics and proof idea | Original source constant |
| --- | --- | --- |
| [01-mean-squared-error.lit](01-mean-squared-error.lit) | The mean minimizes squared error. Split the candidate's error into the mean's error and a nonnegative square; compare 84 with 80 for scores 72, 84, 96. | `homepageAveragePlaygroundSource` |
| [02-union-and-intersection.lit](02-union-and-intersection.lit) | Union commutes; inspect concrete union/intersection membership and prove a nonmembership by contradiction. | `homepageFiniteSetsSource` |
| [03-newton-error.lit](03-newton-error.lit) | A positive Newton iterate for √2 has error `(x - sqrt(2))^2 / (2 * x)`, by expanding the square and using `sqrt(2)^2 = 2`. | `homepageNewtonErrorSource` |
| [04-sqrt-two-irrational.lit](04-sqrt-two-irrational.lit) | A reduced rational representation of √2 would make both numerator and denominator even, contradicting their gcd. | `homepageSqrtTwoIrrationalSource` |
| [05-cantor-diagonal.lit](05-cantor-diagonal.lit) | The diagonal subset `{x S: not x $in f(x)}` contradicts surjectivity onto the power set. | `homepageCantorPlaygroundSource` |
| [06-number-theory.lit](06-number-theory.lit) | 166 lines. Divisibility witnesses, Bezout certificates, the Diophantine criterion and `84*(-3)+30*9=18`, followed by congruence. | [Number theory showcase](../../../showcases/math_concepts_in_litex/3_number_theory/main.lit) |
| [07-sequence-limits.lit](07-sequence-limits.lit) | 130 lines. Epsilon tails, constant sequences, uniqueness of limits and a limit selector restricted to convergent sequences. | [Real analysis showcase](../../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit) |
| [08-groups-and-homomorphisms.lit](08-groups-and-homomorphisms.lit) | 402 lines. Integer addition motivates groups, cancellation and subgroups; homomorphisms lead to kernel normality and injectivity, with doubling and zero-map examples. | [Abstract algebra lecture](../../../showcases/abstract_algebra/abstract_algebra.lit) |
| [09-linear-algebra.lit](09-linear-algebra.lit) | 741 lines. Coordinate operations → vector spaces and subspaces → linear combinations → span and independence → basis and unique standard coordinates. | [Linear algebra lecture, through §2.4](../../../showcases/linear_algebra/linear_algebra.lit) |
| [10-topology.lit](10-topology.lit) | 489 lines. Discrete and indiscrete two-point spaces → preimages and continuity → a continuous bijection with discontinuous inverse → swap homeomorphism. | [Topology lecture, Chapters1–2](../../../showcases/topology/topology.lit) |
| [11-finite-probability.lit](11-finite-probability.lit) | 154 lines. Probability vectors → expectation and variance → least squares → conditional probability and a Bayes calculation. | [Finite probability showcase](../../../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit) |
| [12-geometry-imo1966.lit](12-geometry-imo1966.lit) | 338 lines. Coordinate/segment definitions → determinant ratios → the IMO1966P6 quarter-area bound. | [Complete geometry solution](../../imo/geometry/imo_1966_p6/solution.lit) |

For a longer reading session, begin with number theory. Follow `divides_by`
from its definition to the Diophantine result using its reference badge; the
same name links several stages of one argument. The limit chapter emphasizes
nested quantifiers and local witnesses. The group chapter exercises structures,
named theorem applications, template sets and a substantially longer source.
The exact provenance, source hashes and current verification records for these
seven branch chapters live in [long_examples.json](long_examples.json).

Every file is also independently verifiable without this project manifest.
The ordered exports are separate examples, with no ambient fact sharing or
cross-file proof dependencies. Strict verification checks the source; the
Reading exporter records its actual evidence. This sample does not add new
kernel mathematics or promise special display support for every construct.
The reader shortens recorded export qualifications when the symbol identity
is unambiguous in context. Unknown or ambiguous external names retain their
qualification; generated binder names may still appear in complex proof facts.

Advanced constructs retain their actual source and checking records; not every
language construct has a dedicated mathematical typesetting view yet.

The reader presents each independent file under an authored Chinese or English
example title, selected by the language control. The labels are maintained in
[reading-titles.json](reading-titles.json); numbered filenames are source
identities, not the names shown to readers. The same metadata is supplied for
the separate assumption, boundary and reuse examples.

## Passing and failing examples

Four new independent [problem/correction pairs](problems/README.md) cover
undefined names, zero divisors, the real square-root domain and a missing
Socrates premise. The gallery menu groups normal chapters and these separate exports into
Passes / Does not pass, keeping
the strict main collection intact. Build the gallery with
`python3 examples/reading/homepage/export_gallery.py <output-directory>`.
Use `--reuse-main` only with an existing verified main export.

## Complete-book reading

The gallery can link a separately exported **The Mechanics of Litex Proof**
module. Export the canonical book first, then supply its output directory:

```sh
target/release/litex -reading -lang zh -r /path/to/book -export /path/to/book-reading
python3 examples/reading/homepage/export_gallery.py /path/to/gallery --reuse-main --mechanics-export /path/to/book-reading
```

The book appears once under **Complete books**. Inside, its ordered chapters
share their original proof context and identities, with bilingual chapter labels
from the book's `reading-titles.json`. A link returns to the other examples.
The gallery accepts only a successful export; if its retained trust summary
contains assumptions or axioms, the book entry says so. Successful ordinary
execution is not strict proof completion. Use `-strict` for a book that must
exclude these assumptions.

This command consumes a local export; it does not publish the canonical book or
copy a local-only workspace into this repository. Hosted distribution requires
separately authorized book content and its generated reading assets.
