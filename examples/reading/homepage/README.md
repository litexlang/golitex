# Mathematics from the Litex homepage

Five self-contained mathematical examples for the interactive reader. Their
proofs are copied unchanged from the sibling `litex-webpage` checkout's
`app/lib/litex/publicSources.ts`; trailing whitespace/newlines are normalized.
They use builtin mathematics and contain no user trust or axioms.
The checked-in `.lit` files are the runnable inputs; that sibling checkout is
provenance only and is not required to run the collection.

From the golitex root:

```sh
target/release/litex -reading -strict -lang zh -r examples/reading/homepage
target/release/litex -strict -lang en -r examples/reading/homepage
target/release/litex -reading -strict -lang zh -r examples/reading/homepage -export homepage-reading
```

Use the contents or source selector to switch examples. Select the first
file's `prop is_least_squares_center` to see its domains and complete quantified
defining condition typeset in LaTeX. Click `prop ⓘ` for the construct's purpose,
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

Every file is also independently verifiable without this project manifest.
The ordered exports are separate examples, with no ambient fact sharing or
cross-file proof dependencies. Strict verification checks the source; the
Reading exporter records its actual evidence. This sample does not add new
kernel mathematics or promise special display support for every construct.
Complex proof formulas currently retain canonical internal qualifiers and
generated binder names in some details; this collection does not change that
existing display behavior.
