# Interactive mathematics: short examples and longer lectures

Eight self-contained mathematical examples for the interactive reader. The first five
proofs are copied unchanged from the sibling `litex-webpage` checkout's
`app/lib/litex/publicSources.ts`; trailing whitespace/newlines are normalized.
They use builtin mathematics and contain no user trust or axioms.
The final three are complete existing golitex showcase lectures, with only
Chinese introductory reading comments added. They develop a chain of definitions,
lemmas, proofs and applications rather than unrelated syntax examples.
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
| [06-number-theory.lit](06-number-theory.lit) | 174 lines. Divisibility witnesses, Bezout certificates, the Diophantine criterion and `84*(-3)+30*9=18`, followed by congruence. | [Number theory showcase](../../../showcases/math_concepts_in_litex/3_number_theory/main.lit) |
| [07-sequence-limits.lit](07-sequence-limits.lit) | 130 lines. Epsilon tails, constant sequences, uniqueness of limits and a limit selector restricted to convergent sequences. | [Real analysis showcase](../../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit) |
| [08-groups-and-homomorphisms.lit](08-groups-and-homomorphisms.lit) | 402 lines. Integer addition motivates groups, cancellation and subgroups; homomorphisms lead to kernel normality and injectivity, with doubling and zero-map examples. | [Abstract algebra lecture](../../../showcases/abstract_algebra/abstract_algebra.lit) |

For a longer reading session, begin with number theory. Follow `divides_by`
from its definition to the Diophantine result using its reference badge; the
same name links several stages of one argument. The limit chapter emphasizes
nested quantifiers and local witnesses. The group chapter exercises structures,
named theorem applications, template sets and a substantially longer source.
The exact provenance, source hashes and current verification records for these
three chapters live in [long_examples.json](long_examples.json).

Every file is also independently verifiable without this project manifest.
The ordered exports are separate examples, with no ambient fact sharing or
cross-file proof dependencies. Strict verification checks the source; the
Reading exporter records its actual evidence. This sample does not add new
kernel mathematics or promise special display support for every construct.
Complex proof formulas currently retain canonical internal qualifiers and
generated binder names in some details; this collection does not change that
existing display behavior.
