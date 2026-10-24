# Mathematical sample chapters

How does a calculation become a reusable piece of mathematics? These seven
sample chapters follow that question through vector spaces, groups, topology,
limits, integer equations, finite probability, and plane geometry. Each starts
with a concrete problem, develops the concepts needed to solve it, and explains
an actual Litex proof or construction.

The chapters assume school algebra and basic set notation. The algebra and
topology chapters introduce their structural vocabulary as it becomes useful;
the analysis chapter explains the order of its epsilon quantifiers. They can
be read independently. Read the source excerpts as mathematical steps: a
declaration introduces an object or a definition, while a subsequent assertion
must follow from the available facts.

| Chapter | Guiding question | Main result |
| --- | --- | --- |
| [1. Vectors and unique coordinates](01-linear-algebra.md) | When do directions give an unambiguous description of every vector? | The standard directions form a basis of the real plane and give unique coordinates. |
| [2. Homomorphisms and lost information](02-abstract-algebra.md) | How can one subset tell us whether a structure-preserving map is injective? | A group homomorphism is injective exactly when its kernel is trivial. |
| [3. The topology of the same function](03-topology.md) | Can the identity function be continuous in only one direction? | A continuous bijection between two-point spaces need not be a homeomorphism; continuous maps compose. |
| [4. Why a sequence has at most one limit](04-analysis.md) | How do two independently chosen tails meet? | Sequence limits are unique; convergent sequences admit a uniquely specified limit value. |
| [5. Integer equations and Bezout witnesses](05-number-theory.md) | What decides whether an integer target can be represented? | Given a positive gcd certificate with Bezout data, `ax + by = c` is soluble exactly when the certified gcd divides `c`. |
| [6. Expectation and conditional probability](06-probability.md) | What changes when outcomes are weighted or new evidence is observed? | Two-point expectation is affine; coherent joint and evidence probabilities give Bayes' formula. |
| [7. Constructing an equilateral triangle](07-geometry.md) | How can a formula prove a geometric construction exists? | An explicit equilateral construction, followed by the sharp quarter-area bound from IMO 1966 Problem 6. |

For a first reading, start with Chapters 1 and 5. Chapter 2 shows how concrete
arithmetic motivates general structural laws. Chapter 3 separates a function
from the structures on its source and target. Chapter 4 adds quantified
approximation, and Chapters 6 and 7 show numerical and geometric applications.
The [Chinese reading guide](README.zh-CN.md) gives the same route in Chinese.

Each chapter contains a short standalone Litex example and clearly labelled
excerpts whose definitions live in the linked complete source. The prose
supplies the mathematical argument between those excerpts. Exercises and their
answers are mathematical extensions; unless explicitly included in a runnable
block, they are not presented as additional formalized theorems.

The selected sources are public examples and original lectures. The linear
algebra lecture draws inspiration from Sheldon Axler's *Linear Algebra Done
Right*; the geometry construction treats the mathematical content of Euclid
I.1 in an analytic plane. These chapters are not reproductions or complete
formalizations of either book. The plane-geometry library used for further
reading is maintained by Jiachen Shen and Keyao Zhu.

[Verification and source map](verification.md) records the exact checked
scope, source fingerprints, and the meaning of strict verification. The seven
chapters use Litex's verifier and builtin mathematics. Their acceptance does
not claim Lean replay or an independent audit of Litex's implementation.

For more extensive material, see the [showcase catalogue](../../showcases/README.md)
and the [proof-writing tutorial](../../showcases/The-Mechanics-of-Litex-Proof/README.md).

