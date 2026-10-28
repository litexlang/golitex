# Read the argument in its source

These short lessons teach complementary ways to read a mathematical proof in
Litex. The source contains the definitions, argument and reading prompts. Hover
the point you want to understand: an object for its domain and introduction,
an equals sign for that adjacent proof, or a fact for its actual premises.
Grey inline text exposes the consequences of a statement. There is no separate
Info View to keep in sync with the argument.

Start with the irrationality of sqrt(2). Its first equality uses the obtained
reduced fraction; later equalities perform different mathematical steps. Follow
one premise and return to the same equals sign. Then read the syllogism: its
conclusion uses a universal implication and the particular human premise. This
distinguishes a statement's mathematical dependencies from occurrences of an
object name in the text.

The definition lesson makes a further distinction explicit:

```litex
prop nonnegative(x R):
    x >= 0

by def $nonnegative(3)
```

The declaration defines a property of real arguments. The last line establishes
one instance by checking its defining condition. Replacing `3` with `-1` leaves
the definition intact but makes that instance fail. Applying the square theorem
to `-1` concerns its square, which is nonnegative. Both comparisons were checked;
the failing lessons are deliberate exercises, not verified assertions.

| Mathematical question | Chinese source | English source | Expected result |
| --- | --- | --- | --- |
| Why is sqrt(2) irrational? | [Irrationality](zh/sqrt-two.lit) | [Irrationality](en/sqrt-two.lit) | Pass |
| Which two premises establish the conclusion? | [Syllogism](zh/syllogism.lit) | [Syllogism](en/syllogism.lit) | Pass |
| What does proving a defined predicate require? | [Definitions](zh/definitions.lit) | [Definitions](en/definitions.lit) | Pass |
| What does membership in a union or intersection mean? | [Sets](zh/sets.lit) | [Sets](en/sets.lit) | Pass |
| Where does a witness come from? | [Cantor](zh/cantor.lit) | [Cantor](en/cantor.lit) | Pass |
| Why does the mean minimize squared error? | [Least squares](zh/least-squares.lit) | [Least squares](en/least-squares.lit) | Pass |
| What happens when the human premise is missing? | [Missing premise](zh/missing-premise.lit) | [Missing premise](en/missing-premise.lit) | Fail |
| Is this real square-root expression defined? | [Square-root domain](zh/sqrt-domain.lit) | [Square-root domain](en/sqrt-domain.lit) | Fail |
| Does a definition make every instance true? | [Unmet condition](zh/definition-failure.lit) | [Unmet condition](en/definition-failure.lit) | Fail |

Each file is independent: the language directories have no `litex.config` and
do not silently load another lesson. The [catalogue](catalogue.json) identifies
the original homepage source by SHA-256 and anchors authored annotations to its
original line numbers. The builder preserves every non-comment mathematical
line and its indentation, with only the explicit concrete-instance insertion
listed in the catalogue. Original homepage files and their provenance remain
unchanged. See the [homepage collection](../homepage/README.md) for that source
collection and the [mathematical design](math_collections.md) for the reused
interfaces and scope boundaries.

`build.py --check` checks the generated source and original-source hashes.
`build.py --check --verify` checks all 18 files with the strict release CLI and
writes [verification.json](verification.json), recording exact source hashes,
expected outcomes and executable identity. Re-run it after changing source or
the verifier; the receipt establishes only the recorded version. The shared
[gallery exporter](../homepage/export_gallery.py) adds these lessons to the
existing example menu. Editing and checking in a browser require its checking
host; static reading alone does not execute changed mathematics.
