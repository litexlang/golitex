# Mathematical progression and boundaries

The lessons reuse the interfaces of the homepage examples. They introduce no
native Obj/prop capability and no extra theorem, axiom or trust. Mathematical
source is preserved except for one concrete predicate instance, recorded in
the catalogue. Source comments teach different reading moves; shared reader
code supplies the same interactions for every lesson.

## From an equality to its premises

The sqrt(2) argument assumes rationality locally and obtains `p Z, q N+` with
`sqrt(2) = p / q` and `gcd(p, q) = 1`. Its chain transforms `p^2` into `2*q^2`.
Prime divisibility then forces both p and q even, contradicting coprimality.
Positive denominator, reduced fraction and local proof scope are essential.
Each adjacent equality has its own evidence; the proof of the complete chain
must not replace the proof of a particular equals sign.

## From a universal implication to an instance

The syllogism keeps `is_human` and `is_mortal` abstract: it claims no empirical
facts about a real person. Its conditional argument assumes a domain `people`,
a member `socrates`, the human premise and a universal mortality implication.
Instantiation at `person = socrates` uses both premises. Membership in `people`
alone does not establish `is_human(socrates)`. The missing-premise exercise
preserves that gap and must remain rejected; it does not prove immortality.

## From a definition to a verified instance

`prop nonnegative(x R): x >= 0` defines a real predicate. The insertion
`by def $nonnegative(3)` checks the body at a concrete argument and establishes
that instance, publishing its actual domain and inequality consequences.
`by def $nonnegative(-1)` fails the defining condition. In contrast,
`squares_are_nonnegative(-1)` concerns `(-1)^2`, not `-1`. Defining vocabulary,
checking a body and applying a theorem retain separate roles.

## From membership to local contradiction

The sets lesson uses builtin `union`, `intersect` and `$in` directly. `A set`
and `B set` bind arbitrary sets; they do not introduce membership in a universal
set. Union requires membership in at least one operand, intersection in both.
The temporary conclusion `1 $in {2, 3}` occurs under a contradiction assumption
and is not a global assertion that the concrete membership is true.

## From surjectivity to a witness

Cantor's theorem takes `S set` and `f fn(x S) power_set(S)`. Its diagonal subset
`{x S: not x $in f(x)}` belongs to `power_set(S)`. Under hypothetical
surjectivity, `obtain a` introduces a preimage of that subset. The contradiction
substitutes the same witness into the defining membership condition. No finite
or nonempty restriction on S is added.

## From an identity to an optimum

`is_least_squares_center(center, a, b, c R)` quantifies over every real candidate.
The function `mean(a, b, c)` returns `(a+b+c)/3`. The error decomposition adds
`3*(candidate-mean)^2` to the mean's error; nonnegativity gives the universal
minimum. The concrete scores 72, 84, 96 have mean 84; candidate 80 costs an
extra 48. A finite list of comparisons cannot replace the universal property.

## Defined expressions before true propositions

The square-root exercise deliberately uses `sqrt(-1)`. The real square-root
operator requires a nonnegative real input; its well-definedness obligation
fails before a value is available. Replacing the argument with 4 repairs that
domain condition. The lesson does not introduce a complex square-root branch
or claim that an undefined expression denotes a false mathematical value.
