# Mathematical scope of the collected IMO proofs

This is a collection of independent existing developments. It introduces no
shared mathematical interface, kernel rule or assumption. Different packages
can reuse local names, so there is no single namespace or combined export file.

## Inequalities

The five complete developments retain their hypotheses, equality cases and
optimality claims. See [their design notes](inequalities/math_collections.md)
for square certificates, weighted radical bounds and the sharp quartic constant.
Positive denominators, root domains and triangle inequalities remain part of
the statements and proofs; collection does not relax them.

## Geometry

Points use `cart(R,R)` and coordinate projections. Local predicates describe
incidence, noncollinearity, side parameters, circles and angles. Each package
includes the definitions it consumes. The independent reusable geometry
library and its [interface notes](../../showcases/2D_Geometry/math_collections.md)
remain outside this collection.

The [geometry index](geometry/README.md) distinguishes full configurations,
scalar alternatives and normalized closure assumptions. A scalar theorem does
not imply an unprovided point construction. Squared area and length formulas
retain their exact interpretations rather than acquiring new geometric meaning
through the directory name.

## Functional equation

The 1972 P5 interface quantifies over real unary functions `f,g` and arbitrary
real `y`. Nonvanishing is an existential nonzero value of `f`; boundedness is
pointwise on all reals. Its proof uses the nonempty range of `abs(f)`, positive
real least upper bound `M`, and the contradiction `M <= M/abs(g(y)) < M`.
The current absolute-value product step fails verification; the collected
source is preserved without adding a trusted lemma.

## miniF2F statement boundaries

These files formalize their dataset statements. Necessary interval bounds are
not solution-set equivalences; an ordered linear system case is not all
permutations; a quartic coefficient bound is not a proof of attainment.
The [miniF2F index](minif2f/README.md) records these boundaries per item.

The 1964 P1 files define natural divisibility existentially and attempt a
unique integer quotient construction before modular induction. Current failure
of that construction remains visible in the verification record. No wrapper,
axiom or placeholder was introduced to make it pass.

## Verification and provenance

Source hashes and commands are in [collection.json](collection.json).
[verification.md](verification.md) distinguishes current strict passes,
current failures, and geometry packages retained with historical evidence but
not rerun in this organization task. A successful check concerns a supplied
proof of its actual statement, not automatic problem solving.
