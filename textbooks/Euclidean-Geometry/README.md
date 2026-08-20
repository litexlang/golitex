# Euclidean Geometry Foundation

This formal publication contains the runnable analytic coordinate foundation
for planar Euclidean geometry over `R`.

It exports `book_zero.lit` as namespace `zero` and `analytic_laws.lit` as
namespace `laws`. Together they define the plane, coordinate operations,
squared distance, lines, circles, and basic geometric predicates, then prove
the coordinate formula and nonnegativity of squared distance.

There is currently no construction chapter or numbered proposition sequence in
this publication.

Verified with:

```text
target/release/litex -compact -runner -r textbooks/Euclidean-Geometry
```
