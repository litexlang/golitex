# Collected IMO proofs

The common entry point for the existing IMO inequalities, geometry solutions,
functional-equation proof, and trust-free miniF2F IMO proof files. The collection
contains **26 distinct year/problem IDs and 30 solution artifacts**. The miniF2F
items retain their dataset statements, which can cover only part of an official
problem; these counts do not assert 26 complete contest solutions.

Proof source and geometry loading order are preserved. Current verification is
reported separately from historical completion: see [verification.md](verification.md).

| Collection | Problems | Solution artifacts | Index |
| --- | ---: | ---: | --- |
| Inequalities | 5 | 5 | [Statements and proofs](inequalities/README.md) |
| Geometry | 12 | 15 | [Official IDs, variants and coverage](geometry/README.md) |
| Functional equations | 1 | 1 | [1972 P5](functional_equations/imo_1972_p5.md) |
| miniF2F IMO variants | 8 | 9 | [Statements and current status](minif2f/README.md) |

## Inequalities

| IMO problem | Topic | Statement | Proof |
| --- | --- | --- | --- |
| 1983 P6 | Triangle-side polynomial inequality and equality cases | [Problem](inequalities/imo_1983_p6.md) | [Litex](inequalities/imo_1983_p6.lit) |
| 1995 P2 | Reciprocal cubic inequality | [Problem](inequalities/imo_1995_p2.md) | [Litex](inequalities/imo_1995_p2.lit) |
| 2001 P2 | Radical inequality | [Problem](inequalities/imo_2001_p2.md) | [Litex](inequalities/imo_2001_p2.lit) |
| 2005 P3 | Fifth-power rational inequality | [Problem](inequalities/imo_2005_p3.md) | [Litex](inequalities/imo_2005_p3.lit) |
| 2006 P3 | Sharp quartic constant, including optimality | [Problem](inequalities/imo_2006_p3.md) | [Litex](inequalities/imo_2006_p3.lit) |

## Geometry

Directory names use official IMO year/problem numbers. The old `problem_N`
labels were source-collection IDs; the [geometry index](geometry/README.md)
preserves that mapping and explains scalar and normalized variants.

| IMO problem | Topic | Proofs |
| --- | --- | --- |
| 1960 P3 | Subdivided hypotenuse and a tangent identity | [Solution 1](geometry/imo_1960_p3/Solution-1/solution.lit), [Solution 2](geometry/imo_1960_p3/Solution-2/solution.lit) |
| 1960 P6 | Cone and inscribed sphere; sharp volume ratio | [Parts (a), (b)](geometry/imo_1960_p6/Solution-1/solution_part_b.lit), [alternative part (a)](geometry/imo_1960_p6/Solution-2/solution_part_a.lit) |
| 1961 P4 | Interior points and cevian ratios | [Litex](geometry/imo_1961_p4/solution.lit) |
| 1961 P5 | Triangle construction with a median-angle condition | [Litex](geometry/imo_1961_p5/solution.lit) |
| 1962 P6 | Circumcenter, incenter and Euler's distance identity | [Scalar variant](geometry/imo_1962_p6/Solution-1/solution.lit), [geometric variant](geometry/imo_1962_p6/Solution-2/solution.lit) |
| 1963 P3 | Equiangular polygon and monotone side lengths | [Normalized proof](geometry/imo_1963_p3/solution.lit) |
| 1966 P6 | Quarter-area bound for corner triangles | [Litex](geometry/imo_1966_p6/solution.lit) |
| 1967 P1 | Four unit disks covering a parallelogram | [Litex](geometry/imo_1967_p1/solution.lit) |
| 1968 P1 | Consecutive integer sides and a doubled angle | [Litex](geometry/imo_1968_p1/solution.lit) |
| 1969 P4 | Semicircle and tangent circles | [Litex](geometry/imo_1969_p4/solution.lit) |
| 1970 P1 | Cevian and inradius/exradius ratios | [Litex](geometry/imo_1970_p1/solution.lit) |
| 1970 P6 | Triangle count among 100 points | [Litex](geometry/imo_1970_p6/solution.lit) |

## Functional equations

| IMO problem | Topic | Statement and proof idea | Proof |
| --- | --- | --- | --- |
| 1972 P5 | A bounded nonzero function satisfying a cosine-type equation | [Problem](functional_equations/imo_1972_p5.md) | [Litex](functional_equations/imo_1972_p5.lit) |

## miniF2F IMO variants

These nine existing proof files cover eight further problem IDs. Their precise
scope and compatibility results are in the [miniF2F index](minif2f/README.md).
Files consisting of assumed results (`trust`) are excluded from this collection.

| IMO problem | Formalized scope | Proof |
| --- | --- | --- |
| 1959 P1 | Coprimality of two linear expressions | [Litex](minif2f/imo_1959_p1.lit) |
| 1960 P2 | Necessary bounds for a radical inequality | [Litex](minif2f/imo_1960_p2.lit) |
| 1961 P1 | Necessary parameter bounds for the positive distinct solutions | [Litex](minif2f/imo_1961_p1.lit) |
| 1962 P2 | Necessary bounds for the stated radical inequality | [Litex](minif2f/imo_1962_p2.lit) |
| 1964 P1 | Divisibility consequences for powers of two | [Part 1](minif2f/imo_1964_p1_1.lit), [Part 2](minif2f/imo_1964_p1_2.lit) |
| 1964 P2 | Triangle-side cubic inequality | [Litex](minif2f/imo_1964_p2.lit) |
| 1966 P5 | Necessary solution values under a fixed ordering | [Litex](minif2f/imo_1966_p5.lit) |
| 1973 P3 | Coefficient lower bound when a reciprocal quartic has a real root | [Litex](minif2f/imo_1973_p3.lit) |

## Run a proof

From the repository root, after building the release binary:

```sh
target/release/litex -lang en -strict -f examples/imo/inequalities/imo_2006_p3.lit
target/release/litex -lang en -strict -f examples/imo/geometry/imo_1960_p3/Solution-1/solution.lit
```

For geometry, `-f` loads the package's configured prefix through the named file;
retain its adjacent `litex.config` and supporting sources. Each solution package
is independent. There is no combined `litex.config`: different solutions define
their own mathematical vocabulary and must not share one namespace.

[collection.json](collection.json) lists every runnable target, source hash and
current status. [source_records.jsonl](source_records.jsonl) records source,
statement scope, proof idea and proof files. The reusable plane-geometry library
remains in [showcases/2D_Geometry](../../showcases/2D_Geometry/README.md).
