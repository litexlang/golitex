# IMO geometry solutions

Twelve IMO problems and fifteen independent solution packages, collected from
the former `showcases/2D_Geometry/IMO` tree without changing any `.lit` source or
configuration. Jiachen Shen and Keyao Zhu maintain the coordinate geometry
library; the contest developments come from Jiachen Shen's geometry collection.

| Official IMO problem | Former collection ID | Package and coverage |
| --- | ---: | --- |
| 1960 P3 | 1 | [Solution 1](imo_1960_p3/Solution-1/solution.lit), [Solution 2](imo_1960_p3/Solution-2/solution.lit): tangent identity from a right triangle, altitude and odd subdivision count. |
| 1960 P6 | 2 | [Solution 1](imo_1960_p6/Solution-1/solution_part_b.lit): both parts and an attaining configuration; [Solution 2](imo_1960_p6/Solution-2/solution_part_a.lit): alternative part (a). Solid geometry is reduced to the axial section and scalar relations. |
| 1961 P4 | 3 | [Solution](imo_1961_p4/solution.lit): both cevian ratio bounds, with incidence and noncollinearity. |
| 1961 P5 | 4 | [Solution](imo_1961_p5/solution.lit): necessity, construction and equality cases. |
| 1962 P6 | 5 | [Scalar alternative](imo_1962_p6/Solution-1/solution.lit); [geometric configuration](imo_1962_p6/Solution-2/solution.lit), deriving circle data and squared/principal-root identities. |
| 1963 P3 | 7 | [Solution](imo_1963_p3/solution.lit): normalized side-chain argument with trigonometric closure equations as hypotheses. |
| 1966 P6 | 12 | [Solution](imo_1966_p6/solution.lit): quarter-area bound through squared unsigned areas. |
| 1967 P1 | 13 | [Solution](imo_1967_p1/solution.lit): necessity and sufficiency for arbitrary disk placement and the stated acute-angle conditions. |
| 1968 P1 | 15 | [Solution](imo_1968_p1/solution.lit): unique existence with witness `(4,5,6)` and all angle-order alternatives. |
| 1969 P4 | 17 | [Solution](imo_1969_p4/solution.lit): common external tangent distinct from the diameter line, from incidence, tangency and side conditions. |
| 1970 P1 | 18 | [Solution](imo_1970_p1/solution.lit): radius ratio identity, with Stewart and radius equations derived from the configuration. |
| 1970 P6 | 20 | [Solution](imo_1970_p6/solution.lit): seventy-percent bound from geometric five-point bounds and finite incidence counting. |

Each package includes its own required definitions and `litex.config`. Read the
actual theorem hypotheses when reusing scalar or normalized variants; they do
not supply geometric constructions beyond their statements.

Run from the repository root:

```sh
target/release/litex -lang en -strict -f examples/imo/geometry/imo_1960_p6/Solution-1/solution_part_b.lit
```

All fifteen packages have historical strict-verification evidence. This
organization task rechecked two representative packages at their new paths;
see [verification.md](../verification.md) for the exact coverage. Development
logs remain in their owning local workspaces.

[All IMO problems](../README.md) · [Geometry library and modeling conventions](../../../showcases/2D_Geometry/README.md)
