# Coordinate Geometry Case Study

This showcase packages the public Euclidean geometry library together with a
fully checked Chinese middle-school geometry case (Problem 217,
`zhongkao_13`).  It demonstrates the intended workflow: geometric predicates
state the problem, while coordinate/vector lemmas discharge the algebra.

## Contents

- `main.lit`: the flattened Euclidean geometry knowledge base;
- `problem_217_midpoint.lit`: the verified isosceles-right-triangle midpoint
  proof, with natural-language/formalization comments;
- `math_collections.md`: concepts and reusable interfaces;
- `litex.config`: standalone exports.

Run from the repository root:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/15_coordinate_geometry_case_study
```

The case file is exported separately so the library and the worked problem can
be checked independently. The library is included as the current project
snapshot; future general-purpose additions should be reviewed before moving
from a case study into the shared KB.
