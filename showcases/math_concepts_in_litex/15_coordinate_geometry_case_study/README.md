# Coordinate Geometry Case Study

This showcase demonstrates formal verification of coordinate geometry problems using Litex.

## Structure

- **geo/**: Shared geometric definitions and theorems (flatten module)
- **problem_XXX/**: Individual verified problems (49 total)

Each problem is a standalone module. Problems that need the shared geometry library import `../geo`.

## Verification

First, build Litex from the repository root:

```bash
cargo build --release
```

Verify a single problem module:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/problem_639
```

Verify every problem module independently:

```bash
for d in showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/problem_*; do
  target/release/litex -compact -runner -r "$d" || exit 1
done
```

## Problems Included

1. **problem_13**
2. **problem_19**
3. **problem_207**: Square and angle bisector
4. **problem_210**: Coordinate geometry proof
5. **problem_212**: Quadrilateral problem
6. **problem_214**: Angle congruence
7. **problem_217**: Extension and perpendicularity
8. **problem_220**
9. **problem_223**
10. **problem_225**
11. **problem_227**
12. **problem_228**
13. **problem_229**
14. **problem_233**
15. **problem_234**
16. **problem_263**
17. **problem_282**
18. **problem_296**
19. **problem_297**: Geometric proof
20. **problem_442**
21. **problem_464**
22. **problem_465**
23. **problem_473**
24. **problem_474**
25. **problem_476**
26. **problem_487**
27. **problem_505**
28. **problem_511**
29. **problem_512**
30. **problem_513**
31. **problem_546**
32. **problem_547**
33. **problem_551**
34. **problem_639**: Perpendicular bisector property
35. **problem_860**
36. **problem_870**
37. **problem_877**
38. **problem_880**
39. **problem_903**
40. **problem_911**
41. **problem_913**
42. **problem_914**
43. **problem_924**
44. **problem_927**
45. **problem_928**
46. **problem_934**
47. **problem_951**
48. **problem_1141**
49. **problem_1150**

## Validation Status

- 49/49 problem modules passed the migration verification batch.
- The shared `geo` module passed a full recursive verification audit: 7,890/7,890 result nodes successful, with no parse gaps or stderr.
- `problem_474`, which exercises the updated shared dependency, passed a fresh integration verification: 292/292 result nodes successful, with no parse gaps or stderr.

## Important Notes

- For problems with `translation.lit`, export order matters: translation must come before solution.
- The showcase root is a plain directory (no `litex.config`) so problem modules can be verified independently.
- Each problem directory contains its `litex.config` and every `.lit` source referenced by that configuration; unreferenced development probes and verifier logs are intentionally excluded.
- Validation and migration audit completed on 2026-09-13.
