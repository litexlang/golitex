# Mathematical Collections

## Published scope

The current public collection exports `chap1`, the source-ordered Chapter 1
prefix. It models recurrence mathematics as callable functions rather than
relations over candidate values.

## Main interfaces

- `hanoi_moves`, `shifted_hanoi_moves`: a recursive move count and its closed
  form.
- `line_regions`, `triangular_sum`, `bent_line_regions`: planar-region and
  triangular-number recurrences.
- `josephus_survivor`: the base/even/odd source recurrence with checked
  concrete consumers.
- `binary_value`, `cyclic_left_bit`, and the binary/radix affine interfaces:
  typed positional representations and source recurrences.

Natural indices use `N`; positive indices use `N+`; finite positional values
use builtin closed-range `sum`. Existing narrow trust is preserved only where
the former chapter recorded proof debt or a cold/session replay performance
fallback. No new trust was introduced by publication recovery.

## Dependency order

Chapter 1 is a leaf module over the standard Litex environment. Future
chapters must be added to `litex.config` in source order and must pass both
their file gate and the complete retained-prefix repository gate.
