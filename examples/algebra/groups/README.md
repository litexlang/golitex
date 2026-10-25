# Shared group theory consumers

These examples import `std/algebra` as `Algebra` through `[import std]`.
They exercise the shared mathematical definitions rather than redeclaring a
local Group or assuming group theorems.

- [main.lit](main.lit) constructs integer addition, calls all twelve theorem
  interfaces, proves the doubling map injective via its trivial kernel, and
  constructs a one-element group.
- [noncommutative/main.lit](noncommutative/main.lit) constructs the real
  Heisenberg group. Its law is `(a,b,c)*(x,y,z)=(a+x,b+y,c+z+a*y)` and its
  inverse is `(-a,-b,a*b-c)`. The generators `(1,0,0)` and `(0,1,0)` produce
  third coordinates one and zero in opposite orders. Cancellation and the
  normal-kernel theorem still apply.
- [negative/](negative/) shares a valid integer-group prefix. Each fixture
  must accept that prefix and reject exactly its final statement.

Run `python3 examples/algebra/groups/check.py` from the repository root. It
checks the library, the migrated integer lecture and both independent example
projects in strict mode. Six rejection controls cover a translation used as
a homomorphism, a missing trivial-kernel premise, arbitrary group commutativity,
a wrong inverse, an empty subgroup and a missing cancellation equality.
It also checks the actual library in archive and shared-data installation
layouts without `LITEX_STD_PATH`, plus the std package inventory.

The examples have no source trust, axioms or abstract predicates. Their results
use Litex's verifier and builtin foundation; no Lean replay is claimed.
[math_collections.md](math_collections.md) describes the consumers' roles.
