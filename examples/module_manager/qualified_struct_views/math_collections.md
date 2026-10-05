# Mathematical interface inventory

- `Lib::facts::Pair`: two real fields, `first` and `second`.
- `Other::facts::Pair`: two integer fields with the same spelling.
- `local::Pair`: two natural fields with the same spelling.
- `Lib::facts::Tagged<S>`: value in the nonempty set S and a natural tag.
- `make`: a real parameter and an explicitly qualified real-pair return carrier.
- `Nested`: an explicitly qualified Pair-valued field and a natural tag.

This is a module/parser acceptance fixture. Each assertion checks native tuple
membership, field projection or a declared return/field carrier. It introduces
no mathematical axiom and does not depend on Cartesian enumeration.

`&Lib::facts::Tagged<S>` is the generic carrier interface. It requires S to be
nonempty and keeps its value field in S, while the tag remains natural. The
empty-set argument is deliberately rejected. Its dependencies are the imported
struct definition and ordinary tuple membership; downstream field and function
return checks consume that declared carrier.

The three Pair definitions deliberately share a spelling but have different
coordinate carriers. `have item &Lib::facts::Pair = (1/2,3/2)` is a real-pair
construction; the same tuple in the integer or natural Pair is rejected. The
qualified interface keeps that owner through parsing rather than inferring it
from the spelling alone. This fixture has no proof or trust debt. Nested field
types are supported; automatically rewriting chained fields through equal
receivers is outside this parser acceptance contract.
