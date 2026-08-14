# Mathematical Design: Sets, Functions, and Relations

## Implemented first-version slice

`main.lit` now checks a set-valued preimage interface, preservation of binary
intersections, supplied left/right/two-sided inverse laws, the implication
from a two-sided inverse to bijectivity, and `same_parity` as a concrete
equivalence relation. It contains no direct `trust`.

## Core interface cards

### Image

- **Meaning:** values reached by `f` from a supplied subset of its domain.
- **Form:** a template-provided set value, represented by the range of the
  restricted function.
- **Sketch:** `set_image<S,T,f,A> = fn_range(fn(x A) T {f(x)})`.
- **Rejected form:** only a binary proposition `is_image_member(y)`; callers
  need an actual set for subset and equality statements.
- **Use:** image-union, image/preimage adjunction, ranges of linear maps.

### Preimage

- **Meaning:** domain values mapped into a supplied target subset.
- **Form:** `have fn` returning `power_set(S)`.
- **Sketch:** `set_preimage(B) = {x S: f(x) $in B}`.
- **Rejected form:** a theorem schema for every membership query.
- **Use:** preimage-intersection and inverse reasoning.

### Function properties

- **Meaning:** injectivity tests equality reflection; surjectivity supplies a
  preimage; bijectivity combines them.
- **Form:** `prop` on supplied carriers and functions.
- **Rejected form:** structures in the first tranche; no caller yet needs to
  carry a packaged bijection and project fields.
- **Use:** inverse existence and uniqueness.

### Inverse

- **Meaning:** the callable value selected from the unique preimage relation
  of a bijection.
- **Form:** relation plus unique-existence theorem, then
  `have fn ... by exist!`.
- **Rejected form:** an arbitrary default-valued total inverse hidden from the
  reader; it obscures the intended domain and choice boundary.
- **Use:** two-sided inverse theorem and later coordinate maps.

The first version stops one direction earlier: it accepts a callable inverse
and proves the resulting bijection. Constructing a callable inverse from an
arbitrary bijection remains the explicit selection boundary.

### Equivalence relation

- **Meaning:** a binary relation with reflexive, symmetric, and transitive
  laws.
- **Form:** initially a `prop` on a supplied relation. Promote to a `struct`
  only if downstream modules need to pass and project packaged relation data.
- **Use:** congruence as the one concrete example.

## Main dependency DAG

```text
Builtin set/function carriers
  -> image, preimage, composition, restriction          [definition]
  -> injective, surjective, bijective                    [signature, definition]
  -> inverse candidate relation                         [definition]
  -> inverse existence                                  [existence]
  -> inverse uniqueness                                 [uniqueness]
  -> supplied inverse laws                               [implemented proof]
  -> two-sided inverse implies bijection                 [implemented proof]
  -> selected inverse from arbitrary bijection           [future selection]

binary relation
  -> reflexive/symmetric/transitive                      [definition]
  -> equivalence relation                               [law]
  -> congruence example                                 [proof]
```

The inverse selection is the primary well-definedness boundary. If current
syntax or the verifier cannot support the ideal selected function naturally,
record that exact blocker instead of replacing the concept with a default-
valued or trusted surrogate.
