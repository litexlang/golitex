# Mathematics in Litex

Selected mathematics from [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/), by Jeremy Avigad and Patrick Massot, expressed and proved in Litex. The original teaches Lean 4 and Mathlib; this showcase follows its mathematical ideas through a different formal interface: definitions introduce objects and relationships, and explicit facts develop the proof.

Start with a witness for an even number, then follow functions and limits, images and inverse images, recursive constructions, records, and algebraic hierarchies. The examples show how a small mathematical vocabulary grows into a reusable context. They also make it possible to discuss Litex and Lean using the same source mathematics, without treating source lines or tactic demonstrations as a completion metric.

## From a definition to a witness

Chapter 1 defines an even natural number by its half. If `n = 2k`, multiplying by `m` gives the new witness `mk`:

```litex
prop even(n N):
    exist k N st {n = 2 * k}

thm even_mul:
    ? forall m, n N:
        $even(n)
        =>:
            $even(m * n)
    obtain k from $even(n)
    witness $even(m * n) from m * k:
        m * n = m * (2 * k) = 2 * (m * k)
```

`even` is a relationship, `k` is a mathematical witness, and `obtain` and `witness` expose the two directions of using the definition. The [chapter](chapter01-introduction.lit) retains one proof of this result where the source gives several Lean proof styles.

## From elementwise facts to set equality

Chapter 4 uses the builtin `preimage_set(f, U)`. The preimage of an intersection equals the intersection of the preimages: prove each inclusion by following an element through `f`, then use set extensionality.

```litex
thm set_preimage_intersection:
    ? forall S, T set, f fn(x S) T, U, V power_set(T):
        preimage_set(f, intersect(U, V)) = intersect(preimage_set(f, U), preimage_set(f, V))
    claim:
        ? forall x preimage_set(f, intersect(U, V)):
            x $in intersect(preimage_set(f, U), preimage_set(f, V))
        f(x) $in intersect(U, V)
        f(x) $in U
        f(x) $in V
        x $in preimage_set(f, U)
        x $in preimage_set(f, V)
    by def preimage_set(f, intersect(U, V)) $subset intersect(preimage_set(f, U), preimage_set(f, V))
    claim:
        ? forall x intersect(preimage_set(f, U), preimage_set(f, V)):
            x $in preimage_set(f, intersect(U, V))
        x $in preimage_set(f, U)
        x $in preimage_set(f, V)
        f(x) $in U
        f(x) $in V
        f(x) $in intersect(U, V)
    by def intersect(preimage_set(f, U), preimage_set(f, V)) $subset preimage_set(f, intersect(U, V))
    by extension preimage_set(f, intersect(U, V)) = intersect(preimage_set(f, U), preimage_set(f, V))
```

The function and subset domains appear in the statement. The proof uses membership facts and two inclusions; it does not select an inverse function or assume injectivity. The [chapter](chapter04-sets-and-functions.lit) continues to images, inverses, indexed set operations and Schröder–Bernstein.

## From operations to mathematical structures

Chapter 8 puts a multiplication and identity into a monoid record, together with their laws. Two inverse candidates are equal by associativity and the identity equations:

```litex
prop is_semigroup(s nonempty_set, mul fn(x, y s) s):
    forall x, y, z s:
        mul(mul(x, y), z) = mul(x, mul(y, z))

struct Monoid<s nonempty_set>:
    mul fn(x, y s) s
    one s
    <=>:
        $is_semigroup(s, mul)
        forall x s:
            mul(one, x) = x
        forall x s:
            mul(x, one) = x

thm monoid_left_inverse_unique:
    ? forall s nonempty_set, monoid &Monoid<s>, a, b, c s:
        monoid.mul(b, a) = monoid.one
        monoid.mul(a, c) = monoid.one
        =>:
            b = c
    b = monoid.mul(b, monoid.one) = monoid.mul(b, monoid.mul(a, c)) = monoid.mul(monoid.mul(b, a), c) = monoid.mul(monoid.one, c) = c
```

Here the record owns callable operations and mathematical laws. The proof reads those laws through the supplied monoid object. The [chapter](chapter08-hierarchies.lit) develops further structures, morphisms and subobjects; it does not reproduce Lean's typeclass elaborator.

## Chapter map

The [module configuration](litex.config) selects the preface and Chapters 1–8 in dependency order. Each row describes implemented material, not complete coverage of every upstream section or declaration.

| Chapter | Mathematical thread | Entry |
| --- | --- | --- |
| 1 | Callable functions, arithmetic and parity witnesses | [Introduction](chapter01-introduction.lit) |
| 2 | Real calculations, generic algebra, real inequalities, order/divisibility and general structures | [Basics](chapter02-basics.lit) |
| 3 | Quantifiers, function symmetry, bounds and sequence limits | [Logic](chapter03-logic.lit) |
| 4 | Images, preimages, inverses and Schröder–Bernstein | [Sets and functions](chapter04-sets-and-functions.lit) |
| 5 | Integer division, prime arithmetic, induction and recursion | [Elementary number theory](chapter05-elementary-number-theory.lit) |
| 6 | Finite sets, counting, lists, trees and formula encodings | [Discrete mathematics](chapter06-discrete-mathematics.lit) |
| 7 | Records, simplices, algebraic structures and Gaussian integers | [Structures](chapter07-structures.lit) |
| 8 | Monoids and groups, scalar actions, morphisms and subobjects | [Hierarchies](chapter08-hierarchies.lit) |

Chapter 2 now follows the original 2.1–2.5 sequence: it starts on `R`, and
introduces general algebraic structures in 2.2. Its [source map](CHAPTER2_SOURCE_MAP.md)
identifies the examples and explains the compatibility appendix.

The [concept guide](math_collections.md) connects these objects and their proof interfaces. [Experiment conclusions](EXPERIMENT_NOTES.md) distinguish observed capabilities, implementation limits and questions that still need measurement. [Source and license notices](NOTICE.md) identify the original book and pinned source.

## Verification scope

The previous selected module passed a complete ordered strict project check on Litex 1.0.6-beta on 2026-10-11; the three examples above passed independently. Chapter 2 was rewritten to follow the original book on 2026-10-13. Its current configured strict Chapter 2 check and Chapter 3 consumer check are recorded separately in [verification evidence](verification.json). The earlier whole-module receipt covers the earlier Chapter 2 bytes; Chapters 4–8 have not been rerun as part of this alignment. There is no imported standard-library or cite module, and no active user `trust`, `axiom` or `abstract_prop` in the exports.

Strict verification is acceptance by Litex's current verifier. Its builtin and inference rules and named foundation releases remain part of the verification boundary. These chapters have not been certified by the Lean kernel. No comparative soundness, speed or AI success-rate result is claimed.

The source book has 13 chapters. Current-version migration of Chapters 9–13 and some omitted mathematics within earlier chapters remain outside this distribution. An independently checked topology draft does not establish the complete later-chapter dependency chain. This showcase presents the selected runnable development and does not claim to be a complete translation of *Mathematics in Lean*.
