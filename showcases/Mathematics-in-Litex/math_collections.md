# Mathematical interfaces in this showcase

This guide follows the selected Chapters 1–8 of *Mathematics in Lean* through their Litex counterparts. It explains the main objects, dependencies and use boundaries. The [chapter map](README.md#chapter-map) locates the executable development.

## Witnesses and relationships

Chapter 1's `even(n N)` is a predicate with an existential body: a witness `k N` satisfies `n = 2 * k`. `even_mul` obtains that half and constructs a new one. The predicate describes candidates; the theorem establishes a fact about them. A predicate named after a theorem would not supply a proof of that theorem.

Chapter 3 uses relationships for function symmetry, bounds and convergence. Its real sequence interface gives the epsilon/cutoff formulation rather than selecting a limit without existence and uniqueness. Product convergence uses a bound on one convergent sequence and a common cutoff before estimating the product.

## Sets and callable functions

Chapter 4 uses native binary set operations and `preimage_set(f, U)`. The set argument has carrier `power_set(T)` when `f` maps `S` to `T`; the preimage belongs to `power_set(S)`. Images retain a source-facing `set_image` template built from `fn_range` on the restricted map.

The proof interface is elementwise: expose membership, evaluate the map, construct a range witness, then establish inclusions or equality. A point fiber `preimage(f, y)` and a set inverse image `preimage_set(f, U)` are distinct objects. Neither chooses an inverse function. Chapter 4's total inverse construction has an explicit nonempty source and default element for outputs with no preimage.

Indexed intersections retain an ambient carrier, including the empty-index case. Changing that carrier or assuming a nonempty index silently would change the mathematics. Schröder–Bernstein depends on the preceding inverse and recursive set-construction interfaces.

## Selected values and recursion

Chapter 5's integer quotient is selected through checked unique existence, with its divisor condition in the interface. Natural-number sums and Fibonacci constructions are callable functions with recursive equations. Chapter 6 uses finite sets and counting, length-indexed `CheckedList` records, and natural-number encodings for recursive trees and formulas.

A relation characterizing possible values is useful in a construction, but it does not replace the callable value consumed later. Recursion, witness existence and uniqueness remain proof obligations. The examples do not justify arbitrary unchecked recursive definitions.

## Data together with laws

Chapter 7 starts with `Point`, whose real coordinates support a callable addition. `StandardTwoSimplex` adds nonnegativity and a sum-one law to its coordinates. Algebraic structures similarly package operations and laws; Gaussian integers retain their arithmetic data and Euclidean-domain development.

Chapter 8's `Monoid<s nonempty_set>` owns `mul` and `one` with associativity and two identity laws. `monoid_left_inverse_unique` reads those laws to compare inverse candidates. Group, scalar-action and morphism constructions reuse this pattern. Relations such as preservation or subobject membership remain propositions about candidates; a proposition with no underlying map is not a morphism object.

These declarations preserve selected mathematical data and laws from the source. They do not reproduce Lean's coercions, instance search, typeclass elaboration or all hierarchy presentation variants. Chapter 2 follows the original five-section order, starting with concrete real calculations. General Ring/Group objects enter in 2.2; general partial orders, lattices, ordered rings and metrics enter in 2.5. The [source map](CHAPTER2_SOURCE_MAP.md) also explains total natural divisibility/gcd and the derivation of metric nonnegativity. Historical operation-and-law theorem headers remain in a compatibility appendix for later consumers.

## Dependency and proof boundaries

The manifest orders the preface and Chapters 1–8. Later exports may cite earlier chapter names; no external module is imported. The executable source contains no user trust, axiom or abstract predicate. Named foundation releases and the verifier's builtin/inference rules remain part of its checked mathematical environment.

The historical 2026-10-11 module gate checked all selected exports together. Current Chapter 2 and Chapter 3 consumer gates cover the rewritten chapter and its preceding context; the changed module has not been rerun through Chapter 8. It does not establish complete source coverage, correctness of every verifier rule or Lean certification. Chapter 2's source alignment introduces explicit total-natural and source-metric interfaces, retaining the old signatures for compatibility.
