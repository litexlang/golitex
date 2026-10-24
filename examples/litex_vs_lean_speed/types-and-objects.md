# Types, objects, and ordinary mathematical notation

Litex keeps number-set membership and conditions of use as facts about
mathematical objects. The examples below show where this lets the source retain
an ordinary calculation, a function call, or a statement about a set. Each
measured example links to an existing runnable Litex/Lean pair in this directory.

A small example makes the object model visible:

```litex
forall callable set:
    callable $in fn(x R) R
    =>:
        callable(4) $in R
```

The same object is introduced as a set and used as a function under a
function-space membership premise. This is a conditional statement: it does
not establish that an arbitrary set is a function. The premise supplies the
callable contract without replacing the source object.

The [runnable example](../proof_nodes/equal/by_object_definition/by_fn_application/callable_alias_special_property.lit)
contains this statement. A native Lean declaration such as `f : Real → Real`
provides the function interface through the declared type. A Lean set-graph
encoding can instead provide an evaluation interface from a proof that the
graph defines a function. Lean supports custom interfaces and coercions, so
this comparison concerns the default organization of objects and evidence,
not a mathematical statement that Lean cannot express.

## 1. Keep a textbook proof across number sets

To prove that sqrt(2) is irrational, assume it is a reduced fraction p/q.
The equation p² = 2q² makes p even; substituting p/2 then makes q even,
contradicting coprimality. The Litex proof follows that route:

```litex
by contra:
    ? not sqrt(2) $in Q
    release thm rational_has_unique_reduced_fraction(sqrt(2))
    obtain p, q from exist! p Z, q N+ st {sqrt(2) = p / q, gcd(p, q) = 1}

    p^2 = (sqrt(2) * q)^2 = sqrt(2)^2 * q^2 = 2 * q^2
    p^2 % 2 = (2 * q^2) % 2 = 0
    release thm prime_divides_power(p, 2, 2)

    p / 2 $in Z
    q^2 = p^2 / 2 = 2 * (p / 2)^2
    q^2 % 2 = (2 * (p / 2)^2) % 2 = 0
    release thm prime_divides_power(q, 2, 2)

    impossible 2 <= gcd(p, q) = 1
```

`p / 2 $in Z` establishes integer membership for the quotient used in the next
equation. The mathematical calculation continues with the same expressions.

The existing Lean proof follows the same parity argument. Its real equation
is transported to integer and natural-number equations. This contextual
excerpt shows one such bridge; `q`, `m`, and `hreal` are defined in the full file:

```lean
have hint : q.num ^ 2 = 2 * (m : Int) ^ 2 := by
  exact_mod_cast hreal
```

The complete source has **12 code lines in Litex and 37 in Lean**, with
**64.7% fewer non-whitespace characters** in the Litex file. Part of the Lean
source handles representations and casts; the total difference also reflects
the selected lemmas and checking interfaces. A direct citation of Mathlib's
irrationality theorem would be a different, much shorter Lean proof route.

[Full Litex proof](sources/new-round/sqrt_two_irrational.lit) ·
[Full Lean proof](sources/new-round/sqrt_two_irrational__scratch.lean)

## 2. Use a positive natural number in integer arithmetic

The quotient-remainder equation uses an integer a and a positive natural
divisor d:

```litex
forall a Z,d N+:
    a=d*quot(a,d)+a%d
```

The measured Lean source chooses `Int` for a and `Nat` for d, and explicitly
embeds d into integer arithmetic:

```lean
import Mathlib

example : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm
```

Litex retains the same d throughout the equation. This pair has **71.4%
fewer non-whitespace characters** on the Litex side. The comparison is specific
to these interfaces: a Lean author could instead choose an integer divisor,
or let coercion inference insert some conversions. Lean does not require every
numeric conversion to be written explicitly.

[Litex source](sources/new-round/integer_division_decomposition.lit) ·
[Lean source](sources/new-round/integer_division_decomposition__lemma.lean) ·
[Lean coercions](https://lean-lang.org/doc/reference/latest/Coercions/)

## 3. Put the condition in the function domain

For a reciprocal, the nonzero condition belongs to the definition's domain:

```litex
have fn bench_recip(x R:x!=0) R=1/x
bench_recip(2)=1/2
```

The call remains ordinary function notation. Litex must establish that the
argument satisfies the domain condition. In the paired Lean interface, the
caller passes a proof of that condition:

```lean
import Mathlib

noncomputable def bench_recip (x : Real) (_hx : x ≠ 0) : Real := 1/x
theorem bench_use : bench_recip 2 (by norm_num) = 1/2 := by rfl
```

Both interfaces preserve the nonzero requirement. This pair has **53.8% fewer
non-whitespace characters** in Litex. Lean can also use implicit proof
parameters and automation; the displayed explicit interface is the one whose
historical checking time is recorded below.

[Litex source](sources/declarations/guarded_function.lit) ·
[Lean source](sources/declarations/guarded_function.lean)

## 4. Ask for the size of a finite set

The everyday mathematical statement is that {1, 2, 3} has three elements:

```litex
finite_set_size({1,2,3})=3
```

The paired Lean source selects a finite-set representation and element type:

```lean
import Mathlib

example : ({1, 2, 3} : Finset Nat).card = 3 := by decide
```

Litex's constructor and cardinality operation carry their own checking
requirements without an element-type annotation in this source. The pair has
**40.9% fewer non-whitespace characters** in Litex. This difference includes
the theorem wrapper and proof as well as the representation annotation.

[Litex source](sources/new-round/finite_cardinality.lit) ·
[Lean source](sources/new-round/finite_cardinality__decide.lean)

## Source size and recorded checking time

The source counts below exclude blank lines, full-line comments, imports,
`set_option` lines, and whitespace. They include declarations, statements,
proofs, and names in the linked files. Library and builtin implementations
are outside both source counts. These are counts of the existing pairs, not
lower bounds on the shortest possible programs.

| Existing source pair | Litex / Lean characters | Fewer characters in Litex | Litex / Lean checking time (ms) | Lean ÷ Litex |
| --- | ---: | ---: | ---: | ---: |
| sqrt(2), matched parity proof | 326 / 923 | 64.7% | 199.285 / 779.754 | 3.91× |
| Integer quotient and remainder | 30 / 105 | 71.4% | 1.135 / 3.341 | 2.94× |
| Guarded reciprocal, definition and call | 49 / 106 | 53.8% | 1.823 / 8.583 | 4.71× |
| Three-element set cardinality | 26 / 44 | 40.9% | 0.049 / 3.597 | 73.43× |

[Source counts, file hashes, and validation](results/type-object-source-counts.json)
identify the exact source snapshots used for the size comparison. The four
pairs were revalidated with the release Litex CLI and Lean; the additional
callable example was also checked. Litex's `-strict` excludes user trust and
axioms while still relying on builtin and inference rules. These checks do not
establish that the two systems have identical trusted bases.

The times are **historical measurements recorded on 2026-10-23**, not a new
measurement accompanying this guide. Three rows are backed by the
[new-round raw samples](results/new-round-raw.json) and
[summary](results/new-round-summary.json). The reciprocal row uses the rounded
aggregate in the [declaration-program table](README.md);
its original samples are not included in the published results directory.

Both timing intervals exclude process startup and imports. Litex measures
parsing, well-definedness, verification, storage, and evidence construction;
Lean measures synchronous command elaboration and kernel checking after
command parsing. See the [measurement contract](README.md#怎么读这些数字) and
[recorded environment](results/environment.json). The cardinality ratio is
large, but its absolute difference is about 3.55 ms.

This directory selects examples where Litex checked faster. The figures do
not establish an overall speed ranking or isolate type design as the cause
of the speed differences. Lean inference and library choices can reduce source
size; some other existing comparisons have shorter Lean source. What these
examples make observable is the Litex source interface: number-set facts,
domain conditions, and mathematical operations can stay directly in the
calculation the reader is following.

For a controlled follow-up on whether numeric bridges explain checking time,
see [the type-bridge experiment](type-bridge-experiment.md). It keeps each
Lean proposition fixed, compares proof variants, and separates elaboration
from the final declaration check. Its measurements retain counterexamples to
the claim that fewer explicit casts or a direct lemma always run faster.
