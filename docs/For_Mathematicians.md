# For Mathematicians

Litex is not trying to replace Lean. It tests a different hypothesis: that a
smaller, readable, fact-oriented formal language can make checked mathematics
cheap enough for students, domain scientists, and AI agents to produce useful
formal data at scale.

This page is for mathematicians who want to know whether Litex can express
ordinary mathematical objects, not only short arithmetic calculations. The
answer is currently mixed in the useful way: some examples are fully checked;
some examples are axiomatic interfaces; some examples deliberately expose
proof debt through `know`, `abstract_prop`, or a trusted theorem interface.

## Mathematical Surface

Litex starts from the same two things mathematicians write on a page:
objects and statements. A file builds a local mathematical world by declaring
objects, naming predicates, proving claims, and reusing the resulting facts.

| Litex form | Mathematical reading |
| --- | --- |
| `S set` | A set. |
| `x S` | An element `x` of the set `S`. |
| `S nonempty_set` | A nonempty set, with nonemptiness available to the verifier. |
| `power_set(S)` | The set of subsets of `S`. |
| `cart(S, T)` | The Cartesian product `S x T`. |
| `fn(x S) T` | A function from `S` to `T`. |
| `fn(i I, j J) R` | An indexed family, such as a matrix entry function. |
| `prop P(...)` | A reusable mathematical predicate or relation. |
| `abstract_prop P(...)` | A named primitive relation whose meaning is supplied axiomatically. |
| `struct Group<s nonempty_set>` | A structure over a nonempty carrier set, with fields and defining properties. |
| `template` | A parameterized construction, such as a quotient-set function for every carrier. |
| `forall`, `exist`, `exist!` | Universal, existential, and unique-existence statements. |
| `claim`, `thm` | A checked local claim or named theorem. |
| `witness` | The explicit witness for an existential statement. |
| `know` | A trusted fact or background theorem. It is not a proof step hidden from view; it marks exactly what is being assumed. |

The important design choice is that proofs usually move forward. Instead of
asking the reader to decode tactic scripts, a Litex proof tends to read as a
sequence of intermediate facts:

```text
have fn f(x R: x > 0) R = x^2

claim $increasing({x R: x > 0}, f):
    claim forall! x, y R: x > 0, y > 0, x < y => f(x) < f(y):
        f(y) - f(x) = y^2 - x^2 = (y - x) * (y + x) > 0
```

This is not a claim that the current standard library is as broad as mathlib.
It is a claim about interface: the first object a mathematician sees is the
mathematical argument, with assumptions and trusted gaps made explicit.

## Example Gallery

The examples below are meant to be read as artifacts, not screenshots. Each
file is runnable with the Litex verifier, and each one shows a different part
of the mathematical surface.

| Area | File | What to look for | Status |
| --- | --- | --- | --- |
| Algebra: quotient groups | [`examples/04_structures/group_quotient.lit`](../examples/04_structures/group_quotient.lit) | A group structure, normal subgroups, left cosets, the quotient set `G/H`, and the quotient multiplication interface `(xH)(yH) = (xy)H`. | Checked quotient-set construction and checked quotient-operation interface for normal subgroups. |
| Algebra: presentation skeleton | [`examples/04_structures/group_property.lit`](../examples/04_structures/group_property.lit) | Homomorphisms, isomorphisms, two-generator presentations, normal forms, and cardinality-bound interfaces. | Assumption-backed proof skeleton. The file verifies as an interface, but many group-theory lemmas are explicitly marked by `abstract_prop` or `know`. |
| Geometry | [`examples/05_case_studies/Hilbert_axioms_on_Euclidean_geometry.lit`](../examples/05_case_studies/Hilbert_axioms_on_Euclidean_geometry.lit) | Points, lines, planes, primitive incidence/congruence relations, and functions such as `line_of(A, B)` and `plane_of(A, B, C)` introduced from unique existence. | Axiomatic development. The verifier checks use of the stated Hilbert-style axioms; it does not construct a Euclidean model. |
| Set theory: maximal principles | [`examples/01_proof_patterns/by_zorn_lemma.lit`](../examples/01_proof_patterns/by_zorn_lemma.lit) | A partial order, chain upper-bound condition, and a maximal element obtained through the Zorn interface. | Checked use of a trusted theorem interface. Zorn's lemma itself is part of the trusted background here. |
| Linear algebra | [`examples/04_structures/diagonal_matrix.lit`](../examples/04_structures/diagonal_matrix.lit) | An indexed matrix as `fn(i closed_range(1, n), j closed_range(1, n)) R`, plus a proof that a displayed `3 x 3` identity matrix is diagonal. | Checked finite-index example. |
| Analysis | [`examples/04_structures/monotonicity_of_a_function.lit`](../examples/04_structures/monotonicity_of_a_function.lit) | Monotonicity of `x^2` on positive reals proved by the algebraic identity `y^2 - x^2 = (y - x)(y + x)`. | Checked elementary analysis example. |
| Analysis interface | [`examples/04_structures/abstract_integral.lit`](../examples/04_structures/abstract_integral.lit) | An abstract integral predicate, integrability, and an additivity theorem exposed as a reusable interface. | Axiomatic interface. Useful for expressing downstream arguments before a full integration library exists. |
| Countability | [`examples/05_case_studies/exist_N^2_to_N_bijection.lit`](../examples/05_case_studies/exist_N%5E2_to_N_bijection.lit) | Triangular numbers, Cantor pairing, injectivity, surjectivity, and an explicit bijection from `N x N` to `N`. | Checked in the current verifier; relies on arithmetic and induction support. |
| Number theory | [`examples/05_case_studies/detailed_there_exists_infinite_number_of_prime_numbers.lit`](../examples/05_case_studies/detailed_there_exists_infinite_number_of_prime_numbers.lit) | A Euclid-style proof that beyond every positive integer there is a larger prime, using products and divisibility. | Checked in the current verifier; relies on product and divisibility rules. |
| Algorithms and number theory | [`examples/05_case_studies/euclid_algorithm.lit`](../examples/05_case_studies/euclid_algorithm.lit) | Recursive quotient/remainder functions, induction on a measure, and Bezout-style extended gcd structure. | Checked larger development, useful for testing recursive definitions and measure induction. |

## A Close-Up: Quotient Groups

The quotient-group example is a good first serious algebra file because it is
not just a proposition. It constructs reusable objects and makes the
well-definedness obligation visible.

```text
macro G "&Group<s>{g}"

prop is_left_coset_with_representative(s nonempty_set, g &Group<s>, h power_set(s), x s, c power_set(s)):
    forall y s:
        =>:
            y $in c
        <=>:
            exist a s st {a $in h, y = @G.op(x, a)}

prop is_group_quotient_set(s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s))):
    q = {c power_set(s): $is_left_coset(s, g, h, c)}
```

The file then proves the set-theoretic function condition:

```text
forall s nonempty_set, g &Group<s>, h power_set(s):
    exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}
```

After that, Litex can turn the unique-existence theorem into a callable
quotient-set function:

```text
template group_quotient<s nonempty_set>:
    have fn group_quotient as set:
        forall g &Group<s>, h power_set(s):
            exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}
```

This is the pattern mathematicians should look for: define the graph of a
construction, prove unique existence, and then obtain a function with the right
defining property.

The same file then records the quotient multiplication shape:

```text
prop is_quotient_multiplication(s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s)), quotient_mul fn(c1, c2 q) q):
    forall c1, c2 q:
        $is_quotient_product_coset(s, g, h, c1, c2, quotient_mul(c1, c2))
```

The file proves the normal-subgroup representative-independence step as a named
theorem:

```text
thm quotient_product_well_defined_thm:
    prove:
        forall s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s)):
            $is_normal_subgroup(s, g, h)
            $is_group_quotient_set(s, g, h, q)
            =>:
                $quotient_product_well_defined(s, g, h, q)
```

It then uses unique existence to build the quotient multiplication function:

```text
template quotient_op<s nonempty_set, q power_set(power_set(s))>:
    have fn quotient_op as set:
        forall g &Group<s>, h power_set(s):
            $is_normal_subgroup(s, g, h)
            $is_group_quotient_set(s, g, h, q)
            =>:
                exist! quotient_mul fn(c1, c2 q) q st {$is_quotient_multiplication(s, g, h, q, quotient_mul)}
```

The final interface theorem exposes both facts together for downstream use:

```text
thm quotient_op_interface_thm:
    prove:
        forall g &Group<R>, h power_set(R), q power_set(power_set(R)):
            $is_normal_subgroup(R, g, h)
            $is_group_quotient_set(R, g, h, q)
            =>:
                $quotient_product_well_defined(R, g, h, q)
                $is_quotient_multiplication(R, g, h, q, \quotient_op<R, q>(g, h))
```

## What Is Checked

Litex checks that a proof line follows from the current local context,
definitions, previous claims, imported facts, builtin rules, infer rules, and
trusted declarations. It also checks well-formedness of objects such as
functions, set comprehensions, structures, templates, and witnesses.

The current trusted surface is intentionally visible:

1. `know` introduces a trusted theorem, axiom, or temporary proof-debt fact.
2. `abstract_prop` introduces a primitive predicate whose semantics are not
   reduced by the verifier.
3. `by zorn_lemma` and similar interfaces expose a high-level theorem as a
   trusted rule.
4. Builtin arithmetic and inference rules are part of the verifier's trusted
   implementation.

This makes Litex useful for pressure-testing mathematics. If a proof needs a
missing theorem, the file can still say exactly which theorem is missing, and
the rest of the argument can remain checkable.

## How To Evaluate The Examples

From the repository root, run a selected file directly:

```text
target/debug/litex -f examples/04_structures/group_quotient.lit
target/debug/litex -f examples/04_structures/diagonal_matrix.lit
target/debug/litex -f examples/04_structures/monotonicity_of_a_function.lit
```

For a broader pass over examples, use the repository test suite described in
the setup and contribution docs.

## Coming Next

Good next examples for this page are not marketing examples; they should be
runnable mathematical files with clear status labels. The natural targets are:

1. simplicial complexes and simplex-like constructions, where the objects are
   finite sets, faces, boundary maps, and incidence relations;
2. finite-dimensional linear algebra and optimization, where matrix, vector,
   convexity, and order statements should remain close to paper mathematics;
3. real analysis theorem fragments, such as monotone convergence, where the
   missing least-upper-bound and sequence-limit interfaces can be isolated
   cleanly;
4. probability and expectation interfaces, where downstream finance,
   engineering, and science arguments often need formal reliability before a
   full measure-theory library is available.

Those examples should appear here only after their files exist and their
checked, axiomatic, or blocked status is explicit.
