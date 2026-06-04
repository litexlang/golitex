# Typical Examples

This page collects a few small but representative Litex examples. The point is
not that these are hard theorems. The point is to show the same interface at
several scales: write a fact, let Litex match it against the context, and keep
growing a checked mathematical object.

## 1. Matching And Substitution

The smallest useful pattern is a syllogism. We introduce a set of humans, an
object `Socrates` in that set, an abstract predicate `mortal`, and a general
fact saying that every human is mortal.

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

know forall x human:
    $mortal(x)

$mortal(Socrates)
```

The final line is not a command about a proof state. It is the mathematical fact
we want. Litex sees that the known `forall` fact has the same predicate shape,
checks that `Socrates $in human`, and substitutes `Socrates` for `x`.

The accepted fact can also carry an explanation like this:

```json
{
  "result": "success",
  "type": "AtomicFact",
  "line": 7,
  "stmt": "$mortal(Socrates)",
  "verified_by": {
    "type": "cite forall fact",
    "cite_source": {
      "line": 4
    },
    "cited_stmt": "forall x human:\n    $mortal(x)"
  }
}
```

Here `abstract_prop mortal(x)` only declares the predicate vocabulary. The
`know` line records an assumed background rule. Once `$mortal(Socrates)` is
accepted, it becomes part of the verified context for later facts.

Litex also supports the named-theorem route used by many formal systems:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

thm all_humans_are_mortal:
    prove:
        forall x human:
            $mortal(x)
    know $mortal(x)

by thm all_humans_are_mortal(Socrates)
$mortal(Socrates)
```

This is useful for standard-library facts, long results, or parameter-sensitive
theorems. The distinctive Litex style is that routine local reasoning can stay
as direct factual lines.

## 2. Structured Algebra

Litex can also define structured mathematical objects in a set-theoretic style.
The next example defines the group property, packages it as a `struct`, and then
defines subgroup and normal-subgroup predicates.

```litex
prop GroupProperty(s nonempty_set, inv fn(x s) s, op fn(x, y s) s, e s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(e, x) = x
        op(x, e) = x
    forall x s:
        op(x, inv(x)) = e
        op(inv(x), x) = e

struct Group<s nonempty_set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        $GroupProperty(s, inv, op, e)

macro G "&Group<s>{g}"

prop is_subgroup(s nonempty_set, g &Group<s>, h power_set(s)):
    @G.e $in h
    forall a, b s:
        a $in h
        b $in h
        =>:
            @G.op(a, b) $in h
    forall a s:
        a $in h
        =>:
            @G.inv(a) $in h

prop is_normal_subgroup(s nonempty_set, g &Group<s>, h power_set(s)):
    $is_subgroup(s, g, h)
    forall x, a s:
        a $in h
        =>:
            @G.op(@G.op(x, a), @G.inv(x)) $in h
```

There is no inheritance hierarchy hidden here. The carrier set, operations, and
relations are visible. A group object gives access to `@G.inv`, `@G.op`, and
`@G.e`; subgroup and normality are stated as relations among the carrier, the
group structure, and the subset.

The longer quotient-group development lives in
[`examples/04_structures/group_quotient.lit`](../../examples/04_structures/group_quotient.lit).

## 3. A Proof Shape: Infinitely Many Primes

The next example shows a proof block rather than only definitions. The `know`
block records background number-theory facts used by the final argument: a
product is divisible by every factor below the bound, every number at least `2`
has a prime divisor, and the finite product is at least the endpoint.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

# Background facts for this final proof block.
know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

The proof follows the classical Euclid move. For a bound `a`, take a prime
divisor `k` of `1 * 2 * ... * a + 1`. If `k <= a`, then the product is divisible
by `k`, so the product plus `1` has remainder `1` modulo `k`, contradicting the
choice of `k`. Therefore `k > a`, and it is the witness for a larger prime.

The full case study is in
[`examples/05_case_studies/there_exists_infinite_number_of_prime_numbers.lit`](../../examples/05_case_studies/there_exists_infinite_number_of_prime_numbers.lit).

## 4. Matrix And Scientific Objects

Litex also needs to handle the objects that appear in routine scientific and
engineering mathematics. Matrices are ordinary objects with indexed entries and
evaluable operations.

```litex
prove:
    matrix(R, 2, 2) = matrix(R, 2, 2)

    have a matrix(R, 2, 2) = [[1, 2], [3, 4]]

    a $in fn (x1 N_pos, x2 N_pos: x1 <= 2, x2 <= 2) R

    a(1, 1) = 1
    a(1, 2) = 2
    a(2, 1) = 3
    a(2, 2) = 4

eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]

have m matrix(R, 2, 2) = [[1, 0], [0, 1]]

eval m ++ m
eval [[2, 0], [0, 2]] -- [[1, 0], [0, 1]]
eval [[1, 2], [0, 1]] ** [[1, 0], [1, 1]]
eval 3 *. [[1, 2], [4, 5]]
eval [[2, 0], [0, 2]] ^^ 2
eval m ** m
eval 2 *. m
eval [[1 / 2, 1 / 3], [0, 1]] ** [[1, 0], [1 / 6, 1 / 2]]
eval (1 / 3) *. [[3, 6], [9, 12]]
```

This surface is intentionally close to ordinary classroom and engineering
notation: introduce a matrix, inspect entries, then evaluate addition,
subtraction, multiplication, scalar multiplication, powers, and exact rational
entries. The same direction should extend to linear algebra, probability,
optimization, numerical methods, and scientific derivations.

The full matrix example is in
[`examples/03_objects_and_data/matrix.lit`](../../examples/03_objects_and_data/matrix.lit).
