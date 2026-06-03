# For Mathematicians

Litex is not trying to replace Lean. It tests a different hypothesis: that a
smaller, readable, fact-oriented formal language can make checked mathematics
cheap enough for students, domain scientists, and AI agents to produce useful
formal data at scale.

This page is for readers who want to see a mathematical object built in the
style of ordinary algebra, not only a short arithmetic proof.

## Classic Example: A Quotient Set

The file `examples/04_structures/group_quotient.lit` is a compact quotient-set
construction for groups. It is a good first serious example because it uses
several high-level Litex tools in one small development:

1. `struct` builds a parameterized group structure over an arbitrary carrier
   set.
2. `template` expresses a family of quotient-set functions indexed by the
   carrier set.
3. The construction isolates the quotient-set layer: for any subset `h`, the
   set of left cosets is a definite object.
4. The last step uses the set-theoretic definition of function: a `forall ...
   exist!` theorem is turned into a callable function by `have fn ... as set`.

The checked slice here is the quotient set, defined as the set of left cosets.
Normality is still defined, but it is not needed for the existence and
uniqueness of this set. The next classical theorem would put the group
operation on the quotient and use normality to prove that multiplication of
cosets is well-defined.

```litex
# A classic quotient-set construction.
#
# This example builds a group as a parameterized struct, defines is_subgroup and
# is_normal_subgroup predicates, defines left cosets, and then turns a
# unique-existence theorem into a template-level quotient-set function.

prop GroupProperty(s set, inv fn(x s) s, op fn(x, y s) s, e s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(e, x) = x
        op(x, e) = x
    forall x s:
        op(x, inv(x)) = e
        op(inv(x), x) = e

struct Group<s set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        $GroupProperty(s, inv, op, e)

prop is_subgroup(s set, g &Group<s>, h power_set(s)):
    &Group<s>{g}.e $in h
    forall a, b h:
        &Group<s>{g}.op(a, b) $in h
    forall a h:
        &Group<s>{g}.inv(a) $in h

prop is_normal_subgroup(s set, g &Group<s>, h power_set(s)):
    $is_subgroup(s, g, h)
    forall x s, a h:
        &Group<s>{g}.op(&Group<s>{g}.op(x, a), &Group<s>{g}.inv(x)) $in h

# Normality is not needed to form the quotient set below. It is the condition
# needed later when defining the group operation on quotient classes.

prop is_left_coset_with_representative(s set, g &Group<s>, h power_set(s), x s, c power_set(s)):
    forall y s:
        =>:
            y $in c
        <=>:
            exist a h st {y = &Group<s>{g}.op(x, a)}

prop is_left_coset(s set, g &Group<s>, h power_set(s), c power_set(s)):
    exist x s st {$is_left_coset_with_representative(s, g, h, x, c)}

# This predicate is the graph of the quotient-set construction. The fourth
# argument `q` is intended to be exactly the set of all left cosets of `h`.
# In ordinary notation this is the underlying set often written as G/H.
prop is_group_quotient_set(s set, g &Group<s>, h power_set(s), q power_set(power_set(s))):
    q = {c power_set(s): $is_left_coset(s, g, h, c)}

# To introduce a real Litex function `group_quotient`, we first prove the
# set-theoretic function condition: for every input `(s, g, h)`, there exists a
# unique output `q`. Here the witness is the displayed set builder itself.
# Uniqueness is easy because any valid `q` must be equal to that same set.
claim:
    prove:
        forall s set, g &Group<s>, h power_set(s):
            exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}
    witness exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)} from {c power_set(s): $is_left_coset(s, g, h, c)}:
        $is_group_quotient_set(s, g, h, {c power_set(s): $is_left_coset(s, g, h, c)})

# `have fn ... as set` consumes the `forall ... exist!` theorem above. It is not
# saying the return type is just `set`; `as set` means "build the function from
# its set-theoretic graph." The actual return set is read from the witness type
# in the `exist!`, namely `power_set(power_set(s))`.
template group_quotient<s set>:
    have fn group_quotient as set:
        forall g &Group<s>, h power_set(s):
            exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}

# After the template, the function value is the unique witness promised by the
# graph predicate. This final check is the usable API: callers can write
# `\group_quotient<R>(g, h)` and immediately recover its defining property.
forall g &Group<R>, h power_set(R):
    $is_group_quotient_set(R, g, h, \group_quotient<R>(g, h))
```

## The Prompt

This example came from an ordinary GPT/Litex feedback loop: ask for the
mathematical shape, run the verifier, repair the next smallest issue, and keep
the checked result. A prompt like this is enough to get a strong first draft:

```text
In Litex, build a small quotient-set example for groups.
Define `Group<s set>` with `struct`, then define `is_subgroup` and
`is_normal_subgroup`. Define `is_left_coset_with_representative`,
`is_left_coset`, and `is_group_quotient_set` as the set of left cosets.

Prove, without `abstract_prop` or a `know` placeholder, that for every carrier
set `s`, group `g`, and subset `h power_set(s)`, there exists a unique
`q power_set(power_set(s))` satisfying `is_group_quotient_set`. Do not use
`is_normal_subgroup` as a prerequisite for this quotient-set existence theorem;
normality should be kept as the condition needed later for quotient-group
multiplication to be well-defined.

Then inside `template group_quotient<s set>:`, use
`have fn group_quotient as set:` to turn that unique-existence theorem into
the callable function `\group_quotient<s>(g, h)`.

Keep the file runnable.
```

The point is not that an AI draft should be trusted. The point is that the
Litex surface syntax is close enough to the mathematical plan that the draft is
easy to generate, while the verifier gives a concrete feedback loop for turning
the draft into checked code.
