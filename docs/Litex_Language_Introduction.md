# Litex Language Introduction

This note is a first-contact introduction to the Litex language.  It is not a
syntax catalogue and not an implementation map.  Its goal is to give the reader
one coherent mental model before they meet reference words such as "object",
"fact", and "statement".

Litex is a language for growing a checked mathematical context.  A file is read
from top to bottom.  Each accepted line may introduce a name, define a word,
prove a fact, open a local proof block, or store information that later lines
can use.  The basic loop is simple:

1. Write the next mathematical fact.
2. Let Litex check whether it follows from the current context.
3. If it succeeds, reuse it later.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

This reads almost exactly like the mathematical sentence: for every real number
`x`, if `x = 2`, then `x + 1 = 3` and `x^2 = 4`.  Litex checks the conclusions
from the introduced object `x`, the local assumption `x = 2`, arithmetic, and
equality substitution.

## Objects, Expressions, And Facts

Mathematics talks about objects: numbers, sets, functions, tuples, expressions,
and named objects introduced earlier.  An expression such as `x + 1` is still
only an object-forming expression.  It becomes a fact only when a relation or
predicate makes a judgment about it:

```litex
2 + 2 = 4
1 $in {1, 2, 3}
not 4 $in {1, 2, 3}
```

In Litex, a fact is something the verifier can try to prove.  Equality, order,
membership, subsethood, and user-defined predicates are all fact-forming
relations.  This distinction is important because not every piece of code is a
fact.  A definition introduces vocabulary; a theorem declaration creates a
named interface; a proof block organizes local reasoning.  Only factual lines
are checked as true or not true relative to the current context.

## Introduced Objects

Ordinary mathematics often says "let `x` be a real number" or "for every
integer `n`".  Litex treats these names as introduced objects, not as variables
whose values keep changing.  Once introduced, the name denotes one fixed object
in the current context.  Its exact value may be unknown, but it is not moving.

```litex
forall n Z:
    n + 1 > n
```

Here `n` is arbitrary.  The proof must work for any integer the context gives
us.  Existential statements reverse the choice:

```litex
forall n Z:
    exist m Z st {m > n}
```

To prove an existential fact, we may provide a witness.  The witness may depend
on objects introduced by outer quantifiers:

```litex
thm every_integer_has_larger_integer_intro:
    ? forall n Z:
        exist m Z st {m > n}
    witness exist m Z st {m > n} from n + 1:
        n + 1 $in Z
        n < n + 1
```

This is why quantifier order matters.  `forall n: exist m:` means we may choose
`m` after seeing `n`.  `exist m: forall n:` would ask for one fixed integer
larger than every integer, which is impossible.

## Defining Vocabulary With `prop`

A `prop` defines a reusable mathematical predicate or relation.  It is how a
file teaches Litex a new word.

```litex
prop is_even(n Z):
    exist k Z st {n = 2 * k}

thm zero_is_even_intro:
    ? forall :
        $is_even(0)
    witness exist k Z st {0 = 2 * k} from 0:
        0 = 2 * 0
```

The dollar sign in `$is_even(0)` marks a call to a named predicate.  The
definition says what that predicate means.  The theorem then proves the
particular fact by giving the witness `k = 0`.

This is the main role of definitions in Litex: not to hide the mathematics, but
to give recurring mathematical shapes a name.

## Implication And Local Context

An implication is a conditional fact.  In Litex, assumptions appear before
`=>:` and conclusions after it.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
```

The conclusion is checked under the local assumption `x = 2`.  The implication
does not assert that every real number equals `2`; it says what follows if that
assumption is available.

Local context is one of the most important ideas in Litex.  Facts introduced
inside a `forall`, `claim`, `by cases`, or `by contra` block are available
where that block says they are available.  They do not automatically become
global facts unless the statement form stores them.

## Proof By Contradiction

To prove a negative statement, it is often natural to assume the opposite and
derive an impossible fact.  Litex writes this with `by contra`.

```litex
prop is_largest_integer(M Z):
    forall n Z:
        n <= M

thm no_largest_integer_intro:
    ? forall :
        not exist M Z st {$is_largest_integer(M)}
    by contra:
        ? not exist M Z st {$is_largest_integer(M)}
        have by exist M Z st {$is_largest_integer(M)}: M
        M + 1 $in Z
        M + 1 <= M
        M < M + 1
        impossible M + 1 <= M
```

The temporary contradiction assumption gives us a supposed largest integer
`M`.  The definition then implies `M + 1 <= M`, while arithmetic gives
`M < M + 1`.  The final line tells Litex which fact is impossible in the
current context.

## Equality And Substitution

Equality is built into Litex.  Reflexivity, symmetry, transitivity, and
substitution through expressions are ordinary checker behavior:

```litex
thm equality_substitution_intro:
    ? forall x, y, z R:
        x = y
        =>:
            2 * x = 2 * y
            x + z = y + z
    2 * x = 2 * y
    x + z = y + z
```

Substitution also works through functions:

```litex
thm function_substitution_intro:
    ? forall f fn(t R) R, x, y R:
        x = y
        =>:
            f(x) = f(y)
    f(x) = f(y)
```

Litex's equality is ordinary equality for the objects under discussion.  If a
topic uses another equivalence relation, such as equality modulo `10`, define
that relation explicitly:

```litex
prop has_same_remainder_mod_10(a, b Z):
    a % 10 = b % 10

thm twelve_and_two_mod_10_intro:
    ? forall :
        $has_same_remainder_mod_10(12, 2)
    12 % 10 = 2
    2 % 10 = 2
    12 % 10 = 2 % 10
```

This keeps the language honest: `12 = 2` is false as an integer fact, but
`12` and `2` have the same remainder modulo `10`.

## Statements Are Actions On Context

The words `object`, `fact`, and `statement` are easy to confuse:

- An **object** is a mathematical thing or expression.
- A **fact** is a judgment about objects.
- A **statement** is a line or block of Litex code that does something.

Some statements assert facts:

```litex
2 + 2 = 4
```

Some statements introduce objects:

```litex
have x R = 2
```

Some statements define vocabulary:

```litex
prop is_positive_real(x R):
    x > 0
```

Some statements package reusable facts:

```litex
thm positive_real_is_nonzero_intro:
    ? forall x R:
        x > 0
        =>:
            x != 0
    x != 0
```

This is why an implementation cheat sheet talks about "statement execution":
each statement is checked, then it may change the mathematical context.

## Well-Definedness Comes Before Proof

Before Litex can prove a fact, it must first check that the objects in the fact
make sense.  For example, `1 / x` requires evidence that `x != 0`, and `f(a)`
requires evidence that `a` is in the domain of `f`.

```litex
forall x R:
    x != 0
    =>:
        x / x = 1
```

If a fact fails because an object is not well-defined, the next step is usually
not to search for a theorem.  The next step is to add the missing domain fact.

## What To Read Next

Read this note before using the implementation cheat sheet.  Then use:

- `docs/Manual.md` for the durable language reference.
- `examples/01_proof_patterns.md` for proof patterns.
- `examples/02_builtin_math.md` for built-in arithmetic, set, function, and
  object behavior.
- `docs/cheatsheet.md` when you want an executor-level map of statement forms,
  fact forms, and environment effects.

The cheat sheet is intentionally dense.  It is a map of the current
implementation, not the first explanation of the language.
