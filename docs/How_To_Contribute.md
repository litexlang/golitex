# How to Contribute to Litex

Jiachen Shen and The Litex Team, 2026-06-02. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/How_To_Contribute.md

Litex is experimental. The most helpful contributions right now are simple:

1. Tell us where the documentation is confusing.
2. Help improve the dataset and textbook translation work.

You do not need to know the Rust kernel to help.

## 1. Tell Us Where the Docs Are Bad

Fresh-reader feedback is very useful. Read a small part of the README, Manual,
Mechanics notes, examples, or website docs, then report exactly where you got
confused.

A good report says:

- which page or example you read;
- the first sentence, concept, or code block that was unclear;
- what you expected it to mean;
- what output, error message, or explanation was confusing;
- what would have made the page easier to follow.

Small reports are enough. One clear confusion point is more useful than a broad
comment like "the docs are hard to read."

## 2. Work on Datasets or Textbooks

The datasets and textbooks Litex wants to explore are tracked here:

https://github.com/litexlang/datasets_and_textbooks

This work has two main directions:

- **Horizontal work: datasets.** Improve or expand problem datasets such as
  MATH500, miniF2F-style problems, high-school math, contests, and exams.
- **Vertical work: textbooks.** Translate a mathematical book or chapter in
  order, preserving the source structure and recording what Litex can or cannot
  express yet.

#### Turn Scaffolding Into Checked Proofs

The goal is not only to make files run. Many current files intentionally use
`know` or `abstract_prop` as temporary scaffolding so that a larger translation
can stay runnable while the missing mathematics remains visible. A useful
contribution is to make that scaffolding smaller, more precise, or unnecessary.

Good dataset/textbook work usually looks like one of these:

- prove an existing `know` directly and remove it;
- find several similar `know` facts and replace them with one reusable theorem,
  definition, or standard-library interface;
- split one broad `know` into a real proof outline, with only the one remaining
  hard sub-step still marked by `know`;
- replace an `abstract_prop` with a concrete `prop` when the intended meaning
  is now clear enough to define;
- record why a proof is blocked, including the smallest useful statement that
  still fails;
- add source or license notes when the original text cannot be redistributed.

A practical workflow is:

1. Make one to three quick passes over a batch and solve the easy items first.
   These are often arithmetic cleanups, missing intermediate equalities,
   obvious witnesses, or small theorem calls.
2. When an item stays stuck after several passes, stop trying random formal
   rewrites. Read the math and write the proof in natural language first.
3. Break that proof into small Litex-shaped steps: definitions to unfold,
   intermediate equalities, estimates, cases, witnesses, and local lemmas.
4. Formalize those steps one by one. If a step still cannot be proved, put the
   `know` on that narrow step, not on the whole theorem.
5. Keep the item status honest: `checkable` only after the relevant Litex code
   verifies; `translated` when the statement is natural but unfinished;
   `blocked` when the remaining obstacle is understood and recorded.

Here is a more realistic example of the workflow. Suppose the source problem
is Euclid's theorem in bounded form:

> For every positive integer `a >= 2`, there is a prime number `k > a`.

A first translation might keep the file runnable by assuming exactly the
conclusion it still needs:

```text
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

claim:
    prove:
        forall a N_pos:
            2 <= a
            =>:
                exist k N_pos st {k > a, $prime(k)}
    have k N_pos
    know k > a
    know $prime(k)
    witness exist k N_pos st {k > a, $prime(k)} from k
```

That version is only a placeholder. The natural-language proof has real
structure:

1. Let `P = 1 * 2 * ... * a` and consider `P + 1`.
2. Use a general theorem that every natural number `n >= 2` has a prime
   divisor.
3. Let `k` be a prime divisor of `P + 1`.
4. If `k <= a`, then `k` divides the product `P`, so `P % k = 0`.
5. Since `k` also divides `P + 1`, we get `(P + 1) % k = 0`; but from
   `P % k = 0`, the same remainder is `1`, a contradiction.
6. Therefore `k > a`, and this prime `k` is the witness.

After writing this outline, split the broad assumption into reusable subgoals
and check the standard library before proving them locally. Here one subgoal is
already a standard-library theorem: `Nat::exists_prime_and_dvd`. In a real file,
you would import `Nat` and use the std theorem, adapting from std's
`$Nat::Prime` / `$Nat::Dvd` interface to the local statement shape if needed.
The product-divisibility step is also a reusable theorem candidate: it can be
proved locally by induction or by splitting the finite product at `k`, but if it
appears in several problems it should be promoted into std instead of copied
every time.

```text
# First reusable fact: use std instead of reproving prime divisors.
import Nat

claim:
    prove:
        forall n N_pos:
            2 <= n
            =>:
                exist k N_pos st {$prime(k), n % k = 0}
    # In the final proof, cite `Nat::exists_prime_and_dvd(n)` and bridge the
    # std facts `$Nat::Prime(k)` and `$Nat::Dvd(k, n)` to this local surface.
    by thm Nat::exists_prime_and_dvd(n)
    # bridge the std witness to the local `$prime(k), n % k = 0` shape here

# Second reusable fact: prove once, then consider moving it into std.
claim:
    prove:
        forall a, k N_pos:
            k <= a
            =>:
                product(1, a, 'N_pos(x){x}) % k = 0
    know:
        forall a, k N_pos:
            k <= a
            =>:
                product(1, a, 'N_pos(x){x}) % k = 0

# The Euclid step now has no broad know.
claim:
    prove:
        forall a N_pos:
            2 <= a
            =>:
                exist k N_pos st {k > a, $prime(k)}
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

That is already a much better contribution. The remaining work is not "prove
infinite primes" as one opaque task; it is a small list of named mathematical
interfaces. In the checked case study, the product-divisibility fact is proved
by splitting the product at `k`. Once the small interfaces are available, the
Euclid step above becomes a clean final proof. The full checked version is in
`examples/05_case_studies/README.md`.

#### Preserve the Mathematical Meaning

Be careful with semantic translation. A bad formalization can pass by proving
the wrong thing. Do not replace a problem with a tautology such as `1 = 1`, and
do not prove only one example when the source statement is quantified. For
example, if the problem says "for positive real `x`, prove `x = 2` from
`x^3 = 8`", proving only `2^3 = 8` misses the statement. The formalization
should keep the variable, hypothesis, and conclusion:

```text
forall x R_pos:
    x^3 = 8
    =>:
        3 = log(2, 8)
        log(2, 8) = log(2, x^3)
        log(2, x^3) = 3 * log(2, x)
        log(2, x) = 1
        x = 2^1 = 2
```

The exact proof route may change depending on the available library, but the
translation must preserve the mathematical content of the original problem.


### Enrich the Standard Library

Dataset and textbook work is one of the main ways Litex discovers what should
belong in the standard library.

The standard library has two jobs:

- record basic background interfaces, such as the relationships among builtin
  objects, predicates, arithmetic, order, membership, divisibility, primes, and
  finite products;
- store reusable theorems that are mathematically routine but too long to
  reprove inside every dataset item.

The second kind is often discovered only after doing real problems. A human may
look at a line like "every number at least two has a prime divisor" or "if
`k <= a`, then `k` divides `1 * ... * a`" and treat it as obvious background.
In a formal language, each of those facts may require induction, witnesses,
divisibility bookkeeping, or product-splitting. When the same proof debt appears
across many items, the right contribution is not to keep copying `know`; it is
to turn the pattern into a named std theorem, prove it once, and replace local
uses with a theorem call.


For each translated item, record the math idea before the Litex code:

```yaml
source:
problem:
proof_idea:
litex_code:
comments:
```

Use `comments` for verifier commands, proof-attempt notes, blockers, license
caveats, and follow-up work. Add extra fields such as `id`, `topic`, `status`,
or `blocker` only when a local dataset dashboard needs them.

## What to Avoid at First

Please do not start by changing the verifier, parser, builtin rules, or
soundness-critical logic unless you already understand that part of the code.
For new contributors, documentation feedback and dataset/textbook work are much
better first contributions.

## Help Make Litex Easier to Understand

Another useful contribution is to make the project easier for outsiders to
understand. Good documentation, demos, and reports should answer questions like:

- What can Litex already run?
- How is Litex different from Lean or ordinary LLM problem solving?
- What is the strongest current demo?
- Which mathematical examples are already `checkable`?
- Which parts are `blocked`, and what do those blockers teach us?
- How can another person get involved?

If you improve a README section, demo note, benchmark page, or contribution
guide so that one of these questions becomes clearer, that is a useful
contribution.
