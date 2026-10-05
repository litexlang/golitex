<div align="center">
  <img src="./assets/logo.PNG" alt="The Litex logo" width="300">

# Litex

### Write mathematics. See why it holds.

Created and maintained by Jiachen Shen.

Litex is designed as an everyday formal language for everyone who wants to
write and understand checkable mathematics.

Write the next mathematical fact directly; Litex checks it and shows the
grounds it found or where checking stopped.

_“Language is an instrument of human reason, and not merely a medium for the expression of thought.”_

_— George Boole, The Laws of Thought (1854), Chapter II (excerpt)_

[Try Litex online](https://litexlang.com) ·
[Read the Blueprint](docs/Litex_Blueprint.md) ·
[阅读中文蓝图](docs/Litex中文蓝图.md)
</div>

## Write a fact and see what it leaves behind

```litex
1 + 1 = 2
have a R = 2
a + 1 = 3
```

The first line is checked by calculation. The second introduces `a` as a real
number: Litex records `a $in R` and `a = 2`. It then checks `a + 1 = 3` using
the available facts and stores that equality for later steps. The author
chooses what to establish; Litex searches for supported local grounds and
reports the method it found.

Definitions join the same flow:

```litex
prop is_odd(x Z):
    x % 2 = 1

$is_odd(3)
```

Litex checks the concrete claim through the definition and keeps
`$is_odd(3)` in the current context. These are small examples of the
fact-oriented interface, not a claim that the verifier can invent an entire
proof from its final statement.

**Multilingual feedback.** The CLI can present JSON verification feedback in
several languages. The same source can be checked with `-lang zh` for Chinese
explanations or `-lang fr` for French ones. Thanks in part to AI-assisted
translation, this multilingual explanatory copy became feasible; the language
setting changes the feedback, not the mathematical statement being checked.
See the [CLI language options](docs/cli.md#basic-shape).

## Start from familiar mathematical objects

Litex aims for a Python-like entry into formal mathematics, where more people
can learn to build checkable knowledge.

Litex takes set theory (ZFC) as its mathematical foundation and presents sets,
elements, functions, and relations as the working vocabulary. In
`have a R = 2`, membership and equality are facts the language can use again;
the author does not first choose an abstract carrier type for `a`. Function
domains, set membership, and other well-definedness conditions still have to
be checked before a statement is accepted.

```litex
have S set = {x R: x > 0}
have fn square(x R) R = x^2
square(2) = 4

prop is_less(x, y R):
    x < y

$is_less(2, 4)
```

**Symbolic input.** Litex also accepts familiar mathematical symbols as input:
`s ∩ u ⊆ t ∩ u` is the symbolic spelling of
`intersect(s, u) $subset intersect(t, u)`.
Most examples use the letter-based spelling because it is easier to type on
an ordinary keyboard. See the [supported Unicode aliases](docs/Manual.md#unicode-mathematical-input-aliases-preview).

Lean elaborates proofs into a core dependent type theory; its compiler IR for
executable programs is a separate path. Litex makes set membership and facts
the default authoring layer. Lean can express set theory too; this compares
their default interfaces, not their current coverage.

The concise surface has an implementation cost. Arithmetic, set construction,
function application, quantifiers, and proof steps need to work together; each
combination must have clear premises, verification grounds, stored results, and
failure feedback. The [Blueprint's design discussion](docs/Litex_Blueprint.md#design-difficulty)
explains this tradeoff in detail.

## Let checked knowledge grow

_“If I have seen further it is by standing on the shoulders of Giants.”_

_— Isaac Newton, letter to Robert Hooke (1676)_

Every accepted statement extends the mathematical context for the statements
that follow.

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

The [checked Cantor example](docs/Litex_Blueprint.md#overview-spine) in the
Blueprint goes further: it defines a diagonal subset, proves a general theorem
without `trust`, then applies it to a `singleton` function to obtain
`missing != singleton(0)`.

## Work with people and AI through feedback

A person chooses the question, constructions, and mathematical meaning. AI can
propose or revise a small source fragment. Litex checks that fragment and
returns structured grounds or a stopping point; accepted steps become the
background for the next attempt. Failed statements do not enter the accepted
context. An external writing tool can save attempts and feedback for later
review—the language does not automatically archive the full collaboration.

First attempt (rejected):

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(0) = 0
```

Revised attempt (accepted):

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

## Independent Lean rechecking is a goal

Litex currently checks supported source with its own verifier. The current
build has **no Litex-to-Lean compiler entrypoint**; `lean/` retains earlier
experimental artifacts. A future handoff must preserve the mathematical
statement, produce a proof without holes, and pass Lean's kernel before it can
serve as independent rechecking or connect to Mathlib. See the
[Blueprint's Lean section](docs/Litex_Blueprint.md#compatibility).

<table>
<thead><tr><th>Litex</th><th>Lean (handwritten)</th></tr></thead>
<tbody>
<tr>
<td valign="top"><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td valign="top"><pre><code>import Mathlib
example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩</code></pre></td>
</tr>
</tbody>
</table>

Litex is an experimental beta project. Its builtin and inference rules, and
any user-written `trust` or `axiom`, are part of the present trust boundary. A successful
Litex check should be read with that scope in mind; the
[Manual's trust and strict-mode section](docs/Manual.md#trust-and-strict-mode)
explains how assumptions are handled. `-strict` rejects executed user `trust`,
`trust have`, and `axiom`, including imported dependencies; abstract predicate
signatures and named foundation releases remain allowed.

## Try Litex

Run it in the [online playground](https://litexlang.com), or install it on
macOS or Linux with Homebrew:

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
litex -lang zh -e '1 + 1 = 2'
litex -e '∅ ∩ ℕ ⊆ ℕ'
```

For other platforms and checkout builds, use the [setup guide](docs/setup.md).
The [CLI reference](docs/cli.md) explains commands and verification output;
the [Manual](docs/Manual.md) and [examples](examples/README.md) are starting
points for writing more Litex. The full argument and further source examples
are in the [Blueprint](docs/Litex_Blueprint.md) and
[中文蓝图](docs/Litex中文蓝图.md).

## About

_“The best way to predict the future is to invent it.”_

_— Alan Kay, “The Early History of Smalltalk” (1993)_

Jiachen Shen (沈嘉辰) is a mathematics PhD student at Fudan University. Lean
showed him that mathematics and programming can meet in a real language;
Litex explores whether formal source can follow more closely the way people
construct mathematical arguments.

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu,
Sheng Xu, Keyao Zhu, and Zhaoxuan Hong for their support and advice.

Litex is released under the [Apache License 2.0](LICENSE).
