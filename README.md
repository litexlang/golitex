<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: The Language Where Mathematics Verifies Itself

*by Jiachen Shen and The Litex Team, version 0.9.96-beta*

[![Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![litexpy](https://img.shields.io/badge/Litexpy-green?logo=python)](https://github.com/litexlang/litexpy)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Zulip](https://img.shields.io/badge/Zulip-blue?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)
[![Manual](https://img.shields.io/badge/Manual-orange?logo=book)](https://litexlang.com/doc/Manual)

**Beta notice:** Litex is experimental and not ready for mission-critical work.

</div>

## What is Litex?

_Truth is ever to be found in simplicity, and not in the multiplicity and confusion of things._

_– Isaac Newton_

Litex is an open-source formal mathematical language for writing checked mathematical proof code. The website is https://litexlang.com.
The basic loop is small:

1. Write the next mathematical fact.
2. Let Litex check it against the facts already in context.
3. Reuse the verified fact on later lines.

Here is a first proof:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

Read it as ordinary mathematics: for every real number `x`, if `x = 2`, then
`x + 1 = 3` and `x^2 = 4`. Litex checks the two conclusions by using the
assumption `x = 2`, routine rewriting, and arithmetic.

This is the central idea of Litex: **users write facts; Litex grows a verified
context**. A Litex file introduces objects, states facts about them, checks
which facts follow, stores the accepted ones, and makes them available to the
lines that come after.

Litex is not intended to replace any other proof assistant. It explores a
different path in formal mathematics: whether a readable, fact-oriented
interface can make it easier for AI systems and humans to translate
natural-language problems and textbook theorems into checkable formal proof
attempts. The goal is to make ordinary mathematical reasoning precise enough
for machine feedback while preserving the structure and appearance of
mathematical reasoning itself.

*We want Litex to become a first language for learning formalization: readable enough that even a curious ten-year-old can follow the core idea. Since a 10-year-old can verify his math homework, and a formal language is used for math verification, it is reasonable to expect that we can develop a formal language that is readable enough that even a curious ten-year-old can follow the core idea.*

Because Litex output supports multiple languages (简体中文, 繁體中文, 日本語,
English, 한국어, Español, Français, Deutsch, Português, Русский, العربية,
हिन्दी, Tiếng Việt, and Bahasa Indonesia), anyone from anywhere can pick up Litex quickly,
and gradually feel the appeal of mathematics and formalization.

On [Hacker news front page](https://news.ycombinator.com/item?id=45369629) in 2025.9

## The First Mental Model

_Mathematics is a game played according to certain simple rules with meaningless marks on papers._

_– David Hilbert_

Think of a Litex file as a small mathematical world that grows one checked fact
at a time. You introduce the objects in the world, give yourself vocabulary,
state the local assumptions of the problem, and then ask Litex whether a new
fact follows.

In implementation terms, that growing world lives in an `Environment`: the
physical container for the mathematical context. A Litex statement has two
jobs. First, Litex checks that the statement makes sense and verifies any fact
it asserts against the current world. Second, if the statement is accepted, its
effects are stored back into that world: new names, definitions, proved facts,
theorem interfaces, and routine inference/cache consequences that later lines
may reuse. This is why a file feels cumulative rather than merely textual.

A classical syllogism shows the shape:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

forall:
    forall x human:
        $mortal(x)
    =>:
        $mortal(Socrates)
```

This says: Socrates is human; if every human is mortal, then Socrates is
mortal. The general rule is kept inside the `forall` premise instead of being
injected into the global context.

The four moves are the basic Litex loop:

1. `have human nonempty_set, Socrates human` builds a tiny world.
2. `abstract_prop mortal(x)` adds a new word that can be used in facts.
3. The inner `forall x human: ...` states the local rule for this proof.
4. `$mortal(Socrates)` asks Litex to verify the particular conclusion.

The example is intentionally small, but it still keeps the assumption visible:
Litex checks that the conclusion follows from the local premise and the rest of
the context; it does not prove the premise from nothing.

When Litex accepts that final line, the verifier output can explain the route
it found. The exact JSON may include line numbers and more trace fields, but
the important shape is:

```text
{
  "result": "success",
  "type": "universal fact",
  "line": 4,
  "statement": "forall :\n    forall x human:\n        $mortal(x)\n =>:\n        $mortal(Socrates)",
  "conclusions": [
    {
      "statement": "$mortal(Socrates)",
      "verification": {
        "type": "cite forall fact",
        "cite_source": {
          "line": 5
        },
        "cited_statement": "forall x human:\n    $mortal(x)"
      }
    }
  ],
  "store_facts": [
    {
      "fact": "forall :\n    forall x human:\n        $mortal(x)\n=>:\n        $mortal(Socrates)",
      "reason": "proved statement"
    }
  ]
}
```

The useful part is not only that a line succeeds. The output tells you whether
the route was arithmetic, a known fact, a matching `forall`, or an inferred
consequence. That makes Litex a feedback loop: write the next fact, run the
checker, read what happened, and add the next piece of context.

Litex supports localized output in many languages.

```json
{
  "结果": "成功",
  "类型": "全称事实",
  "行": 4,
  "语句": "forall :\n    forall x human:\n        $mortal(x)\n    =>:\n        $mortal(Socrates)",
  "结论": [
    {
      "语句": "$mortal(Socrates)",
      "验证": {
        "类型": "引用 forall 事实",
        "引用来源": {
          "行": 5
        },
        "被引用语句": "forall x human:\n    $mortal(x)"
      }
    }
  ],
  "存储事实": [
    {
      "事实": "forall :\n    forall x human:\n        $mortal(x)\n=>:\n        $mortal(Socrates)",
      "原因": "已证明语句"
    }
  ]
}

```

For most factual statements, the proof route is reported under `verification`.
More structured facts can include a `steps` array inside that object. A
successful `forall` fact instead reports `conclusions`, where
each conclusion carries its own `verification`; detail output additionally
expands the local `parameters` and `assumptions`. Non-factual statements such
as definitions, `claim`, `thm`, and `by cases` report their context changes
under `effects`; detail output can expand their local `inside_results`.

Every factual statement has exactly one of three outcomes: **true**,
**unknown**, or **error**. `true` means Litex found a proof path relative to the
current context, such as a builtin rule, a checked fact, or an explicitly
stated local assumption. `unknown` means the statement is meaningful, but Litex
did not find enough verified or assumed information to prove it. `error` means
the line cannot be checked as a valid fact, often because the syntax is wrong or
some object is not well-defined, such as an undeclared name, a function argument
outside its domain, or `1 / 0`.

## How is Litex Different

_A mathematician, like a painter or poet, is a maker of patterns. If his patterns are more permanent than theirs, it is because they are made with ideas._

_– G. H. Hardy_

Litex supports two complementary ways to verify a fact.

*The Litex-native route is pattern matching against the verified context.* Instead
of naming and citing the theorem, you can leave the universal fact in context
and write the conclusion directly:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

forall:
    forall x human:
        $mortal(x)
    =>:
        $mortal(Socrates)
```

Here Litex matches `$mortal(Socrates)` against the known `forall`, checks that
`Socrates human` is already in context, substitutes `x` with `Socrates`, and
verifies the conclusion. This is the core difference in proof style: Litex can
use named theorem calls when names make the proof clearer, but it also lets
ordinary factual lines drive verification by their mathematical shape.


The explicit route is `by thm`: give a theorem a name, remember that name, and
cite it with the required arguments. This is closer to the named-theorem style
used by Lean and other formal proof systems.

```litex
thm add_one_after_two:
    prove:
        forall x R:
            x = 2
            =>:
                x + 1 = 3
    x + 1 = 2 + 1 = 3

by thm add_one_after_two(2)
2 + 1 = 3
```

## A Quick Gallery

The examples above are deliberately tiny. The samples below give a fast visual
sense of the larger Litex surface. They are excerpts, not full runnable files;
the linked pages contain runnable examples and fuller context.

The infinite-primes case study ends with the usual Euclid move: take a prime
divisor of `1 * 2 * ... * a + 1`, split on whether it is already below `a`,
derive the modular contradiction, and return the larger prime as a witness.

<!-- litex:skip-test -->
```text
claim forall! a N_pos: 2 <= a => {exist k N_pos st {k > a, $prime(k)}}:
    2 <= a <= product(1, a, '(x N_pos) N_pos {x}) <= product(1, a, '(x N_pos) N_pos {x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, '(x N_pos) N_pos {x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, '(x N_pos) N_pos {x}) % k = 0
            (product(1, a, '(x N_pos) N_pos {x}) + 1) % k = (product(1, a, '(x N_pos) N_pos {x}) % k + 1 % k) % k = 1
            impossible (product(1, a, '(x N_pos) N_pos {x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

Mathematical structures can be defined directly, with operations and axioms
kept close to the ordinary textbook shape:

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
```

Templates let users make reusable mathematical interfaces for parameterized
families of sets. Ordinary tuple products can be written with `cart(A, B, C)`;
the example below uses the same Cartesian idea in a constrained function-space
presentation. For any three sets `A`, `B`, and `C`, it names the set of
three-indexed functions whose first component lies in `A`, second in `B`, and
third in `C`, then recovers those component membership facts from the
definition. The point is not that this one object is special, but that templates
are useful for "for any sets of this shape" interfaces, which appear throughout
mathematics.

```litex
template<A, B, C set>:
    have cart3 set = {f fn(i N_pos: i <= 3) union(A, union(B, C)): f(1) $in A and f(2) $in B and f(3) $in C}

forall g \cart3<R, Q, Z>:
    g(1) $in R
    g(2) $in Q
    g(3) $in Z
```

`by contra`, `by cases`, `by for`, `by induc`, `by extension`, `by zorn_lemma` are builtin statements that prove by contradiction, cases, for, induction, extension and Zorn's lemma respectively. Here `by contra` proves that the square function is not surjective by finding a counterexample.

```litex
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn square(x R) R = x^2
forall x R:
    square(x) = x^2

by contra not $surjective_fn(R, R, square):
    have by exist x R st {-1 = square(x)}: x
    0 <= x^2
    -1 = square(x) = x^2
    0 <= -1
    impossible 0 <= -1
```

Visit online textbook for more examples: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Introduction .

## Goals of Litex

_We are not trying to meet some abstract production quota of definitions, theorems and proofs. The measure of success of our success is whether what we do enables people to understand and think more clearly and effectively about math._

_- William Thurston_

Litex is experimental, but it is aiming at three simple things:

1. **Human-in-the-Loop AI for Mathematical Exploration** As AI makes mathematical generation abundant, Litex helps turn fragmented reasoning into scalable, verifiable, and reusable mathematical knowledge, scale users' ability to use AI for mathematical exploration.
2. **Support scientific discovery.** Provide an accessible, scalable framework that enables both experts and non-experts to verify, refine, and reuse mathematical reasoning across science, engineering, and AI.
3. **A formal mathematical language that inspires everyone.** Formal math should
be a usable, readable medium for learning, communication, and research, close
enough to everyday math that students, mathematicians, AI agents, and curious
readers can benefit from rigor without losing sight of the ideas.

This educational goal matters for dependencies. A student learning calculus
does not first memorize a huge theorem dictionary and then cite a synonym of
the theorem in the book. They build definitions, lemmas, and proof habits in
order. Litex's builtins provide the basic mathematical ground so that this
kind of step-by-step development can start early, while larger imports and
`proof_debt` assumptions should remain visible background, not a way to erase the
book's proof. The code should be where the mathematical work happens, not only
a bibliographic reference into a theorem database.

This route comes with a clear audit obligation. A Litex result should be read
relative to its trusted background: builtin rules, inference rules,
standard-library facts, and any explicit `proof_debt` assumption injections. The
project goal is not to hide that boundary; it is to make the boundary visible
while keeping the user-facing proof script close to ordinary mathematical
writing.

For a textual walkthrough of the implementation pipeline, see
[Architecture](https://litexlang.com/doc/Architecture). The diagram below gives
the broader component landscape:

<div align="center">
  <img src="assets/verifier_flow.png" alt="Litex kernel" width="1000">
  <p><em>Litex kernel: the core components and their relationships.</em></p>
</div>

## Starting Points

Litex keeps the public documentation small:

1. [Setup: Download Litex](https://litexlang.com/doc/Setup): install Litex,
   run files, and understand CLI output.
2. [Manual](https://litexlang.com/doc/Manual): the source of truth for syntax,
   statements, proof flow, builtin rules, and inference.
3. [FAQ](https://litexlang.com/doc/FAQ): design rationale, trust boundaries,
   comparison notes, and old overview material in condensed form.
4. [Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean): dedicated
   comparison with Lean's interface and ecosystem.
5. [Hugging Face: Litex code examples and datasets](https://huggingface.co/litexlang)

Contact us:

1. [Email](mailto:litexlang@outlook.com)
2. [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)

## Special Thanks

_未来没有计划，但一定更好。_

_- 樊振东在巴黎奥运会后接受采访时说_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Litex is an attempt to make mathematics more accessible to everyone. It is
trying to solve a problem so basic that it is easy to miss. Elementary school
students can check each other's math homework because, even with very little
mathematical knowledge, they already understand the shape of mathematical
reasoning: new facts should follow from old facts by inspectable steps. Formal
languages are supposed to make that kind of checking precise, but there is
still no formal language for mathematics that ordinary students, scientists,
AI agents, and curious readers can all read naturally. Many people do not see
this as an unsolved problem; some assume it is impossible. Litex is built
around the opposite hope: that we can have a reasoning language rigorous enough
for machines to verify and readable enough for people to share. Even if today’s AI systems can already handle many mathematical
problems and write other formal languages for specific tasks, Litex’s
defining feature will always remain special: users can genuinely read
and understand it.

Hi, I’m Jiachen Shen, creator of Litex. I am deeply grateful to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong for their support and advice. I am sure this list will keep growing.
