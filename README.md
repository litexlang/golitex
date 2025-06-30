<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**Release v0.1.1-beta (not yet ready for production use)**  
*May 2025*  
*Created by Jack Shen*

[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Website](https://img.shields.io/badge/Website-blue?logo=website)](https://litexlang.org)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Online Playground](https://img.shields.io/badge/Online%20Playground-darkgreen?logo=playground)](https://litexlang.org/playground)

</div>

## Litex: the simplest formal language

_Mathematics is the language with which God wrote the universe._

_-- Galileo Galilei_

_The best way to predict the future is to invent it._

_-- Alan Kay_

Litex is a simple and easy-to-learn formal language. It makes formal reasoning as natural as writing in natural language. Thanks to its innovative design, even 10-year-olds can learn Litex easily. In the foreseeable future, Litex is going to reduce the time ratio between formalizing a proof and writing it in natural language from 10:1 to 1:1.

The key insight of Litex is: mathematical verification is nothing but a kind of **match and substitution** problem, similar to "ctrl+f (or cmd+f)" in your browser. When doing verification, you find an established fact, match it with the new statement, substitute the variables in the established fact with the new statement, and check if the new statement is equal to the substituted established fact. If they are equal, the new statement is verified. Read [this example](#a-simple-example) and [this section](#verification-is-pattern-matching-and-so-is-litex) for more details.

Traditional formal languages like Lean, Coq, [are fundamentally different from Litex](#examples-litex-for-curious-formal-language-users), because they are still programming languages, just like Python and C. There are huge gaps between programming and verification. Serving both purpose of computation and verification is technically challenging, which makes them much more complex than Litex. The following table might give you a sense of the gap.

| Feature              | Mathematics                                                                 | Programming                                                                    |
|----------------------|------------------------------------------------------------------------------|--------------------------------------------------------------------------------|
| **Variable**          | No real "variable" — once an object is defined, its meaning is fixed        | Variables can change values during execution                                   |
| **Function**          | A symbol that builds new expressions from input symbols (no execution)      | A block of executable code that performs computation or side effects           |
| **Execution**         | No execution — everything is symbolic manipulation or `match and substitution`           | Involves actual computation steps and runtime behavior                         |
| **Control Flow**      | Uses logical constructs like `∀` (for all) to reason about all cases         | Uses constructs like `for`, `while`, `if` to control the flow of execution     |
| **Iteration**         | Infinite or large domains handled abstractly (e.g. by induction or logic)    | Requires explicit loops and step-by-step computation                           |
| **Existential Quantification** |  Existential quantification is a fundamental part of math | No existential quantification — all objects are explicitly defined |
| **Purpose**           | To prove or verify truth symbolically                                        | To perform tasks, process data, interact with systems                          |

Litex, as a domain language, takes advantage of the difference between programming and verification, and is designed to be a simple and intuitive reasoning verifier. Math serves two purposes: 1. for computation, i.e. calculate the output of a function given the input, and 2. for verification, i.e. make sure a new statement is correct given the established ones. Computation is how math is used to solve real-world problems. Verification is how math, the old language of the universe, enriches itself by making sure the new statements are correct. The software industry has already revolutionized how we compute, and Litex is here to change how we verify.

This README shows how the deep understanding of both the nature of mathematics and the nature of programming shapes the unique design of Litex. Let's start with a simple example.

---

- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
- **Litex Zulip Community:** [Litex Zulip Community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
- **Litex Design(Under Development):** [Litex Design](./doc/design/design.md)
- **Litex Playground:** [Litex Playground](https://litexlang.org/playground)
- **Litex Tutorial:** [Litex Tutorial](./doc/tutorial/tutorial.md)
- **Litex Applications of Formal Reasoning:** [Litex Applications of Formal Reasoning](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md)
- **Litex License:** [Litex License](./LICENSE)
- **Litex Contributing:** [Litex Contributing](./CONTRIBUTING.md)

## A Simple Example

_If you define the problem correctly, you almost have the solution._

_-- Steve Jobs_

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle, which formalizes deductive reasoning as follows. Run this example on [playground](https://litexlang.org/playground):

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>obj human set</code> <br><br>
      <code>prop intelligent(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$intelligent(x)</code> <br> <br>
      <code>obj Jordan human</code> <br> <br>
      <code>$intelligent(Jordan)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def intelligent (x : Human) : Prop := true</code> <br><br>
      <code>axiom intelligent_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), intelligent x</code> <br><br>
      <code>example (Jordan : Human) : intelligent Jordan := intelligent_all Jordan</code>
    </td>
  </tr>
</table>

The above example means: `Human` is the set of all humans. Using `know`, we establish a simple fact: all humans are intelligent. When the user input `intelligent(Jordan)`, the system will automatically find the fact `forall x Human: $intelligent(x)` and substitute `x` with `Jordan`, and then check if the result is true. This process is called `match and substitution`. Since Jordan is in the set of `Human`, "Jordan is intelligent" is true.

Each statement in Litex has four potential outcomes: true, false, unknown, or error. All factual statements start with `$` to differentiate them from functions.

Keep this example in mind. This is the most classic example of how people uses `match and substitution` to establish new facts. Refer to this example when you are reading the next section.

## Verification is pattern matching, and so is Litex.

_Common sense is not so common._

_-- Voltaire_

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Math is about deriving new facts from established ones. Verification is about making sure the new facts are true based on the established ones. There are and only are two ways of verifying a new fact:

1. From special case to special case. e.g. `a = 1` => `a = 1`. The derived fact `a = 1` (the second statement) is true because the first statement is true and the first statement is written exactly the same as the second statement. I call it `match`.

2. From general case to special case. e.g. `forall x Human: $intelligent(x)` => `$intelligent(Jordan)`. The derived fact `intelligent(Jordan)` is true because by substituting `x` with `Jordan`, the first statement is true, and the second statement is written exactly the same as the first statement after substitution. I call it `match and substitution`.

You just learned how Litex builds math from basic pieces, like building blocks. To sum up, `match and substitution` is the basic way of deriving new facts from established ones. Such method is called first-order logic. We can construct the whole math system by this way in Lite as long as basic arithmetic and counting are built-in. [^1][^2][^3]

[^1]: There are exceptions. Facts about symbols with literal information (e.g. numbers like 1, 2, 3, counting etc) are not verified in this way. Facts related to counting are not verified in this way. There are and only these two exceptions. Those facts are verified by Litex's builtin rules, the user does not need to worry about them.

[^2]: Voltaire once said: "Common sense is not so common." In the case of Litex, Litex makes the process of building math as easy as `ctrl+f/cmd+f` in your browser, by discovering that math is nothing but a special kind of `match and substitution` problem. Everyone is so familiar with this process, but almost no one actually finds its significance and use this idea to create a simple formal language. The real magic of Litex is that it works just like how people think in daily life. This is a hard magic for the language designer, because it requires a deep understanding of both the nature of mathematics and the nature of programming, but is worth the effort.

[^3]: In naive set theory, where almost all daily math is based on, all facts are derived by `match and substitution` using first-order logic, with only two exceptions: 1. mathematical induction. 2. the axiom of replacement. Those two are builtin in Litex.

## Litex Keywords

_Keep it simple, stupid._

_-- The Unix Philosophy_

Litex is a simple language. I hope many of the keywords are already familiar to you.[^3]

| Keyword | Meaning |
|---------|---------|
| `obj` | Define an object. Anything in Litex is an object. |
| `prop` | Define a proposition. A factual statement must has its proposition name and its proposition objects. |
| `know` | Establish a fact |
| `forall` | Universal quantification |
| `exist` | Existential quantification |
| `have` | Introduce an object using an existential quantification |
| `exist_prop` | Existential quantification with a proposition |
| `iff` | Equivalence |
| `then` | Implication |
| `or` | Disjunction |
| `not` | Negation |
| `fn` | Define a function |
| `fn_template` | Define a class of functions |
| `set` | set |
| `in` | membership of an object in a set |
| `dom` | domain of a proposition, function, function template, etc. |
| `enum` | enumeration |
| `len`  | length of a set |
| `finite_set` | a set with a finite number of elements |
| `indexable_set` | a set with a countable number of elements |
| `prove` | open a local environment to write some statements without affecting the global environment |
| `claim` | claim a factual statement, prove it here |
| `prove_by_contradiction` | prove by contradiction |
| `prove_in_each_case` | prove by case analysis |
| `prove_by_math_induction` | prove by mathematical induction |
| `prove_iteratively` | prove a universal statement by iterating over a finite et |
| `import` | import a file or directory |
| `import_globally` | import a file globally |

[^3]: Although these keywords are rarely defined strictly in math textbooks, they are used everyday and everywhere. The Litex creator tried his best to make the meaning of these keywords as close to the meaning in our daily math expression, along with his own ideas and understanding, so that Litex is both intuitive and strict.

##  Examples: Litex for Curious Formal Language Users

_Beautiful is better than ugly. Explicit is better than implicit. Simple is better than complex._

_-- The Zen of Python_

Here are some examples of Litex, in Litex for Curious Lean Users and other formal language users. Detailed explanations are provided in [Litex for Curious Lean Users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md). I put them here for you to get a sense of the language. Run these examples on [playground](https://litexlang.org/playground).

I will show you how Litex is shaped by common sense, and why common sense is not so common in traditional formal languages. It must be noted that making Litex so common sense is a very uncommon thing, because it requires a deep understanding of both the nature of mathematics and the nature of programming.

The definition of algorithm is a good example. In mathematics, an algorithm is a computational method that can be precisely defined as a quadruple (Q, I, S, f), where:
- Q is a set representing all possible states of computation
- I is a subset of Q representing valid inputs
- S is a subset of Q representing valid outputs
- f is a function from Q to Q that defines the computational rule

The computation proceeds by repeatedly applying f to an input x in I, generating a sequence x₀, x₁, x₂, ... where x₀ = x and xₖ₊₁ = f(xₖ). An algorithm must terminate in finitely many steps for any valid input, producing an output in S. This formal definition ensures that algorithms are well-defined mathematical objects that can be rigorously analyzed and verified.


<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>fn comp_seq(Q set, f fn(Q)Q) fn(Q, N)Q:</code><br>
      <code>&nbsp;&nbsp;forall x Q, n N:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(Q, f)(x,n+1) = f(comp_seq(Q, f)(x, n))</code><br><br>
      <code>exist_prop n N st exist_comp_seq_end(Q set, x Q, f fn(Q,N)Q):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;f(x, n) = f(x, n+1)</code><br><br>
      <code>prop is_algorithm(Q set, I set, f fn(Q)Q):</code><br>
      <code>&nbsp;&nbsp;forall x Q: # i.e. Q is subset of I</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;f(x) $in I</code><br>
      <code>&nbsp;&nbsp;iff:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall x I:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$exist_comp_seq_end(Q, x, comp_seq(Q, f))</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>structure ComputationalMethod where</code><br>
      <code>&nbsp;&nbsp;Q : Type</code><br>
      <code>&nbsp;&nbsp;I : Set Q</code><br>
      <code>&nbsp;&nbsp;S : Set Q</code><br>
      <code>&nbsp;&nbsp;f : Q → Q</code><br>
      <code>&nbsp;&nbsp;f_fixed : ∀ q ∈ S, f q = q</code><br><br>
      <code>namespace ComputationalMethod</code><br><br>
      <code>def comp_seq (cm : ComputationalMethod) (x : cm.Q) : ℕ → cm.Q</code><br>
      <code>&nbsp;&nbsp;| 0 => x</code><br>
      <code>&nbsp;&nbsp;| n + 1 => cm.f (comp_seq x n)</code><br><br>
      <code>def TerminatesIn (cm : ComputationalMethod) (x : cm.Q) (k : ℕ) : Prop :=</code><br>
      <code>&nbsp;&nbsp;comp_seq cm x k ∈ cm.S ∧</code><br>
      <code>&nbsp;&nbsp;∀ i < k, comp_seq cm x i ∉ cm.S</code><br><br>
      <code>def IsAlgorithm (cm : ComputationalMethod) : Prop :=</code><br>
      <code>&nbsp;&nbsp;∀ x ∈ cm.I, ∃ k, TerminatesIn cm x k</code><br><br>
      <code>end ComputationalMethod</code>
    </td>
  </tr>
</table>

Next I want to show you how Litex can be used to solve a simple linear equation. It's clear that the Litex version can be read and understood by a 10-year-old, while the Lean version is much more complex.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>obj x R, y R:</code><br>
      <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
      <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br><br>
      <code>2 * (2 * x + 3 * y) = 2 * 10</code><br>
      <code>4* x + 6 * y = 2 * 10</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = y</code><br>
      <code>y = 6</code><br>
      <code>2 * x + 3 * 6 = 10</code><br>
      <code>2 * x + 18 - 18 = 10 - 18</code><br>
      <code>2 * x + 18 - 18 = -8</code><br>
      <code>(2 * x) / 2 = -8 / 2</code><br>
      <code>(2 * x) / 2 = x</code><br>
      <code>x = -4</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example (x y : ℝ) (h₁ : 2 * x + 3 * y = 10) (h₂ : 4 * x + 5 * y = 14) : x = -4 ∧ y = 6 := by</code><br>
      <code>&nbsp;&nbsp;have h₃ : 2 * (2 * x + 3 * y) = 2 * 10 := by rw [h₁]</code><br>
      <code>&nbsp;&nbsp;have h₄ : 4 * x + 6 * y = 20 := by linear_combination 2 * h₁</code><br>
      <code>&nbsp;&nbsp;have h₅ : (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [h₄, h₂]</code><br>
      <code>&nbsp;&nbsp;have h₆ : (4 * x + 6 * y) - (4 * x + 5 * y) = y := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;have h₇ : 20 - 14 = 6 := by norm_num</code><br>
      <code>&nbsp;&nbsp;have h₈ : y = 6 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [←h₆, h₅, h₇]</code><br>
      <code>&nbsp;&nbsp;have h₉ : 2 * x + 3 * 6 = 10 := by rw [h₈, h₁]</code><br>
      <code>&nbsp;&nbsp;have h₁₀ : 2 * x + 18 = 10 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [mul_add] at h₉</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;simp at h₉</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;exact h₉</code><br>
      <code>&nbsp;&nbsp;have h₁₁ : 2 * x = -8 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linear_combination h₁₀ - 18</code><br>
      <code>&nbsp;&nbsp;have h₁₂ : x = -4 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linear_combination h₁₁ / 2</code><br>
      <code>&nbsp;&nbsp;exact ⟨h₁₂, h₈⟩</code>
    </td>
  </tr>
</table>

I know Lean can use tactics to solve the same problem, and it is shorter. Litex will introduce similar features in the future. What I really want to show you here is that Litex is much more readable and intuitive than Lean in this case. Not every situation can be solved by tactics, and writing tactics itself in Lean is not easy. Litex spares you from remembering all these difficult things like `have`, `by`, `rw`, `simp`, `exact` and strange syntax etc. All you need is basic math knowledge, which significantly reduces the barrier to entry.

## Contact & Contribute to Litex

_The people who are crazy enough to think they can change the world are the ones who do._

_-- Steve Jobs_

_What I cannot create, I do not understand._

_-- Richard Feynman_

Hi, I am Jiachen Shen (call me Jackie Shen), the creator of Litex. I am a PhD student in mathematics and programming language enthusiast (a programming language geek, if you are one too, you are welcome to contact me). In 2023, I shockingly found that math is somehow equivalent to programming, after reading Professor Terence Tao's [blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/). This is the most amazing idea that I have ever seen in my life. In 2024, after thinking about it for a year, I started to implement Litex. After more than 3000 git commits, what it means to be a "formal language that is intuitive and as aligned with daily math expression as possible" is finally to make sense to me and my kernel sort of works now.

As Arabic numbers transforms the world of math by its clean and concise expression, Litex aims to transform the world of math by its intuitive and natural expression using formal language. Giving semantics to keywords and syntax to Litex and at the same time making what it means as aligned with daily math expression as possible, is the major challenge of Litex. The creator of Litex is trying to make it happen, and that is almost done.

As formal languages are becoming more and more important [in the AI safety, AI reasoning, math collaboration](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md), I think it is time to make Litex more accessible to the public. Hope you enjoy Litex and feel free to contact [me](mailto:litexlang@outlook.com) or join the [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/) to discuss.