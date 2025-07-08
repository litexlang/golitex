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

_Common sense is not so common._

_-- Voltaire_

Litex is a simple and easy-to-learn formal language. It makes formal reasoning as natural as writing in natural language. Thanks to its innovative design, even 10-year-olds can learn Litex easily. In the foreseeable future, Litex is going to reduce the time ratio between formalizing a proof and writing it in natural language from 10:1 to 1:1.

The key insight of Litex is: mathematical verification is nothing but a kind of **match and substitution** problem, similar to "ctrl+f (or cmd+f)" in your browser. When doing verification, you find an established fact, match it with the new statement, substitute the variables in the established fact with the new statement, and check if the new statement is equal to the substituted established fact. If they are equal, the new statement is verified. Read [this example](#a-simple-example) and [this section](#verification-is-pattern-matching-and-so-is-litex) for more details. Try Litex on [playground](https://litexlang.org/playground).

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

Litex, as a domain language, takes advantage of the difference between programming and verification, and is designed to be a simple and intuitive reasoning verifier. Technically, Litex is a "Read-Only Turing Machine". It does not have variables, execution, control flow, iteration, etc. Traditional formal languages sort of robbed you of the joy of exploring mathematics by forcing you to spend most of your time wrestling with the formal language itself. Litex brings that joy back! [^1]

Math serves two purposes: 1. for computation, i.e. calculate the output of a function given the input, and 2. for reasoning and verification, i.e. make sure a new statement is correct given the established ones. Math is the language of the universe and since the beginning of history we human beings have been using math to know how things work to do real-life problems. The software industry has already revolutionized how we compute, and Litex is here to change how we reason.

This README shows how the deep understanding of both the nature of mathematics and the nature of programming shapes the unique design of Litex. Let's start with a simple example.

[^1]: Focusing on and only on verification makes Litex much easier to use than traditional formal languages. For example, Litex kernel searches the established fact for you, so you neither have to give names to the established facts nor recall what the established facts you are using to verify the new statement. When you are using Lean, you do not have such freedom. Think this way: when you are using Lean or Coq to formalize math, you are actually implementing a Litex kernel by yourself in the first place so that you can use it to verify your statements. This burden really should not be on the user.

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

Each statement in Litex has four potential outcomes: true, false, unknown, or error. Factual statements start with `$` to differentiate them from functions.[^1]

When you run the above example on [playground](https://litexlang.org/playground), you might see the output similar to this:

```
Jordan = Jordan
is true. proved by
literally the same
human = human
is true. proved by
literally the same
$in(Jordan, human)
is true. proved by
$in(Jordan, human)
Jordan matches Jordan
human matches human

$intelligent(Jordan)
is true. proved by
forall x human:
    $intelligent(x)
```

It says how the factual statement `$intelligent(Jordan)` is verified by the Litex kernel based on the established facts. Here a universal fact `forall x Human: $intelligent(x)` is used to verify the specific factual statement `$intelligent(Jordan)`. Keep this example in mind. This is the most classic example of how people uses `match and substitution` to establish new facts. Refer to this example when you are reading the next section.

[^1]: Factual expressions are typically written as `$propName(objects)`. They begin with `$` to differentiate them from functions. Litex is a language close to everyday math, that is why it provides 3 handy exceptions to make your code nicer: 1. builtin keywords like =, > are written as daily life math 2. If the proposition requires one and only one object, it can be written as `object $propName` 3. If the proposition requires two objects, it can be written as `object1 $propName object2`.

## Verification is pattern matching, and so is Litex.

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

_God made the integers, man made the rest._

_-- Kronecker_

Math is about deriving new facts from established ones. Verification is about making sure the new facts are true based on the established ones. There are and only are two ways of verifying a new fact:

1. From special case to special case. e.g. `a = 1` => `a = 1`. The derived fact `a = 1` (the second statement) is true because the first statement is true and the first statement is written exactly the same as the second statement. I call it `match`.

2. From general case to special case. e.g. `forall x Human: $intelligent(x)` => `$intelligent(Jordan)`. The derived fact `intelligent(Jordan)` is true because by substituting `x` with `Jordan`, the first statement is true, and the second statement is written exactly the same as the first statement after substitution. I call it `match and substitution`.

You just learned how Litex builds math from basic pieces, like building blocks. To sum up, `match and substitution` is the basic way of deriving new facts from established ones. Such method is called first-order logic. We can construct the whole math system by this way in Lite as long as basic arithmetic and counting are built-in. [^2][^3][^4][^5]

[^2]: There are exceptions. Facts about symbols with literal information (e.g. numbers like 1, 2, 3, counting etc) are not verified in this way. Facts related to counting are not verified in this way. There are and only these two exceptions. Those facts are verified by Litex's builtin rules, the user does not need to worry about them.

[^3]: Voltaire once said: "Common sense is not so common." In the case of Litex, Litex makes the process of building math as easy as `ctrl+f/cmd+f` in your browser, by discovering that math is nothing but a special kind of `match and substitution` problem. Everyone is so familiar with this process, but almost no one actually finds its significance and use this idea to create a simple formal language. The real magic of Litex is that it works just like how people think in daily life. This is a hard magic for the language designer, because it requires a deep understanding of both the nature of mathematics and the nature of programming, but is worth the effort.

[^4]: In naive set theory, where almost all daily math is based on, all facts are derived by `match and substitution` using first-order logic, with only two exceptions: 1. mathematical induction. 2. the axiom of replacement. Those two are builtin in Litex.

[^5]: Litex is a very simple language to learn. In fact, I am not sure whether I should use "learn" to describe it. Most of Litex language features are so common sense that we use it everyday to reason. I guess people can not "learn" what they have already known! A lot of people may think math is hard, but what Litex does is to make math as easy as `ctrl+f/cmd+f` in your browser. Let more people find pleasure in the wonderful world of math!

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
| `prove_over_finite_set` | prove a universal statement by iterating over a finite set |
| `import` | import a file or directory |

[^3]: Although these keywords are rarely defined strictly in math textbooks, they are used everyday and everywhere. Litex creator can not find strict definition for keywords like `proposition`, `is`, `in` etc (actually, the word `definition` is also a vague word). He tried his best to make the meaning of these keywords as close to the meaning in our daily math expression, along with his own ideas and understanding, so that Litex is both intuitive and strict.

##  Examples: Litex for Curious Formal Language Users

_Beautiful is better than ugly. Explicit is better than implicit. Simple is better than complex._

_-- The Zen of Python_

_What I cannot create, I do not understand._

_-- Richard Feynman_


Here are some examples of Litex, in Litex for Curious Lean Users and other formal language users. Detailed explanations are provided in [Litex for Curious Lean Users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md). I put them here for you to get a sense of the language. Run these examples on [playground](https://litexlang.org/playground).

I will show you how Litex is shaped by common sense, and why common sense is not so common in traditional formal languages. It must be noted that making Litex so common sense is a very uncommon thing, because it requires a deep understanding of both the nature of mathematics and the nature of programming.

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

Next we prove `sqrt(2) is irrational`. Since the standard library is not yet implemented, we have to define the logBase function ourselves for now. Note that how easy it is to define a new concept in Litex. You do not have to start from a very low level concept and build up to a higher level concept. You can define a new concept directly.

The Litex proof requires no extra knowledge except basic math knowledge, but the Lean proof requires a huge amount of knowledge about Lean tactics. Tactics are not easy to learn, not easy to remember, and very far from what we are truly thinking when we are doing math.

Litex:

```
fn logBase(x, y N) N:
    dom:
        y != 0

know forall x, y, z N:
    logBase(x^y, z) = y * logBase(x, z)
    logBase(x*y, z) = logBase(x, z) + logBase(y, z)

know forall x N:
    logBase(x, x) = 1

claim:
    not sqrt(2) $in Q
    prove_by_contradiction:
        have x, y st $rational_number_representation_in_fraction(sqrt(2))
        
        x = sqrt(2) * y
        x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)
        sqrt(2) ^ 2 = 2 # must write it out
        x ^ 2 = 2 * (y ^ 2)
        logBase(x ^ 2, 2) = logBase(2 * (y ^ 2), 2)
        
        logBase(x ^ 2, 2) = 2 * logBase(x, 2)
        logBase(y ^ 2, 2) = 2 * logBase(y, 2)

        logBase(2 * (y ^ 2), 2) = logBase(2, 2) + logBase(y ^ 2, 2)
        logBase(2, 2) = 1
        logBase(2 * (y ^ 2), 2) = 1 + logBase(y ^ 2, 2)

        logBase(x ^ 2, 2) = 1 + 2 * logBase(y, 2)
        2 * logBase(x, 2) = 1 + 2 * logBase(y, 2)

        (2 * logBase(x, 2)) % 2 = (1 + 2 * logBase(y, 2)) % 2
        (2 * logBase(x, 2)) % 2 = 0
        0 = (1 + 2 * logBase(y, 2)) % 2

        (1 + 2 * logBase(y, 2)) % 2 = 1 % 2 + (2 * logBase(y, 2)) % 2
        1 % 2 + (2 * logBase(y, 2)) % 2 = 1 + 0
        0 = 1
```

Lean:

```
theorem sqrt2_irrational : 
  ¬ ∃ a b : ℕ, a.gcd b = 1 ∧ a * a = 2 * b * b := by
  intro h
  obtain ⟨a, b, hcop, h⟩ := h

  have ha_even : Even (a) := by
    rw [Nat.mul_assoc] at h
    have : Even (a * a) := by rw [h]; exact even_mul_right b b
    exact even_of_even_sq this

  obtain ⟨k, hk⟩ := ha_even

  have h2 : 2 * k * k = b * b := by
    rw [hk, ←mul_assoc, ←mul_assoc, mul_comm 2 2, ←mul_assoc] at h
    apply Nat.mul_right_cancel (Nat.zero_lt_succ _)
    rw [←h, ←mul_assoc, ←mul_assoc]
    rfl

  have hb_even : Even b := even_of_even_sq (by rw [←h2]; exact even_mul_left _ _)

  obtain ⟨m, hm⟩ := hb_even  -- b = 2m

  have : a.gcd b ≠ 1 := by
    rw [hk, hm]
    have : (2 * k).gcd (2 * m) = 2 * (k.gcd m) := Nat.gcd_mul_left_right
    apply Nat.ne_of_gt
    apply Nat.mul_pos (by decide)
    exact Nat.gcd_pos_left m (by decide)

  contradiction
```

Next I want to show you how Litex can be used to verify a simple group theory statement. It's clear that the Litex version can be read and understood by a 10-year-old, while the Lean version is much more complex.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):</code><br>
      <code>&nbsp;&nbsp;forall x s, y s, z s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(mul(x, y), z) = mul(x, mul(y, z))</code><br>
      <code>&nbsp;&nbsp;forall x s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(x, inv(x)) = e</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(inv(x), x) = e</code><br><br>
      <code>fn inverse(x R)R:</code><br>
      <code>&nbsp;&nbsp;inverse(x) + x = 0</code><br><br>
      <code>forall x R:</code><br>
      <code>&nbsp;&nbsp;inverse(x) $in R</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = inverse(x) + x</code><br>
      <code>&nbsp;&nbsp;inverse(x) + x = 0</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = 0</code><br><br>
      <code>$is_group(R, +, inverse, 0)</code><br>
      <code>$is_group(Z, +, inverse, 0)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>structure MyGroup (G : Type) where</code><br>
      <code>&nbsp;&nbsp;add : G → G → G</code><br>
      <code>&nbsp;&nbsp;zero : G</code><br>
      <code>&nbsp;&nbsp;neg : G → G</code><br>
      <code>&nbsp;&nbsp;add_assoc : ∀ a b c : G, add (add a b) c = add a (add b c)</code><br>
      <code>&nbsp;&nbsp;zero_add : ∀ a : G, add zero a = a</code><br>
      <code>&nbsp;&nbsp;add_zero : ∀ a : G, add a zero = a</code><br>
      <code>&nbsp;&nbsp;add_left_neg : ∀ a : G, add (neg a) a = zero</code><br><br>
      <code>def intAddGroup : MyGroup Int where</code><br>
      <code>&nbsp;&nbsp;add := Int.add</code><br>
      <code>&nbsp;&nbsp;zero := 0</code><br>
      <code>&nbsp;&nbsp;neg := Int.neg</code><br>
      <code>&nbsp;&nbsp;add_assoc := by intros; apply Int.add_assoc</code><br>
      <code>&nbsp;&nbsp;zero_add := by intros; apply Int.zero_add</code><br>
      <code>&nbsp;&nbsp;add_zero := by intros; apply Int.add_zero</code><br>
      <code>&nbsp;&nbsp;add_left_neg := by intros; apply Int.neg_add_self</code><br><br>
      <code>-- R is not builtin in Lean, the user has to define it himself or rely on the library. We skip use float as an example.</code><br>
      <code>def floatAddGroup : MyGroup Float where</code><br>
      <code>&nbsp;&nbsp;add := Float.add</code><br>
      <code>&nbsp;&nbsp;zero := 0.0</code><br>
      <code>&nbsp;&nbsp;neg := Float.neg</code><br>
      <code>&nbsp;&nbsp;add_assoc := by intros; apply Float.add_assoc</code><br>
      <code>&nbsp;&nbsp;zero_add := by intros; apply Float.zero_add</code><br>
      <code>&nbsp;&nbsp;add_zero := by intros; apply Float.add_zero</code><br>
      <code>&nbsp;&nbsp;add_left_neg := by intros; apply Float.neg_add_self</code><br>
    </td>
  </tr>
</table>



## Contact & Contribute to Litex

_The people who are crazy enough to think they can change the world are the ones who do._

_-- Steve Jobs_

_The best way to predict the future is to invent it._

_-- Alan Kay_

Hi, I am Jiachen Shen (call me Jackie Shen), the creator of Litex. I am a PhD student in mathematics and programming language geek. In 2023, I shockingly found that math is somehow equivalent to programming, after reading Professor Terence Tao's [blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/). This is the most amazing idea that I have ever seen in my life. In 2024, after thinking about it for a year, I started to implement Litex. I use Tao's Analysis One as the main "test case" of Litex. After more than 3000 git commits, what it means to be a "formal language that is intuitive and as aligned with daily math expression as possible" is finally to make sense to me and my kernel sort of works now.

As Arabic numbers transforms the world of math by its clean and concise expression, Litex aims to transform the world of math by its intuitive and natural expression using formal language. Giving semantics to keywords and syntax to Litex and at the same time making what it means as aligned with daily math expression as possible, is the major challenge of Litex. This is a long journey, but I am trying my best to make it happen.

As formal languages are becoming more and more important [in the AI safety, AI reasoning, math collaboration](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md), I think it is time to make Litex more accessible to the public. Hope you enjoy Litex and feel free to contact [me](mailto:litexlang@outlook.com) or join the [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/) to discuss.