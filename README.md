<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**Release v0.1.6-beta (not yet ready for production use)**  
*Jiachen Shen and The Litex Team (Zhaoxuan Hong, et al.)*
**Try Litex on [playground](https://litexlang.org/playground).**

[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Website](https://img.shields.io/badge/Website-blue?logo=website)](https://litexlang.org)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Online Playground](https://img.shields.io/badge/Online%20Playground-darkgreen?logo=playground)](https://litexlang.org/playground)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)

</div>

## Litex: the simplest formal language

_Mathematics is the language with which God wrote the universe._

_-- Galileo Galilei_

_Common sense is not so common._

_-- Voltaire_

[![Click Me To Try Litex On Online  Playground](https://img.nshields.io/badge/Click_Here_To_Try_Litex_On_Online_Playground-%E2%86%92_Explore-FF6B6B?style=for-the-badge)](https://litexlang.org/playground)

**If you are a non-technical reader, please read [this section](#litex-introduction-for-non-technical-readers).**

**Litex is an intuitive and scalable formal language to validate your reasoning. Since a 10-year-old can reason about basic math, even a 10-year-old should be able to learn and use Litex easily to solve their own problems. We assume a man without any math or programming background can learn Litex in 1-2 hours.**

**Formal language makes the process of writing math into a process of writing code. This is a very powerful idea. AI researchers use it to build better and safer models. However, traditional formal languages are too complex for non-technical readers. AI researchers, mathematicians are calling for a new formal language to boost their job.**

**This simplicity and accessibility of Litex reduces the time ratio, between formalizing a proof and writing it in natural language, from 10:1 to 1:1. That is why constructing Litex codebase is 10x cheaper and has a 10x lower entrance barrier than traditional formal languages. This is a blessing for both AI industry and math community.**

Math is about deriving new facts from established ones. Verification is about making sure the new facts are true based on the established ones. There are just two ways of verifying a new fact:

1. From special case to special case. e.g. `a = 1` => `a = 1`. The derived fact `a = 1` (the second statement) is true because the first statement is true and the first statement is written exactly the same as the second statement. I call it `match`.

2. From general case to special case. e.g. `forall x Human => $intelligent(x)` => `$intelligent(Jordan)`. The derived fact `intelligent(Jordan)` is true because by substituting `x` with `Jordan`, the first statement is true, and the second statement is written exactly the same as the first statement after substitution. I call it `match and substitution`.

The key insight behind Litex's extreme simplicity is: mathematical verification is nothing but a fancy form of **match and substitution** problem, similar to "ctrl+f and ctrl+r (or cmd+f and cmd+r)" in your browser. When doing verification, you find an established fact, match it with the new statement, substitute the variables in the established fact with the new statement, and check if the new statement is equal to the substituted established fact. If they are equal, the new statement is verified. 

To ignite the process of deriving new facts from established ones, we need some established facts which are by default true. The fundamentals of modern mathematics i.e. axioms of set theory, are built-in in Litex.

Currently, the bottleneck in this field is that formal languages are too difficult for both humans and AI, resulting in scarce and expensive training data. However, Litex, with its simplicity and close alignment with mathematical syntax and semantics, reduces the cost and barrier of dataset construction by an order of magnitude.

## Installing and updating

_Keep it simple, stupid._

_-- The Unix Philosophy_

The core principle of Litex is simplicity. That is why it is easy to install and get your hands dirty with Litex! To install or update Litex core, you could run the following commands for different systems.

We recommend macOS users to install Litex by Homebrew with following command:

```bash
brew install litexlang/tap/litex
```

For Ubuntu/Debian users, please paste following command to your terminal:

```bash
wget https://github.com/litexlang/golitex/releases/download/0.1.9-beta/litex_0.1.9-beta_amd64.deb
sudo dpkg -i litex_0.1.9-beta_amd64.deb
```

For Windows users, please download MSI file form [**HERE**](https://github.com/litexlang/golitex/releases/download/0.1.9-beta/litex_0.1.9-beta_amd64.msi)

After installing, your could run `litex -version` to see if it was installed. And enjoy it via command `litex`.

## Supporting Tools

As you installed Litex core, you can interact with Litex via following tools:

- [litex-python-api](https://github.com/litexlang/litex-python-api)
- [litex-jupyter-kernel](https://github.com/litexlang/litex-jupyter-kernel)

## Difference between Litex and Python and Lean

Litex is very intuitive, which is very rare for a formal language. Traditional formal languages like Lean, Coq, because they are still programming languages, just like Python and C. There are huge gaps between programming and verification. Serving both purpose of computation and verification is technically challenging, which makes them much more complex than Litex. The following table might give you a sense of the gap.

| Feature              | Mathematics                                                                 | Programming                                                                    |
|----------------------|------------------------------------------------------------------------------|--------------------------------------------------------------------------------|
| **Variable**          | No real "variable" — once an object is defined, its meaning is fixed        | Variables can change values during execution                                   |
| **Function**          | A symbol that builds new expressions from input symbols (no execution)      | A block of executable code that performs computation or side effects           |
| **Execution**         | No execution — everything is symbolic manipulation or `match and substitution`           | Involves actual computation steps and runtime behavior                         |
| **Control Flow**      | Uses logical constructs like `∀` (for all) to reason about all cases         | Uses constructs like `for`, `while`, `if` to control the flow of execution     |
| **Iteration**         | Infinite or large domains handled abstractly (e.g. by induction or logic)    | Requires explicit loops and step-by-step computation                           |
| **Existential Quantification** |  Existential quantification is a fundamental part of math | No existential quantification — all objects are explicitly defined |
| **Purpose**           | To prove or verify truth symbolically                                        | To perform tasks, process data, interact with systems                          |

Litex, as a domain language, takes advantage of the difference between programming and verification, and is designed to be a simple and intuitive reasoning verifier. Technically, Litex is a "Read-Only Turing Machine". It does not have variables, execution, control flow, iteration, etc. The fundamental difference between programming and verification is verification never changes what has been established (i.e. what has been proved to be true is always true), but when programming we are always updating values of variables. Traditional formal languages sort of robbed you of the joy of exploring mathematics by forcing you to spend most of your time wrestling with the formal language itself. Litex brings that joy back! [^1][^2]

Math serves two purposes: 1. for computation, i.e. calculate the output of a function given the input, and 2. for reasoning and verification, i.e. make sure a new statement is correct given the established ones. Math is the language of the universe and since the beginning of history we human beings have been using math to know how things work to do real-life problems. The software industry has already revolutionized how we compute, and Litex is here to change how we reason.

This README shows how the deep understanding of both the nature of mathematics and the nature of programming shapes the unique design of Litex. Let's start with a simple example.

[^1]: The Litex kernel is much larger than Lean's kernel. There are two reasons for that. First, there are multiple ways to build the foundations of mathematics. Litex uses set theory, while Lean uses type theory. Although the two are logically equivalent, type theory is more abstract. This abstraction helps keep the Lean kernel small, but also makes it harder for users to understand. Since most people are introduced to set theory in high school, it is not ideal to use type theory as the foundation if the goal is to make a formal language widely accessible. Second, Lean is a programming language. Because it is Turing-complete, Lean shifts the responsibility of implementing low-level logic to the user. This means that users must essentially build parts of the system themselves before they can even begin verifying their own statements — and there's no guarantee that their implementation is correct. In contrast, Litex handles low-level logic within the kernel itself. This allows users to focus entirely on expressing and verifying their ideas, and it makes Litex both easier to use and computationally more efficient than most other formal languages. Every design choice in Litex is made with user-friendliness as the top priority. Litex is focused solely on verification, which dramatically simplifies the user experience. For example, the Litex kernel automatically searches for established facts, so users don’t need to name them or remember which ones they’re using. In Lean or Coq, this kind of support doesn’t exist — the user must essentially reimplement a Litex-like kernel by hand before verification can even begin. This burden should not fall on the user.

[^2]: Litex has a symbolic view of math. The process of  `match and substitution` cares about what a symbol is, not what a symbol means.

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

This example means: All humans are intelligent. Jordan is a human. Therefore, Jordan is intelligent. It is a very typical syllogism example. (本例是一个典型的三段论例子：所有人类都是聪明的。乔丹是人类。因此，乔丹是聪明的。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>let human set, Jordan human</code> <br><br>
      <code>prop intelligent(x Human)</code> <br><br>      
      <code>know forall x Human => $intelligent(x)</code> <br>
      <code>$intelligent(Jordan)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>def Human := Type</code> <br><br>
      <code>def intelligent (x : Human) : Prop := true</code> <br><br>
      <code>axiom intelligent_all :</code><br>
      <code>&nbsp;&nbsp;∀ (x : Human), intelligent x</code> <br><br>
      <code>example (Jordan : Human) : intelligent Jordan := intelligent_all Jordan</code>
    </td>
  </tr>
</table>

The above example means: `Human` is the set of all humans. Using `know`, we establish a simple fact: all humans are intelligent. When the user input `intelligent(Jordan)`, the system will automatically find the fact `forall x Human => $intelligent(x)` and substitute `x` with `Jordan`, and then check if the result is true. This process is called `match and substitution`. Since Jordan is in the set of `Human`, "Jordan is intelligent" is true.

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

It says how the factual statement `$intelligent(Jordan)` is verified by the Litex kernel based on the established facts. Here a universal fact `forall x Human => $intelligent(x)` is used to verify the specific factual statement `$intelligent(Jordan)`. Keep this example in mind. This is the most classic example of how people uses `match and substitution` to establish new facts. Refer to this example when you are reading the next section. The kernel prints out how it verifies the statement, so you can see how it works.

[^1]: Factual expressions are typically written as `$propName(objects)`. They begin with `$` to differentiate them from functions. Litex is a language close to everyday math, that is why it provides 3 handy exceptions to make your code nicer: 1. builtin keywords like =, > are written as daily life math 2. If the proposition requires one and only one object, it can be written as `object $propName` 3. If the proposition requires two objects, it can be written as `object1 $propName object2`.

## Verification is pattern matching, and so is Litex.

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

_God made the integers, man made the rest._

_-- Kronecker_

Math is about deriving new facts from established ones. Verification is about making sure the new facts are true based on the established ones. There are and only are two ways of verifying a new fact:

1. From special case to special case. e.g. `a = 1` => `a = 1`. The derived fact `a = 1` (the second statement) is true because the first statement is true and the first statement is written exactly the same as the second statement. I call it `match`.

2. From general case to special case. e.g. `forall x Human => $intelligent(x)` => `$intelligent(Jordan)`. The derived fact `intelligent(Jordan)` is true because by substituting `x` with `Jordan`, the first statement is true, and the second statement is written exactly the same as the first statement after substitution. I call it `match and substitution`.

You just learned how Litex builds math from basic pieces, like building blocks. To sum up, `match and substitution` is the basic way of deriving new facts from established ones. We can construct the whole math system by this way in Lite as long as basic arithmetic and counting are built-in. [^3][^4][^5][^6][^7]

[^3]: There are exceptions. Facts about symbols with literal information (e.g. numbers like 1, 2, 3, counting etc) are not verified in this way. Facts related to counting are not verified in this way. There are and only these two exceptions. Those facts are verified by Litex's builtin rules, the user does not need to worry about them.

[^4]: Voltaire once said: "Common sense is not so common." In the case of Litex, Litex makes the process of building math as easy as `ctrl+f & ctrl+r /cmd+f & cmd+r` in your browser, by discovering that math is nothing but a special kind of `match and substitution` problem. Everyone is so familiar with this process, but almost no one actually finds its significance and use this idea to create a simple formal language. The real magic of Litex is that it works just like how people think in daily life. This is a hard magic for the language designer, because it requires a deep understanding of both the nature of mathematics and the nature of programming, but is worth the effort.

[^5]: In naive set theory, where almost all daily math is based on, all facts are derived by `match and substitution` using first-order logic, with only two exceptions: 1. mathematical induction. 2. the axiom of replacement. Those two are builtin in Litex. Since high-order logic is "passing proposition as parameter to another proposition", facts about high-order logic are still verified by `match and substitution`. Litex will implement high-order logic in the future. If you are still worried about whether Litex is rigorous, the Litex kernel prints out how it verifies the statement, so you can see how it works.

[^6]: Litex is a very simple language to learn. In fact, I am not sure whether I should use "learn" to describe it. Most of Litex language features are so common sense that we use it everyday to reason. I guess people can not "learn" what they have already known! A lot of people may think math is hard, but what Litex does is to make math as easy as `ctrl+f & ctrl+r /cmd+f & cmd+r` in your browser. Let more people find pleasure in the wonderful world of math!

[^7]: Carful readers may worry the foundation of Litex is shaky, because `match and substitution` is not a very rigorous concept. They might think Type theory, where Lean is based on, is more solid. I disagree. First, the kernel of type system in Lean is just a huge piece of C++ code, doing `match and substitution`. Second, no matter what mathematical foundation a traditional formal language is based on (in the case of Lean, it is Type theory), it is still a programming language, which is no different from Python. The syntax style of Lean makes it sort of easier to write formal proofs, but it is still very very far from what we are truly thinking when we are doing math, because the semantics of Lean is still a programming language. All language designers agree it is the semantic that matters more, not the syntax. Litex has a semantics designed to be as close to the way we think in daily life as possible.

## Litex Keywords

_Design and programming are human activities; forget that and all is lost._

_-- Bjarne Stroustrup_

Litex is a simple language. I hope many of the keywords are already familiar to you.[^3]

| Keyword | Meaning |
|---------|---------|
| `let` | Define an object. Anything in Litex is an object. |
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
| `len`  | length of a set |
| `finite_set` | a set with a finite number of elements |
| `prove` | open a local environment to write some statements without affecting the global environment |
| `claim` | claim a factual statement, prove it here |
| `prove_by_contradiction` | prove by contradiction |
| `prove_in_each_case` | prove by case analysis |
| `prove_by_induction` | prove by mathematical induction |
| `prove_over_finite_set` | prove a universal statement by iterating over a finite set |
| `import` | import a file or directory |
| `exist_in` | exist a object in a set |
| `set_defined_by_replacement` | define a set by a axiom of replacement |
| `obj_exist_as_preimage_of_prop` | exist a object as the preimage of a proposition |
| `obj_exist_as_preimage_of_fn` | exist a object as the preimage of a function |
| `N` `N_pos` `Z` `Q` `R` `C` | builtin sets: natural numbers, positive natural numbers, integers, rational numbers, real numbers, complex numbers |
| `clear` | clear all facts |
| `set_product` | a product of sets |
| `proj` | a projection of a set product |

[^3]: Although these keywords are rarely defined strictly in math textbooks, they are used everyday and everywhere. Litex creator can not find strict definition for keywords like `proposition`, `is`, `in` etc (actually, the word `definition` is also a vague word). He tried his best to make the meaning of these keywords as close to the meaning in our daily math expression, along with his own ideas and understanding, so that Litex is both intuitive and strict.

##  Examples: Litex for Curious Formal Language Users

_Beautiful is better than ugly. Explicit is better than implicit. Simple is better than complex._

_-- The Zen of Python_

_What I cannot create, I do not understand._

_-- Richard Feynman_

The best way to introduce something is by comparing it to other things of the same kind. Lean is a popular formal language, which has a 1 million LOC library and a vivid user community. The reason why people use Lean instead of Python to write math is that Lean is a programming language based on type theory, and type theory is one of the many ways of defining math. However, type theory is hard (even math PhD students do not understand it) and modern mathematics is built on top of another theory called set theory. Litex is based on set theory. I put examples here for you to get a sense of the simplicity of Litex. Run these examples on [playground](https://litexlang.org/playground).

I will show you how Litex is shaped by common sense, and why common sense is not so common in traditional formal languages. It must be noted that making Litex so common sense is a very uncommon thing, because it requires a deep understanding of both the nature of mathematics and the nature of programming.

Next I want to show you how Litex can be used to solve a simple linear equation. It's clear that the Litex version can be read and understood by a 10-year-old, while the Lean version is much more complex.

This example means: Solve the equation 2x + 3y = 10 and 4x + 5y = 14. (本例是一个典型的多元线性方程组例子：解方程 2x + 3y = 10 和 4x + 5y = 14。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>let x R, y R:</code><br>
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
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example (x y : ℝ) (h₁ : 2 * x + 3 * y = 10) (h₂ : 4 * x + 5 * y = 14) : x = -4 ∧ y = 6 := by</code><br>
      <code>&nbsp;&nbsp;have h₃ : 2 * (2 * x + 3 * y) = 2 * 10 := by rw [h₁]</code><br>
      <code>&nbsp;&nbsp;have h₄ : 4 * x + 6 * y = 20 := by linear_combination 2 * h₁</code><br>
      <code>&nbsp;&nbsp;have h₅ : (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 := by</code><br>
      <code>&nbsp;&nbsp;rw [h₄, h₂]</code><br>
      <code>&nbsp;&nbsp;have h₆ : (4 * x + 6 * y) - (4 * x + 5 * y) = y := by</code><br>
      <code>&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;have h₇ : 20 - 14 = 6 := by norm_num</code><br>
      <code>&nbsp;&nbsp;have h₈ : y = 6 := by</code><br>
      <code>&nbsp;&nbsp;rw [←h₆, h₅, h₇]</code><br>
      <code>&nbsp;&nbsp;have h₉ : 2 * x + 3 * 6 = 10 := by rw [h₈, h₁]</code><br>
      <code>&nbsp;&nbsp;have h₁₀ : 2 * x + 18 = 10 := by</code><br>
      <code>&nbsp;&nbsp;rw [mul_add] at h₉</code><br>
      <code>&nbsp;&nbsp;simp at h₉</code><br>
      <code>&nbsp;&nbsp;exact h₉</code><br>
      <code>&nbsp;&nbsp;have h₁₁ : 2 * x = -8 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₀ - 18</code><br>
      <code>&nbsp;&nbsp;have h₁₂ : x = -4 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₁ / 2</code><br>
      <code>&nbsp;&nbsp;exact ⟨h₁₂, h₈⟩</code>
    </td>
  </tr>
</table>

I know Lean can use tactics to solve the same problem, and it is shorter. Litex will introduce similar features in the future. What I really want to show you here is that Litex is much more readable and intuitive than Lean in this case. Not every situation can be solved by tactics, and writing tactics itself in Lean is not easy. Litex spares you from remembering all these difficult things like `have`, `by`, `rw`, `simp`, `exact` and strange syntax etc. All you need is basic math knowledge, which significantly reduces the barrier to entry.

There is another way to write the same example in Litex, a bottom-up way.


<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>claim:</code><br>
       <code>&nbsp;forall x, y R:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x = -4</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;y = 6</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;4 * x + 5 * y = 14</code><br>
       <code>&nbsp;&nbsp;prove:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;=:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;10</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 * -4 + 3 * 6</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 * x + 3 * y</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;=:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;14</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;4 * -4 + 5 * 6</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;4 * x + 5 * y</code><br>
       <code></code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>example : ∀ x y : ℝ, x = -4 → y = 6 → (2 * x + 3 * y = 10 ∧ 4 * x + 5 * y = 14) :=</code><br>
       <code>by</code><br>
       <code>&nbsp;intro x y hx hy</code><br>
       <code>&nbsp;constructor</code><br>
       <code>&nbsp;· rw [hx, hy]</code><br>
       <code>&nbsp;&nbsp;calc</code><br>
       <code>&nbsp;&nbsp;&nbsp;2 * (-4) + 3 * 6 = (-8) + 18 := by rw [mul_neg, mul_one]</code><br>
       <code>&nbsp;&nbsp;&nbsp;_                = 10         := by rw [add_comm]</code><br>
       <code>&nbsp;· rw [hx, hy]</code><br>
       <code>&nbsp;&nbsp;calc</code><br>
       <code>&nbsp;&nbsp;&nbsp;4 * (-4) + 5 * 6 = (-16) + 30 := by rw [mul_neg, mul_one]</code><br>
       <code>&nbsp;&nbsp;&nbsp;_                = 14         := by rw [add_comm]</code><br>
       <code></code><br>
    </td>
  </tr>
</table>


Next we prove `sqrt(2) is irrational`. Since the standard library is not yet implemented, we have to define the log function ourselves for now. Note that how easy it is to define a new concept in Litex. You do not have to start from a very low level concept and build up to a higher level concept. You can define a new concept directly.

The Litex proof requires no extra knowledge except basic math knowledge, but the Lean proof requires a huge amount of knowledge about Lean tactics. Tactics are not easy to learn, not easy to remember, and very far from what we are truly thinking when we are doing math. On the other hand, any line of Litex code is very obvious to understand.

This example means: Prove `sqrt(2) is irrational`. (本例是一个典型的无理数证明例子：证明 `sqrt(2) 是无理数`。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>claim:</code><br>
      <code>&nbsp;&nbsp;not sqrt(2) $in Q</code><br>
      <code>&nbsp;&nbsp;prove_by_contradiction:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have x, y st $Q_representation_in_fraction(sqrt(2))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x = sqrt(2) * y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;sqrt(2) ^ 2 = 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = 2 * (y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, x ^ 2) = log(2, 2 * (y ^ 2))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, x ^ 2) = 2 * log(2, x)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, y ^ 2) = 2 * log(2, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, 2 * (y ^ 2)) = log(2, 2) + log(2, y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, 2) = 1</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, 2 * (y ^ 2)) = 1 + log(2, y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, x ^ 2) = 1 + 2 * log(2, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * log(2, x) = 1 + 2 * log(2, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(2 * log(2, x)) % 2 = (1 + 2 * log(2, y)) % 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(2 * log(2, x)) % 2 = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;0 = (1 + 2 * log(2, y)) % 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(1+2 * log(2, y)) % 2 = 1 % 2 + (2*log(2, y)) % 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;1 % 2 + (2 * log(2, y)) % 2 = 1 + 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;0 = 1</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>theorem sqrt2_irrational :</code><br>
      <code>&nbsp;&nbsp;¬ ∃ a b : ℕ, a.gcd b = 1 ∧ a * a = 2 * b * b := by</code><br>
      <code>&nbsp;&nbsp;intro h</code><br>
      <code>&nbsp;&nbsp;obtain ⟨a, b, hcop, h⟩ := h</code><br><br>
      <code>have ha_even : Even a := by</code><br>
      <code>&nbsp;&nbsp;rw [Nat.mul_assoc] at h</code><br>
      <code>&nbsp;&nbsp;have : Even (a * a) := by rw [h]; exact even_mul_right b b</code><br>
      <code>&nbsp;&nbsp;exact even_of_even_sq this</code><br><br>
      <code>obtain ⟨k, hk⟩ := ha_even</code><br><br>
      <code>have h2 : 2 * k * k = b * b := by</code><br>
      <code>&nbsp;&nbsp;rw [hk, ←mul_assoc, ←mul_assoc, mul_comm 2 2, ←mul_assoc] at h</code><br>
      <code>&nbsp;&nbsp;apply Nat.mul_right_cancel (Nat.zero_lt_succ _)</code><br>
      <code>&nbsp;&nbsp;rw [←h, ←mul_assoc, ←mul_assoc]</code><br>
      <code>&nbsp;&nbsp;rfl</code><br><br>
      <code>have hb_even : Even b :=</code><br>
      <code>&nbsp;&nbsp;even_of_even_sq (by rw [←h2]; exact even_mul_left _ _)</code><br><br>
      <code>obtain ⟨m, hm⟩ := hb_even</code><br><br>
      <code>have : a.gcd b ≠ 1 := by</code><br>
      <code>&nbsp;&nbsp;rw [hk, hm]</code><br>
      <code>&nbsp;&nbsp;have : (2 * k).gcd (2 * m) = 2 * (k.gcd m) := Nat.gcd_mul_left_right</code><br>
      <code>&nbsp;&nbsp;apply Nat.ne_of_gt</code><br>
      <code>&nbsp;&nbsp;apply Nat.mul_pos (by decide)</code><br>
      <code>&nbsp;&nbsp;exact Nat.gcd_pos_left m (by decide)</code><br><br>
      <code>contradiction</code>
    </td>
  </tr>
</table>

Next I want to show you how Litex can be used to verify a simple group theory statement. It's clear that the Litex version can be read and understood by a 10-year-old, while the Lean version is much more complex. Look how easy it is to narrow the function type of `inverse` from `R` to `Z`.

This example means: Define a group, and prove `R` is a group. (本例是一个典型的群论例子：定义一个群，并证明 `R` 是一个群。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):</code><br>
      <code>&nbsp;&nbsp;forall x s, y s, z s:</code><br>
      <code>&nbsp;&nbsp;mul(mul(x, y), z) = mul(x, mul(y, z))</code><br>
      <code>&nbsp;&nbsp;forall x s:</code><br>
      <code>&nbsp;&nbsp;mul(x, inv(x)) = e</code><br>
      <code>&nbsp;&nbsp;mul(inv(x), x) = e</code><br><br>
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
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
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
      <code>-- R is not builtin in Lean, the user has to define it himself or rely on the library. We skip it.</code><br>
    </td>
  </tr>
</table>

To better show the power of `fn_template`, There is another example of defining an algorithm mathematically. This example means: Define an algorithm, and prove `f(x) = x` is an algorithm. (本例是一个典型的算法定义例子：定义一个算法，并证明 `f(x) = x` 是一个算法。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
       <code>fn comp_seq(D set, f fn(D)D) fn(D, N)D:</code><br>
       <code>&nbsp;&nbsp;forall x D, n N:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(D, f)(x,n+1) = f(comp_seq(D, f)(x, n))</code><br>
       <code>&nbsp;&nbsp;comp_seq(D, f)(x, 0) = x</code><br>
       <code></code><br>
       <code>exist_prop n N st exist_end_of_comp_seq(D set, x D, f fn(D,N)D):</code><br>
       <code>&nbsp;&nbsp;f(x, n) = f(x, n+1)</code><br>
       <code></code><br>
       <code>prop is_algorithm(D set, I set, f fn(D)D):</code><br>
       <code>&nbsp;&nbsp;forall x I: # i.e. I is subset of D</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x $in D</code><br>
       <code>&nbsp;&nbsp;<=>:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;forall x I:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$exist_end_of_comp_seq(D, x, comp_seq(D, f))</code><br>
       <code></code><br>
       <code>fn f(x R)R:</code><br>
       <code>&nbsp;&nbsp;f(x) = x</code><br>
       <code></code><br>
       <code>claim:</code><br>
       <code>&nbsp;&nbsp;forall x R:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;$exist_end_of_comp_seq(R, x, comp_seq(R, f))</code><br>
       <code>&nbsp;&nbsp;prove:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(R, f)(x, 0) = x</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(R, f)(x, 0 + 1) = f(comp_seq(R, f)(x, 0))</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(R, f)(x, 0 + 1) = f(x)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;f(x) = x</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(R, f)(x, 0 + 1) = x</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(R, f)(x, 0) = comp_seq(R, f)(x, 1)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;exist 0 st $exist_end_of_comp_seq(R, x, comp_seq(R, f))</code><br>
       <code></code><br>
       <code>$is_algorithm(R, R, f)</code><br>
       <code></code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
       <code>structure ComputationalMethod where</code><br>
       <code>  Q : Type</code><br>
       <code>  I : Set Q</code><br>
       <code>  S : Set Q</code><br>
       <code>  f : Q → Q</code><br>
       <code>  f_fixed : ∀ q ∈ S, f q = q</code><br>
       <code></code><br>
       <code>namespace ComputationalMethod</code><br>
       <code></code><br>
       <code>def comp_sequence (cm : ComputationalMethod) (x : cm.Q) : ℕ → cm.Q</code><br>
       <code>  | 0 => x</code><br>
       <code>  | n + 1 => cm.f (comp_sequence x n)</code><br>
       <code></code><br>
       <code>def TerminatesIn (cm : ComputationalMethod) (x : cm.Q) (k : ℕ) : Prop :=</code><br>
       <code>  comp_sequence cm x k ∈ cm.S ∧</code><br>
       <code>  ∀ i < k, comp_sequence cm x i ∉ cm.S</code><br>
       <code></code><br>
       <code>def IsAlgorithm (cm : ComputationalMethod) : Prop :=</code><br>
       <code>  ∀ x ∈ cm.I, ∃ k, TerminatesIn cm x k</code><br>
       <code></code><br>
       <code>end ComputationalMethod</code><br>
       <code></code><br>
       <code>open ComputationalMethod</code><br>
       <code></code><br>
       <code>def IdMethod : ComputationalMethod :=</code><br>
       <code>{ Q := ℝ,</code><br>
       <code>  I := Set.univ,</code><br>
       <code>  S := Set.univ,</code><br>
       <code>  f := id,</code><br>
       <code>  f_fixed := by intros q h; rfl }</code><br>
       <code></code><br>
       <code>example : IsAlgorithm IdMethod :=</code><br>
       <code>by</code><br>
       <code>  intros x hx</code><br>
       <code>  use 0</code><br>
       <code>  unfold TerminatesIn comp_sequence</code><br>
       <code>  constructor</code><br>
       <code>  · simp</code><br>
       <code>    exact Set.mem_univ _</code><br>
       <code>  · </code><br>
       <code>    intros i hi</code><br>
       <code>    exact False.elim (Nat.not_lt_zero _ hi)</code><br>
       <code></code><br>
    </td>
  </tr>
</table>


## Litex Introduction For Non-Technical Readers

_We always overestimate the change that will occur in the next two years and underestimate the change that will occur in the next ten._

_-- Bill Gates_

**Litex** is a simple and easy-to-learn formal language. Its design philosophy is to make the process of formal reasoning as intuitive and natural as writing in natural language. Thanks to its innovative syntax and semantic mechanisms, even ten-year-olds can quickly learn to use Litex for basic formal expression.

Existing formal languages (such as Lean, Coq, Isabelle, etc.) are too complex and have steep learning curves, severely limiting their broader adoption and impact. In the foreseeable future, Litex aims to reduce the time cost ratio between *formalizing* a mathematical proof and *writing* it in natural language from the current \~10:1 to 1:1, dramatically improving the efficiency of structuring mathematical knowledge. 

At its core, mathematics serves two key purposes: one is **computation**, i.e., deriving outputs from known inputs; the other is **reasoning and verification**, ensuring the correctness of new propositions based on existing knowledge. Computation has already been revolutionized by the software industry—from manual calculations to high-performance computing, from the Turing machine model to modern deep learning frameworks. In contrast, the domain of reasoning still largely relies on human experts expressing and checking arguments in natural language.

The birth of **Litex** aims to fill this gap. It enables the reasoning process to be directly understood, checked, and generated by machines—transforming mathematical reasoning from a natural language activity into a **structured, automated, and verifiable process**.

In areas like probability theory, calculus, combinatorics, etc., where so many real world engineering problems are solved by, it is nearly impossible to use existing formal languages like Lean to formalize them because of their steep learning curve. Litex, as a powerful yet easy-to-learn formal language, is designed to fill this gap.

For the time being, The number of people who study and use math is 100-1000 times more than the number of people who study and use formal languages. There is certainly a huge existing opportunity for Litex to make a difference.

Litex isn’t just solving today’s problems—it’s opening the door to a new era in AI. As language models evolve, reasoning is emerging as the true measure of intelligence. Leading labs like DeepMind, OpenAI, and DeepSeek are already integrating formal languages into training to improve logical consistency. Meta’s \$15B investment in Scale AI shows the future of AI lies in data—especially structured, logic-rich data. Natural language alone falls short; to teach reasoning, we need formal languages. Just as Python became core to AI development, formal languages like Litex are poised to become vital infrastructure on the path to AGI.


**Litex**, driven by minimalist design, balances readability, expressive power, and automation. It aspires to become the *standard intermediate language for AI reasoning systems*, while also supporting formal verification tasks across advanced manufacturing, crypto-currency, software engineering, and education. 

**In one sentence**: Computation has been automated—reasoning should be too. Litex is making that a reality.

## Contact & Contribute to Litex

_The people who are crazy enough to think they can change the world are the ones who do._

_-- Steve Jobs_

_The best way to predict the future is to invent it._

_-- Alan Kay_

Hi, I am Jiachen Shen (call me Jackie Shen), the creator of Litex. I am a PhD student in mathematics and programming language geek. In 2023, I shockingly found that math is somehow equivalent to programming, after reading Professor Terence Tao's [blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/). This is the most amazing idea that I have ever seen in my life. In 2024, after thinking about it for a year, I started to implement Litex. I use Tao's Analysis One as the main "test case" of Litex. After more than 3000 git commits, what it means to be a "formal language that is intuitive and as aligned with daily math expression as possible" is finally to make sense to me and my kernel sort of works now.

As Arabic numbers transforms the world of math by its clean and concise expression, Litex aims to transform the world of math by its intuitive and natural expression using formal language. Giving semantics to keywords and syntax to Litex and at the same time making what it means as aligned with daily math expression as possible, is the major challenge of Litex. This is a long journey, but I am trying my best to make it happen.

As formal languages are becoming more and more important [in the AI safety, AI reasoning, math collaboration](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md), I think it is time to make Litex more accessible to the public. Some of the features of Litex are still under development and not yet open-sourced. Hope you enjoy Litex and feel free to contact [me](mailto:litexlang@outlook.com) or join the [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/) to discuss. If you want to contribute or have any questions, please contact me through [email](mailto:litexlang@outlook.com).