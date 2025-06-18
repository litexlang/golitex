<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

_The Formal Language Where Natural Expression Meets Scalable Formal Reasoning_

**Release v0.1.1-beta (not yet ready for production use)**  
*May 2025*  
*Created by Jiachen Shen (You can call me Jackie Shen.)*

[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com)
[![Website](https://img.shields.io/badge/Website-blue?logo=website)](https://litexlang.org)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Online Playground](https://img.shields.io/badge/Online%20Playground-darkgreen?logo=playground)](https://litexlang.org/playground)

</div>

## About The Adventure of Litex

_Science is what we understand well enough to explain to a computer; art is everything else._

_-- Donald Knuth_

_The best way to predict the future is to invent it._

_-- Alan Kay_

**Welcome to our [zulip community](https://litex.zulipchat.com) to get the latest updates and discuss with us.**

Litex is a simple and easy-to-learn formal language. It makes formal reasoning as natural as writing in natural language. Thanks to its innovative design philosophy, even 10-year-olds can learn Litex easily. This gives it a dimensional advantage over existing formal languages, such as Lean, which even PhD students struggle to master.

This is an adventure with two goals: 1. to make formal reasoning as intuitive as natural language and everyday thinking, from both high-level and low-level perspectives. 2. to spread the idea and power of formal reasoning to a larger audience.

By unifying how we express and verify reasoning (including math), Litex is poised to become the key infrastructure for scalable knowledge engineering in the AI era. In the field of AI, formal languages have become an indispensable tool for top researchers. Terence Tao uses them to reconstruct mathematical proofs, Bengio's team employs them to verify AI safety, DeepSeek-R1 leverages them to enhance reasoning capabilities, and the AlphaProof series utilizes them to simultaneously generate problems and answers, forming a self-improving closed loop.

Although still in its testing phase, leading institutions such as CMU, Mila, and Oxford have already begun exploring, testing, and experimenting with Litex. Investing in Litex is not just a bet on the future of this technological approach—it also unlocks vast opportunities in the commercialization of formalized datasets and language support services. The relentless engineering efforts of the Litex team will make all these possible.

Learn more in [tutorial](./doc/tutorial/tutorial.md). Download the latest version of Litex [here](https://github.com/litexlang/golitex/releases). Try Litex in your browser [here](https://litexlang.org/playground).

While Litex is in the early stages of development, it has already established a solid foundation that demonstrates the potential of this approach. Contributors read [contribute to Litex](./doc/contribute_to_Litex/contribute_to_Litex.md) for more details. **If you have any problems, please contact us through [Contact](#contact--contribute-to-litex) methods provided in this README.**

**NOTE: Litex is still under development. THE CREATOR OF LITEX IS LOOKING FOR LONG-TERM OR SHORT-TERM CONTRIBUTORS. READ [CONTRIBUTE TO LITEX](./doc/contribute_to_Litex/contribute_to_Litex.md) FOR MORE DETAILS.**

## Using Litex

_If I have seen further, it is by standing on the shoulders of giants._

_-- Isaac Newton_

_The only source of knowledge is experience._

_-- Albert Einstein_

**WARNING: Litex is still under development. Unexpected bugs might happen.**

This section is for you to try Litex step by step. If you just want to have a quick look at Litex, you can skip this section.

### Download Litex and Try It

#### Choice 1: Try Litex in your browser

Visit [Litex Playground](https://litexlang.org/playground) to try Litex in your browser.

#### Choice 2: Download the latest version of Litex to your machine

step 1: download latest version [release](https://github.com/litexlang/golitex/releases). It is a binary file, so you can just run it in your terminal.

step 2: run your downloaded binary file and enter the REPL (Read-Eval-Print Loop) mode of Litex. Try enter `1 + 1 = 2` and see what happens. Enter `exit` to quit the REPL mode.

If you are on Mac, you might need to give it permission to run. If it still does not work, input `chmod 777 YOUR_BINARY_FILE_NAME` in your terminal and try again.

step 3: `git clone https://github.com/litexlang/golitex.git` and run `YOUR_BINARY_FILE_NAME PATH_TO_YOUR_CLONED_REPO/examples/comprehensive_examples/syllogism.lix` in the root directory of the cloned repo. This will run the example code. Other examples (e.g. Hilbert geometry axioms formalization for experts, multivariate linear equation for children) are in the same directory. You can also input the code directly in the REPL mode.

Both choices are free. I recommend you to try Litex in your browser first, because it is much more convenient.

**SORRY THERE IS NO MORE EXAMPLES FOR NOW. I SINGLE-HANDEDLY DEVELOPED THE WHOLE LANGUAGE FOR 2800 GIT COMMITS. I HAVE ALREADY DONE MY BEST. THAT IS WHY I AM SO EXCITED TO HAVE YOU HERE.**

After having a sense of Litex, do this:

0. Read the [README](./README.md) to get a sense of the project.
1. Read the [tutorial](./doc/tutorial/tutorial.md) to get a sense of the language.
2. Read the [Litex for Curious Lean Users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md) to get a sense of the difference between Litex and Lean.
3. To learn applications of Litex, read [applications of formal reasoning in AI and many other fields](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md).
4. To read a comprehensive example, read [formalization of Hilbert geometry axioms](./examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix).
5. Contribute piece by piece to the Litex kernel or the Litex dataset, e.g. formalize mathematical concepts, fix bugs, add new features, improve documentation, etc. on [github](https://github.com/litexlang/golitex), [zulip](https://litex.zulipchat.com).

**IF YOU HAVE ANY PROBLEMS, PLEASE CONTACT THROUGH [zulip](https://litex.zulipchat.com) OR litexlang@outlook.com OR [github](https://github.com/litexlang/golitex).**

**THANK YOU FOR YOUR FEARLESS EARLY ADOPTION! HERE IS MY HEARTFELT THANKS TO Litex's EARLIEST FANS -- THE BOLD PIONEERS WHO TRUSTS ME FROM THE START!**

## A Simple Example

_Keep it simple, stupid._

_-- The Unix Philosophy_

_If you define the problem correctly, you almost have the solution._

_-- Steve Jobs_

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle, which formalizes deductive reasoning as follows:

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>obj Human set</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$self_aware(x)</code> <br> <br>
      <code>obj Bob Human</code> <br> <br>
      <code>$self_aware(Bob)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def self_aware (x : Human) : Prop := true</code> <br><br>
      <code>axiom self_aware_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), self_aware x</code> <br><br>
      <code>example (Bob : Human) : self_aware Bob := self_aware_all Bob</code>
    </td>
  </tr>
</table>

Consider `Human` as the set of all humans. Using `know`, we establish a simple fact: all humans are self-aware. Since Bob is in the set of `Human`, "Bob is self-aware" is true. This simple example shows how Litex builds math from basic pieces, like building blocks. Each statement in Litex has four potential outcomes: true, false, unknown, or error. All factual statements start with `$` to differentiate them from functions.

Notice how Litex is much simpler than Lean4. Instead of writing complex axioms with special names, you just use familiar words like `know` and `forall`. Litex automatically finds the facts it needs, just like searching in a database. Moreover, there are less unfamiliar keywords, less twisted syntax in Litex. People can understand Litex at first glance and say "oh, I already get this." instead of trying to figure out what this keyword or that syntax means. Users can focus more on math itself instead of the formal language they use. Litex's syntax is similar to Python and Go, so if you've done any programming, you'll feel right at home. See more in [Litex for Curious Lean Users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md), [tutorial](./doc/tutorial/tutorial.md).

## Understand Litex in 60 Seconds: The Core Idea of Match & Substitute

_All human knowledge begins with intuitions, thence passes to concepts and ends with ideas._

_-- Immanuel Kant_

_Mathematics is a game played according to certain simple rules with meaningless marks on paper._

_-- David Hilbert_

There are two things in math: objects and factual statements. Objects are the things that we are talking about, and factual statements are the statements about objects. Sets, functions, numbers, etc. are all objects. And factual statements are statements like "Jordan is intelligent", "1 < 2", "x = 1", etc. In Litex, a factual statement has four potential outcomes: true, false, unknown(not enough information to determine the truth value), or error(the statement is not well-formed). A fact is a statement that is true.

Math is built on top of a small sets of reasoning rules and axioms. There are basically two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

Think of "match and substitute" as a fancy version of "search and find" on your computer (ctrl+f on windows, cmd+f on mac). When Litex is verifying a given factual statement, it "finds" a related known general fact, "substitutes" it with the parameters of current statement, and the new fact is "matched" with the current statement. Then Litex verifies the new fact and stores it into its memory as known fact for future use.

Amazingly, with these two ways of deriving a new fact, and with a set of carefully chosen axioms, we can (nearly) build the entire world of mathematics. And you have ALREADY learned the basic mechanism of Litex in just one minute: **match and substitute**. Pretty simple, right?

All daily math is built around first-order-logic, naive set theory, natural numbers related axioms (mathematical induction, Peano axioms, extension to rational numbers and real numbers), and all of these are implemented in Litex. So it does not matter whether you are formalizing algebra or geometry or any other math, as long as you are clear about concepts and axioms of the math you are formalizing, you can use Litex to formalize it.

There are two major special cases of match and substitute:

1. about rational numbers, like 1, 3.5 or 4.123456789. These objects are different from user-defined objects because their literal representation directly encodes information and **match and substitute** is not enough to handle them. Rational numbers and their basic operations like addition, multiplication, inequalities are builtin in Litex, and Litex handles all the verification rules for them automatically. 

2. about counting and prove a universal fact on a finite set by iterating over the set. Again they are different because their literal representation directly encodes information and **match and substitute** is not enough to handle them. If a set has finite number of elements, we verify case by case to prove a universal fact on that set (for infinite sets, we can only use `forall` to express their properties.). Litex provides a special keywords to handle this case.

## The Secret behind Litex's Unique Design

_Cross the river by feeling the stones._

_-- Chinese Proverb_

_Simplicity is the ultimate sophistication._

_-- Leonardo da Vinci_

TL;DR: Traditional formal languages are programming languages. Code in Programming languages are for execution. Litex is a not a programming language, just as math is not a programming language. Verification of mathematical reasoning is done by matching and substituting, and that is exactly what Litex does. The user provides statements to deduce new facts from existing facts (that is what we call reasoning), and Litex is here to make sure every statement makes sense.

Everyone knows how to reason, including 10-year-old. We reason thousands of time every day without even noticing it. Yet, traditional formal languages, like Lean4, Coq, and Isebelle are so complex that even the smartest mathematicians find it hard to use. Why is that?

It turns out that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. 

If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

On the other hand, Litex is a formal language that operates as a Read-Only Turing Machine. By deliberately sacrificing Turing completeness, Litex focuses solely on mathematical verification. Unlike programming languages, Litex eliminates variables, control flow, and execution semantics - concepts that are foreign to pure mathematics. 

This design choice, similar to how SQL specializes in database operations, allows Litex to specialize in everyday math as much as possible. The language adopts Python-like syntax for accessibility.

Another important design choice is that the user does not need to give names to facts, because Litex can automatically find the matched facts it needs. It saves a lot of time and effort for the user. Read [tutorial](./doc/tutorial/tutorial.md) for more details.

Throughout the years, natural languages are [considerably more expressive than their formal mathematical counterparts](https://terrytao.wordpress.com/advice-on-writing-papers/take-advantage-of-the-english-language/). With Litex, we can finally make the best of both worlds.

Litex takes a use-driven, example-first approach to formalization. Instead of building on sophisticated theories, it evolves by trying to express real mathematical texts—like Tao’s *Analysis I* or Weil’s *Number Theory for Beginners*. When something is hard to formalize, Litex doesn’t force a fit; it grows new features to make expression natural. This trial-and-error, practice-guided development makes Litex uniquely adaptable and intuitive.

In a nutshell, Litex is for EVERYONE, from children to experts, to learn and use formal language at AI age. It scales up reasoning by making the process of writing formal reasoning as intuitive as writing in natural language.

This is a summary of the differences between Litex and Lean4.

| Feature       | Litex                | Lean4          |  
|--------------|---------------------|--------------|  
| Turing-complete | ❌ No               | ✅ Yes        |  
| Focus        | Math formalization  | Proof + Programming |  
| Syntax Style | Python-like         | Functional      |
| Learning Curve | Low (10-year-old friendly) | High (The prerequisites are very high even for PhD students) |
| Auto-fact Finding | ✅ Yes (automatic) | ❌ No (manual naming) |
| Type System  | Set theory + first-order logic | Complex (dependent types) |
| Built-in Math | ✅ Yes (rational numbers, basic operations) | ❌ No (requires libraries) |
| Community Size | Small (growing) | Large (established) |
| Production Ready | ❌ Not yet | ✅ Yes |

## Answers to Common Questions

_Given enough eyeballs, all bugs are shallow._

_-- Linus Torvalds_

Litex's growth is driven by the needs of its users. The users shape the language, not anyone else. If you have any ideas, please contact us through [zulip](https://litex.zulipchat.com) or litexlang@outlook.com.

1. Why is Litex poised for success now?

Litex represents an intellectual breakthrough in formal language design. The rapidly expanding AI industry presents the perfect opportunity, as it needs tools for ensuring AI safety, enhancing reasoning, and accelerating scientific discovery.

2. What makes Litex different from other formal languages?

Litex's greatest strength is its remarkable simplicity. While other formal languages require years of expertise to master, Litex is intuitive enough for children to learn, striking the perfect balance between power and accessibility.

3. How do I formalize concepts like uniform distribution over (0,1) or anything like that?

Think of formalization like reading a book - you need to understand the previous pages before the last one. Similarly, formalizing advanced concepts requires building up from fundamentals. For example, formalizing uniform distribution over (0,1) requires many prerequisites. The good news is that translating mathematical concepts to Litex is straightforward once you have the prerequisites in place.

4. Resources of Litex:

[Applications of Formal Reasoning in AI and Many Other Fields](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md)

[Tutorial](./doc/tutorial/tutorial.md)

[Formalization of Hilbert Geometry Axioms](./examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix)

[Litex for Curious Lean users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md)

[Website](https://litexlang.org)

[Github](https://github.com/litexlang/golitex)


##  Examples: Litex for Curious Lean Users

_Common sense is not so common._

_-- Voltaire_

_Beautiful is better than ugly. Explicit is better than implicit. Simple is better than complex._

_-- The Zen of Python_

Here are some examples of Litex, in Litex for Curious Lean Users4. Detailed explanations are provided in [Litex for Curious Lean Users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md). I put them here for you to get a sense of the language.

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
      <code>&nbsp;&nbsp;forall x Q:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;comp_seq(Q, f)(x,n) = f(comp_seq(Q, f)(x, n-1))</code><br><br>
      <code>exist_prop n N st exist_comp_seq_end(Q set, x Q, f fn(Q,N)Q):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;f(x, n) = f(x, n+1)</code><br><br>
      <code>prop is_algorithm(Q set, I set, f fn(Q)Q):</code><br>
      <code>&nbsp;&nbsp;$subset_of(I, Q)</code><br>
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

_Talent wins games, but teamwork and intelligence win championships._

_-- Michael Jordan_

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics and programming language enthusiast (a programming language geek, if you are one too, you are welcome to contact me). In 2023, I shockingly found that math is somehow equivalent to programming, after reading Professor Terence Tao's [blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/). This is the most amazing idea that I have ever seen in my life. In 2024, after thinking about it for a year, I started to implement Litex. After more than 2500 git commits, what it means to be a "formal language that is intuitive and as aligned with daily math expression as possible" is finally to make sense to me and my kernel sort of works now.

Litex is evolving from implementation to community-driven development. The interpreter is 90% complete and covers most daily math. However, it is still not ready for production use. Now, I face a big challenge: the conflict between an individual's limited capacity and the extensive demands of an open-source project. See more in [contribute to Litex](./doc/contribute_to_Litex/contribute_to_Litex.md) to help me grow the project.

You can contribute by:
1. Contributing to the interpreter or standard library
2. Creating datasets for AI training
3. Improving documentation
4. Exploring Litex's mathematical capabilities
5. Spreading the word about Litex
6. Building standard library of Litex
7. Creating the LitexDojo, similar to how LeanDojo is for Lean.

Since 90% of the functionality delivered now is better than 100% of it delivered never[^1], the inventor of Litex put it open-source to welcome everyone, including you, to learn, try, use, and contribute to Litex, even though Litex is not fully ready. Feel free to contact us and join this exciting journey!


- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
- **Litex Zulip Community:** [litex.zulipchat.com](https://litex.zulipchat.com)

[^1]: Kernighan & Plauger, The Elements of Programming Style, 1978.
