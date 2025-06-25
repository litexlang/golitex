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

## Litex's Unique Design

_Simplicity is the ultimate sophistication._

_-- Leonardo da Vinci_

_Science is what we understand well enough to explain to a computer; art is everything else._

_-- Donald Knuth_

TL;DR: Traditional formal languages are programming languages. Code in Programming languages are for execution. Litex is a not a programming language, just as math is not a programming language. Verification of mathematical reasoning is done by matching and substituting, and that is exactly what Litex does. The user provides statements to deduce new facts from existing facts (that is what we call reasoning), and Litex is here to make sure every statement makes sense. This is the secret behind Litex's accomplishment of reducing the time ratio between formalizing a proof and writing it in natural language from 10:1 to 1:1.

Everyone knows how to reason, including 10-year-old. We reason thousands of time every day without even noticing it. Yet, traditional formal languages, like Lean4, Coq, and Isebelle are so complex that even the smartest mathematicians find it hard to use. Why is that?

It turns out that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. There are good points in making a prover a programming language, because it hands to duty of tackling with tricky details of math to the user and the user can have enough freedom to do whatever he wants. But this is very hard for beginners.

If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

On the other hand, Litex is a formal language that operates as a Read-Only Turing Machine. By deliberately sacrificing Turing completeness, Litex focuses solely on mathematical verification. Unlike programming languages, Litex eliminates variables, control flow, and execution semantics - concepts that are foreign to pure mathematics. By carefully choosing what to include and what to exclude, Litex is able to be as simple as possible.

This design choice, similar to how SQL specializes in database operations, allows Litex to specialize in everyday math as much as possible. The language adopts Python-like syntax for accessibility. To be more specific, Litex is a domain specific language for formal reasoning.

Another important design choice is that the user does not need to give names to facts, because Litex can automatically find the matched facts it needs. It saves a lot of time and effort for the user. Read [tutorial](./doc/tutorial/tutorial.md) for more details.

Throughout the years, natural languages are [considerably more expressive than their formal mathematical counterparts](https://terrytao.wordpress.com/advice-on-writing-papers/take-advantage-of-the-english-language/). With Litex, we can finally make the best of both worlds.

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
| Translation to Natural Language | ✅ Easy and natural | ❌ Difficult and indirect |
| Production Ready | ❌ Not yet | ✅ Yes |
