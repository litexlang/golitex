<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**version v0.1.10-beta (not yet ready for production use)**  
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

[![Click Me To Try Litex On Online Playground](https://img.shields.io/badge/Click_Here_To_Try_Litex_On_Online_Playground-%E2%86%92_Explore-FF6B6B?style=for-the-badge)](https://litexlang.org/playground)

**Litex is an intuitive and scalable formal language for coding your reasoning. It ensures all steps of your reasoning are correct. We assume a man without any math or programming background can start using Litex after 1-2 hours of learning.**

**Formal language makes the process of writing math into a process of writing code. This is a very powerful idea, because code means automation without human intervention, large-scale collaboration, standardization, etc. The tedious process of verifying a piece of reasoning (e.g. a proof of a mathematical theorem) is now automated.**

**Computers have revolutionized how we calculate. With the combined power of AI (generate unverified reasoning automatically) and formal language (verify reasoning automatically), we are now entering a new era of automated reasoning. AI researchers are now using formal languages to build better and safer models.**

**However, traditional formal languages are too complex for non-technical users. AI researchers, mathematicians are calling for a new formal language to boost their job. Fundamentally, since a 10-year-old can reason about basic math by following specific rules, and using a formal language is nothing more than using such set of rules to reason, everyone should be able to learn formal language easily.**

**If you have the above problems, Litex is the perfect language for you. It is such a simple language that lowers the bar and cost of using formal language by 10 times. This simplicity and accessibility of Litex reduces the time ratio, between formalizing a proof and writing it in natural language, from 10:1 to 1:1. That is why constructing Litex codebase is 10x cheaper and has a 10x lower entrance barrier than traditional formal languages. This is a blessing for both AI industry and math community.**

## Different ways to run Litex

_Keep it simple, stupid._

_-- The Unix Philosophy_

Litex provides you with many ways to run Litex, I hope there is one that suits you.

- Run Litex in Web Browser
- Run Litex locally
- Run Litex in Python
- Run Litex in Jupyter Notebook

...

Visit [Start](https://litexlang.org/doc/Start) to get started.

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
      <code>know forall x Human => $intelligent(x)</code> <br><br>
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

## Contact & Contribute to Litex

_The people who are crazy enough to think they can change the world are the ones who do._

_-- Steve Jobs_

_The best way to predict the future is to invent it._

_-- Alan Kay_

Hello, my friend, this is Jiachen Shen, creator of Litex. I welcome you to join the Litex community and grow with Litex together.

As Arabic numbers transforms the world of math by its clean and concise expression, Litex aims to transform the world of math by its intuitive and natural expression using formal language. Giving semantics to keywords and syntax to Litex and at the same time making what it means as aligned with daily math expression as possible, is the major challenge of Litex. This is a long journey, but I am trying my best to make it happen.

Currently, our work on Litex focuses on several key directions:

Standard Library of Litex – so that users can directly access existing facts and mathematical concepts, rather than starting entirely from scratch.

Dataset of Litex – including the translation of short mathematical problems ranging from elementary school to undergraduate level.

Advanced Dataset – covering IMO problems, university textbooks, and mathematical research papers.

Inconvenience Detection – there are still many small bugs and usability issues across the Litex toolchain; if you encounter any of them, please let us know.

Documentation of Litex – documentation is the very first step for new users to get in touch with Litex. The first impression matters a lot, so we must ensure that our documentation is clear, polished, and welcoming.

Litex + AI – this is closely tied to the dataset. Litex’s ultimate goal is to scale formal reasoning in the AI age, and embedding Litex into AI workflows is therefore an essential and intrinsic direction.

If you are interested in any of those topics, please contact me through [email](mailto:litexlang@outlook.com) or join the [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/).