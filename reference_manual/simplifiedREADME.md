# Litex: A Minimalist Proof Assistant

## About

_That language is an instrument of Human reason, and not merely a medium for the expression of thought._

_–- George Boole_

Litex is a minimalist proof assistant (formal language). Since even children grasp math naturally, a formal language design should exist that's easily understood and used by anyone. The goal of Litex is to invent such a language. The implementation approach leverages a profound understanding of the commonalities and distinctions between programming and mathematics.

Traditional proof assistants lack the fluidity and ease needed to scale formal proofs, while Litex handles the growing complexity of modern mathematics effectively through its well-designed syntax. Litex is designed to be as  intuitive as Python or LaTeX, with a minimal learning curve. Users can trust their common sense to write Litex.

Litex has the potential to greatly impact both mathematics and AI:

- **For Mathematics**: It simplifies complex proofs and ensures correctness, eliminating the need for paper reviews. This enables trust and large-scale collaboration, like a "GitHub for Math," and supports interactive math textbooks.

- **For AI**: It improves formal reasoning and proof automation, essential for AI training. Its simplicity will attract users, increasing the availability of formal datasets, which are currently limited.

In short, Litex can transform math collaboration and boost AI's reasoning with more formal data. The core of Litex is simplicity.

## Getting Started

_Mathematics... is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Let us begin with a quick introduction to Litex. Our aim is to show the essential elements of the language, but without getting bogged down in details, rules, and exceptions.

### Litex Expressions

Every expression of Litex has just four kinds of outcomes: true, false, unknown, error. 

- **True**: Litex confirms your expression based on known facts.

- **False**: Litex disproves your expression based on known facts.

- **Unknown**: Litex cannot find relevant facts to conclude.

- **Error**: Your input is incorrect, e.g., a typing mistake.

This mirrors how Humans think when reading proofs: confirming correctness (true), spotting errors (false), being unsure (unknown), or encountering input issues (error). 

Previous formal languages(proof assistants), such as Lean4 and Coq, are still general-purpose languages. They support execution, arithmetic, and control flow, which prevents their syntax from focusing solely on theorem proving and requires them to accommodate other functionalities. This results in highly redundant syntax.

Litex, free from execution constraints, functions like a regex matcher or SQL query processor, validating structured statements against formal rules. Adding unnecessary features would dilute its expressive power, that is why Litex expressions only have four outcomes. Execution in Litex is possible but delegated to plugins, not the language itself.


### First Example


<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>type Human</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x is self_aware</code> <br> <br>
      <code>var Bob Human</code> <br> <br>
      <code>Bob is self_aware</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def self_aware (x : Human) : Prop := true</code> <br><br>
      <code>axiom self_aware_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), self_aware x</code> <br><br>
      <code>def Bob : Human := Human</code> <br><br>
      <code>example : self_aware Bob := self_aware_all Bob</code>
    </td>
  </tr>
</table>

For now, you don't need to understand everything; you only need to conceptually know what it is doing. `Human` is a type representing all humans. Mathematically, you can think of `Human` as the set containing all humans. All humans are set to be `self_aware` by the user as a fact (i.e. true expression) using `know` keyword. `Bob` is `Human`. Therefore, `Bob is self_aware` is a true expression. This is a classic example of syllogism (三段论).

