# Litex: A Minimalist Proof Assistant

## About

_That language is an instrument of human reason, and not merely a medium for the expression of thought._

_–- George Boole_

Litex is a minimalist proof assistant (formal language). Since even children grasp math naturally, a formal language design should exist that's easily understood and used by anyone. The goal of Litex is to invent such a language. The implementation approach leverages a profound understanding of the commonalities and distinctions between programming and mathematics.

Traditional proof assistants lack the fluidity and ease needed to scale formal proofs, while Litex handles the growing complexity of modern mathematics effectively through its well-designed syntax. Litex is designed to be as  intuitive as Python or LaTeX, with a minimal learning curve. Users can trust their common sense to write Litex.

Litex has the potential to greatly impact both mathematics and AI:

- **For Mathematics**: It simplifies complex proofs and ensures correctness, eliminating the need for paper reviews. This enables trust and large-scale collaboration, like a "GitHub for Math," and supports interactive math textbooks.

- **For AI**: It improves formal reasoning and proof automation, essential for AI training. Its simplicity will attract users, increasing the availability of formal datasets, which are currently limited.

In short, Litex can transform math collaboration and boost AI's reasoning with more formal data. The core of Litex is simplicity.

## A Tour of Litex

_Mathematics... is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Let us begin with a quick introduction to Litex. Our aim is to show the essential elements of the language, but without getting bogged down in details, rules, and exceptions.

### Getting started

Every expression of Litex has just four kinds of outcomes: true, false, unknown, error. 

- **True**: Litex confirms your expression based on known facts.

- **False**: Litex disproves your expression based on known facts.

- **Unknown**: Litex cannot find relevant facts to conclude.

- **Error**: Your input is incorrect, e.g., a typing mistake.

This mirrors how humans think when reading proofs: confirming correctness (true), spotting errors (false), being unsure (unknown), or encountering input issues (error). 

Previous formal languages, such as Lean4 and Coq, are still general-purpose languages. They support execution, arithmetic, and control flow, which prevents their syntax from focusing solely on theorem proving and requires them to accommodate other functionalities. This results in highly redundant syntax.

Litex, free from execution constraints, functions like a regex matcher or SQL query processor, validating structured statements against formal rules. Adding unnecessary features would dilute its expressive power, that is why Litex expressions only have four outcomes. Execution in Litex is possible but delegated to plugins, not the language itself.