# The Litex Reference Manual

**Release v0.1.1-beta**  
*May 2025*  
*Created by Jiachen Shen*

This manual is a reference for Litex, written for potential contributors and users who want to understand how Litex works inside.

## Words from the Inventor

_The best way to predict the future is to invent it._

_-- Alan Kay_

I, Jiachen Shen, a hacker and a math enthusiast. I majored in math and self-taught programming. Also, I am a programming language geek. I have been working on Litex since 2024, and I am still working on it. I really like designing and engineering new languages.

A good art is what makes its creator happy and makes its users find it useful.[^1] I hope Litex can be a good art for both me and its users.

In the AI age, we are facing a paradigm shift from data-driven learning to formal-language-driven reinforcement learning. Traditional formal languages are too complex and too far removed from the expression habits of everyday mathematics. Litex is here to make formal language more accessible to everyone.

**NOTICE: Litex is still under active development. Contribution and early adoption is welcome!**

## Litex view of math

Math is built on top of a small sets of reasoning rules and axioms. There are basicly two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

OK, you have already known the basic idea of Litex.

Another group of reasoning rules are about real numbers, like 1, 3.5 or 4.123456789. These objects are different from the user-defined objects, as 1. their literal represenation contains information 2. it is impossible for the user to declare them one by one and must be builtin. Verification of these objects is done by builtin rules and the users do not need to worry about them.




---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com

## Design Principles of Litex

_That language is an instrument of Human reason, and not merely a medium for the expression of thought, is a truth generally admitted._

_–- George Boole_

[^1]: [Computer programming as an art](https://dl.acm.org/doi/10.1145/1283920.1283929)