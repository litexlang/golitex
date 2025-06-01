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

If you are a software developer, or mathematician, or an AI researcher, you might have encountered formal languages. Formal languages are softwares where, people write down their reasoning without breaking the rules of the language, and the software will check if the reasoning are valid accordingly. It works like how a human checks whether a piece of math is correct, but in a more strict and automated way. Just like nobody can calculate faster than a calculator, it can be imagined that nobody can check the validity of reasoning faster than a formal language.

However, traditional formal verification languages like Lean4, Coq, and Isabelle are too complex and too far removed from everyday mathematical notation. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later. The fundamental reason for this complexity is that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

That is why Litex chooses not to be a programming language, making it in first principle different from other traditional formal lanuages. (Technically, Litex is a Read-Only Turing Machine, instead of a Turing Machine.) It is designed to be simple and intuitive. No brain-exploding theories, no complex syntax, no need to learn a new programming language. All you need to learn before using Litex is building a connection between your own intuition and Litex expressions. Believe me, that is pretty easy. You will find the process of mathematical verification is nothing more than "match and substitute". Many mathematical expressions can be translated from natural language to Litex code almost directly. 

Maybe you are a young teenager captivated by mathematics, eager to master the art of deductive reasoning and rigorous thinking, just like the ancient philosophers such as Plato or the brilliant detective Sherlock Holmes.

Maybe you are an AI researcher striving to develop reasoning models that can match or surpass human cognitive abilities. Formal mathematical data could enhance your model's reasoning capabilities and perhaps inspire the next breakthrough in model architecture.

Maybe you are a mathematics student seeking to streamline the paper review process, identify potential errors in your thesis, and collaborate with fellow mathematicians online - much like how programmers collaborate through platforms like GitHub.

Maybe you are a rocket scientist who needs absolute certainty in every mathematical formula, ensuring your spacecraft's precise trajectory to the moon.

Maybe you are simply an enthusiast who finds joy in appreciating the elegance of mathematics and discovering how individual concepts intertwine to create a magnificent tapestry of knowledge.

Litex is the perfect language for you. I hope you will enjoy it.

**NOTICE: Litex is still under active development. Contribution and early adoption is welcome!**

## Litex view of math

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Math is built on top of a small sets of reasoning rules and axioms. There are basicly two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

OK, you have already known the basic idea of Litex.

Another group of reasoning rules are about real numbers, like 1, 3.5 or 4.123456789. These objects are different from the user-defined objects, as 1. their literal represenation contains information 2. it is impossible for the user to declare them one by one and must be builtin. Verification of these objects is done by builtin rules and the users do not need to worry about them.

## Difference Between A Programming Language and Math

There are several examples of major differences between a programming language and math:

1. There is no variable in math. Every object in math is determined once it is defined. Yet an object might change its value in programming languages.

2. There is control flow in math. "for i in range(1000)" never exists in any math proof. Nobody iterates 1000 thousand of times in his brain to prove a statement. Instead, he uses keyword "forall" to express the same meaning.

3. A function in programming is for execution, yet in math a function is just a symbol which takes in other symbols as parameters and forms a new symbol. There is no execution of function in math. All is verification.

It turns out that traditional formal languages, like Lean4, Coq, and Isabelle, attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

The huge difference between math or reasoning in general and programming languages is why Litex is not designed to be a programming language, making it in first principle different from other traditional formal lanuages. Technically, Litex is a Read-Only Turing Machine, instead of a Turing Machine.

Litex sacrifices Turing completeness to focus exclusively on mathematical verification, adopting a Python-like syntax for ease of use and LaTeX-like elegance for mathematical expression (similar to how SQL sacrifices completeness to specialize in database logic). This makes Litex accessible not only to professional mathematicians but also to beginners. 

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com

## Design Principles of Litex

_Keep it simple, stupid._

_-- The Unix Philosophy_

_Language design is a curious mixture of grand ideas and fiddly details._

_-- Bjarne Stroustrup, inventor of C++_

Litex is a minimalist proof assistant, designed to be simple and intuitive. It draws inspiration from various programming languages, particularly Go, Lisp, Tex, C, Python. Litex embrace simplicity, the only way to be flexible enough for the unknown future and to maintain conceptual integrity, as its core design principle.

Inheritance (C++/Java-style) is a poor fit for Litex:

Inflexible – Inheritance hierarchies are rigid, making extension and evolution difficult, which is common in other proof assistants.

Layer freedom – Users should begin at any abstraction level, not forced from low-level math, which is more aligned with mathematical discovery in R life.

Not Intuitive – Inheritance is not intuitive. An object can for sure belong to multiple sets, but in inheritance, an object can only belong to one type (or belong to a fixed part of inheritance hierarchy).

(In fact, GoLang is so well-designed and Litex learns so much from it, that Litex chooses GoLang to implement itself.)

Beyond Go, Litex draws inspiration from other programming languages. For instance, Python's scoping rules have shaped Litex's approach to object and function scope. 

The C programming language's syntax and semantics significantly influenced Litex's design. Operator overloading behavior is inspired by C++. The inventor of Litex holds a deep appreciation for Lisp's "everything is a list" philosophy, which contributes to the language's conceptual integrity. Also, since C uses postfix like L to make number as type the user want to overloade type of a numbner literal(e.g. 1L represents a long integer), Litex uses postfix to do type inference(e.g. 1r represents 1 as R number). No user defined type overloading is allowed.

(Syntactically, Litex learn from python and go. Semantically, Litex learn from Lisp, C and awk. As a daily tool, Litex learn from Tex and ipynb. Litex design principle is a mixture of all of them.)

Furthermore, Tex's clear distinction between "math expressions" and "plain words" inspired Litex's separation of "factual expressions" from ordinary symbols. Litex also aspires to achieve the same level of ubiquity and utility as Tex, aiming to become a widely adopted daily tool. This ambition is encapsulated in its name: Litex = Lisp + Tex, symbolizing the fusion of Lisp's expressive elegance and Tex's practicality.

The best to test Litex is by translating "real-world" into Litex. I use Professor Terrence Tao's Analysis I and II to test Litex. The set theory chapter of Analysis I helps a lot to remind me what functionalities are missing at each stage of implementing Litex.

The user can divide the problem into indenpent tasks and store them in different packages to make execution faster.

*The Litex interpreter basically takes the top-down approach to verify a fact, which means it basicly start from proposition and try to find a fact that can be used to prove the proposition, instead of coming from the bottom up, from related symbols to derive new facts and then use them to prove the proposition.*

There are many "design balences" in Litex. Math is so common that anybody has some basic knowledge of it. On the other hand, some branch of math can be so hard that only experts can understand. So there is a very huge gap between two groups of Litex users: innocent non-professionals, AI researchers who know some math, and math experts. What they want Litex to be is different. Since Litex is a pragmatic language and I wish it could have as many users as possible, any time I encounter those "hard choices", I always put the innocent group of users' demand first.

Litex is fundamentally a read-only Turing machine. Once any fact is stored, it can not be removed or changed. The amount of data stored in memory is in porpotion to the amount of code that the user write. Such design makes Litex align with everyday math.

Litex gets its name from Lisp and Tex. Lisp is a programming language that is very close to math. Tex is a typesetting system that is very close to math. Both of them greatly inspired Litex, making Litex also a formal language that is very close to math.

Litex intentionally has few keywords and minimal syntax sugar to encourage consistent programming habits - there should be only one way to express a given logic. This makes code more readable and prevents users from getting overwhelmed by too many expression choices.

## Conclusion

_That language is an instrument of Human reason, and not merely a medium for the expression of thought, is a truth generally admitted._

_–- George Boole_

## The Problem Litex Solves

_If you define the problem correctly, you almost have the solution._

_-- Steve Jobs_

As you can see, mathematics is the science of abstraction, and computer science is science of abstraction. Litex bridges the two, scaling mathematical reasoning with software engineering principles. It lets users divide and conquer proofs — just as programmers manage software complexity — ushering math into the computational age. No extra complexity is between you, your proof, and your thoughts.

Fields medalist Terence Tao shows great interest in the combination of formal languages and AI. When asked about formalizing everything in formal language, he said: "So I think the smarter thing to do in many cases is just to wait until it's easier. Instead of taking 10 times as long to formalize it, it takes two times as long as the conventional way."[[AI will become mathematicians' co-pilot](https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/)] Litex is my answer to this challenge. I hope you and many others can join the Litex community to make this happen.



[^1]: [Computer programming as an art](https://dl.acm.org/doi/10.1145/1283920.1283929)