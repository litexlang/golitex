# Contribute to Litex

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

## Challenge of Litex

_Common sense is not so common._

_-- Voltaire_

The **match and substitute**, which is the basic way of reasoning in math, is actually a very interesting and fundamental way of understanding what math actually is. Throughout centuries, the definition of math is always changing, different mathematicians and philosophers have different opinions on what it is. If math is truly a game of **match and substitute**, with just a few exceptions like counting and natural numbers, then it is technically possible to formalize all math in Litex. If not, then Litex semantics needs extra features. 

Moreover, giving semantics to keywords like **prop** or **in** is actually very tricky for Litex, because people just assume what they mean and do not think about the underlying mechanism and the Litex creator has to think about it by himself. This is the major challenge of Litex.

One major challenge is that I require less functionality than a Turing machine. I only need enough syntax and semantics to express mathematics, which allows the language to be much more concise. However, deciding which features to remove from a Turing-complete system (or from typical programming languages like Python), and which to retain in order to correctly express mathematics, is a serious problem.

Fortunately, Litex has translated a vast amount of mathematical material, and there has never been a case where the logic could not be expressed. Empirically, the user does not need to worry about this.

## Evolution and Development of Litex

_Cross the river by feeling the stones._

_-- Chinese Proverb_

_Quantity changes lead to quality changes._

_-- Hegel_

_Worse is better._

_-- A Famous Software Development Proverb_

_Estimated number of users of C++ is 1 in 1979, 16 in 1980, 38 in 1981, 85 in 1982, ..., 150000 in 1990, 400000 in 1991. In other words, the C++ user population doubled every 7.5 months or so._

_-- Bjarne Stroustrup, A History of C++: 1979-1991_

Litex takes a use-driven, example-first approach to formalization. Instead of building on sophisticated theories, at its invention stage, the creator of Litex evolves it by trying to express real mathematical texts, like Tao's *Analysis I* or Weil's *Number Theory for Beginners* in Litex. When something is hard or impossible to formalize using existing features, it grows new language features (syntactically and semantically) to make expression natural. Any time the creator of Litex feels that the language is not expressive enough, he will add new features to make it more expressive. 

Sometimes the new feature covers the functionalities of the old one and the old one is replaced by the new one. This trial-and-error, practice-guided development makes Litex uniquely adaptable and intuitive. Any feature is added with careful test about whether it is as useful and intuitive as possible and whether it is not harmful to the existing features. In most cases, a feature either works as a syntactic sugar which significantly improves the readability and writing experience of the code, or it is a new feature that is necessary for the user to express certain types of logic.

Litex is designed to serve users. It is not an academic experiment to design the perfect formal language. It is a practical tool to help users formalize their math, train their AI models, and other tasks. Thus to fulfill its mission, Litex has to grow with its users. 

Litex development follows the humble [worse is better](https://www.dreamsongs.com/RiseOfWorseIsBetter.html) philosophy. Think about it: JavaScript made every mistake in its design as a programming language while it did everything right to make itself one of the most influential programming languages in the world by serving its users' most urgent needs: the language of the Internet. Litex is not perfect, but it is pragmatic enough.

It's hard to know how to implement Litex. It's even harder to know what to implement, how different language features work together with one another. Since Litex is so different, the creator of Litex has to try to implement it by trial-and-error instead of following any existing theories or just mimicking existing formal languages. Litex is rooted in its unique and simple (However, this simplicity is not easy to achieve.) ideas, not theories.

The creator of Litex wishes Litex to obtain adoption exponentially, like C++ and other programming languages did. It does not need a glorious beginning, but it needs a strong engine to grow. Compared with potential number of users of formal languages, all traditional formal languages are tiny. Litex wants to change that.

That is why Litex really needs YOUR help: to use it, to spread the word about it, to contribute to it, to improve it, to make it better.

## Join My Journey

Litex is an ambitious project with a clear vision: to create a simple, intuitive, and powerful formal language for mathematics. While we're in the early stages of development, we've already established a solid foundation that demonstrates the potential of this approach. Like a promising startup, we're building something that could fundamentally change how we think about and work with mathematical formalization.

## Difficulties I Face

This challenge I faced can be summarized as: **The conflict between an individual's limited capacity and the extensive demands of an open-source project** (or, more broadly, **a mismatch between a solo developer's resources and the requirements of a systemic engineering effort**).  

Specifically, it manifests as:  
1. **Individual capability vs. team-based development**:  
   Projects like Litex typically require teamwork (development, testing, maintenance, promotion, etc.), but the author is an independent developer and PhD student with limited time and resources, making it difficult to balance academic work and the open-source project.  

2. **Innovation vs. sustained effort**:  
   Designing the core syntax (intellectual creation) can be achieved by an individual, but subsequent engineering, ecosystem building, and maintenance require long-term systematic effort—far beyond what one person can handle.  

3. **Academic pressure vs. open-source ideals**:  
   Fully committing to Litex could lead to failing to graduate (a real-world survival issue), but abandoning it would stall the project (a clash between ideals and reality).  

At its core, this is a contradiction between **"individual heroism" and "collective collaboration,"** a classic dilemma faced by many independent developers and researchers.

**If you can help me solve this contradiction, no matter how small, you are welcome to contact me.**

## Difficulties You Face

Litex is still in the early stage of development, I do not want to underestimate the difficulty of the task. There are 2 main challenges for you to formalize mathematical concepts in Litex, or contribute to the Litex kernel:

- The language is still unstable, there might be some bugs or insufficiencies in the language design.
- There is very little existing code for Litex, so you need to formalize a lot of mathematical concepts from scratch.

If you are still willing to try, then you are one of the brave ones who dared to believe. I recommend you to start with the following steps:

0. Read the [README](../README.md) to get a sense of the project.
1. Read the [tutorial](../tutorial/tutorial.md) to get a sense of the language.
2. Read the [Litex for Curious Lean Users](../litex_for_curious_lean_users/litex_for_curious_lean_users.md) to get a sense of the difference between Litex and Lean.
3. Contribute piece by piece to the Litex kernel or the Litex dataset, e.g. formalize mathematical concepts, fix bugs, add new features, improve documentation, etc.

**THANK YOU FOR YOUR FEARLESS EARLY ADOPTION! HERE IS MY HEARTFELT THANKS TO Litex's EARLIEST FANS -- THE BOLD PIONEERS WHO TRUSTS ME FROM THE START!**

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
- **Litex Zulip Community:** [litex.zulipchat.com](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)

## Why Contribute?

Litex represents a unique opportunity to be part of something groundbreaking. By contributing, you'll be:
- Shaping the future of mathematical formalization
- Working on a project that bridges the gap between traditional mathematics and modern computing
- Helping create tools that could revolutionize how AI systems understand and work with mathematics
- Building a community that values simplicity and intuition in mathematical expression

## How You Can Help

We welcome contributors from all backgrounds - whether you're a programmer, mathematician, AI researcher, or simply passionate about making mathematics more accessible. Here are some ways you can contribute:

### 1. Core Development
- Report bugs and suggest features
- Help improve the language design
- Contribute to the compiler and runtime
- Enhance documentation and tutorials

### 2. Mathematical Formalization (Litex dataset)
- Formalize mathematical concepts from textbooks (WARNING: This is a very hard task, since it requires a deep understanding of the mathematical concepts and the ability to express them in such an unstable formal language like Litex. However, it is still recommended to try to formalize them piece by piece)
    - For example, formalize Terrence Tao's [Analysis I](https://tiu-edu.uz/media/books/2024/05/28/1664976801.pdf), which since the beginning of Litex has been the example that I use to test my syntax. By coincidence, Tao himself has launched a project to [formalize Analysis I in Lean](https://github.com/teorth/analysis). It will be very interesting to see how the two languages compare.
    - You can also help to formalize math dataset, e.g. [mini2f2](https://huggingface.co/datasets/cat-searcher/minif2f-lean4), [minif2f-solutions of DeepSeek-Prover-V2](https://github.com/deepseek-ai/DeepSeek-Prover-V2), [formal conjectures](https://github.com/google-deepmind/formal-conjectures), [gsm8k](https://huggingface.co/datasets/openai/gsm8k), [MetaMathQA](https://huggingface.co/datasets/meta-math/MetaMathQA), [DAPO-Math](https://huggingface.co/datasets/YouJiacheng/DAPO-Math-17k-dedup), [orz_math_57k](https://huggingface.co/datasets/Open-Reasoner-Zero/orz_math_57k_collection), [prm800k](https://huggingface.co/datasets/tasksource/PRM800K), [DeepMath-103K](https://arxiv.org/html/2504.11456v1)
    - Some recommended math textbooks to formalize: [The Foundations of Geometry by Hilbert](https://math.berkeley.edu/~wodzicki/160/Hilbert.pdf), [Concrete Mathematics](https://seriouscomputerist.atariverse.com/media/pdf/book/Concrete%20Mathematics.pdf), [Combinatorial Mathematics by Douglas West](https://dokumen.pub/combinatorial-mathematics-1107058589-9781107058583.html) , [Algebra by Michael Artin](https://gregoryberry.net/wp-content/uploads/2024/01/Artin-Algebra.pdf), [Analysis by Terence Tao](https://tiu-edu.uz/media/books/2024/05/28/1664976801.pdf), [Linear Algebra Done Right by Sheldon Axler](https://linear.axler.net/LADR4e.pdf), Number Theory For Beginners By Andrew Weil (There is a channel on our Zulip community https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/ for discussions about formalization of this book), [Topology by James Munkres](https://eclass.uoa.gr/modules/document/file.php/MATH707/James%20R.%20Munkres%20Topology%20%20Prentice%20Hall%2C%20Incorporated%2C%202000%20by%20James%20R.%20Munkres%20%28z-lib.org%29.pdf), [Differential Geometry of Curves and Surface](https://docenti.ing.unipi.it/griff/files/dC.pdf)
- Convert mathematical papers into Litex
- Create example proofs and derivations
- Help build a comprehensive mathematical library

### 3. Tool Development
- Create IDE extensions (VSCode, etc.)
- Develop visualization tools
- Build web-based interfaces
- Design educational materials
- Create tools similar to LeanDojo, helping AI agents learn Litex

### 4. Community Building
- Share your experiences with Litex
- Write blog posts and tutorials
- Help others learn the language
- Participate in discussions about language design

## Why Your Contribution Matters

Every contribution, no matter how small, helps Litex grow stronger. By formalizing mathematical concepts in Litex, you'll help us:
- Identify and fix language design issues
- Discover new features and improvements
- Create a rich library of examples
- Build a foundation for AI training and research

## Getting Started

The best way to start contributing is to try formalizing something you're familiar with - whether it's a mathematical concept, a proof, or an algorithm. Your unique perspective and expertise can help shape Litex into a more powerful and versatile tool.

Join us in this exciting journey to make mathematics more accessible, intuitive, and powerful. Together, we can build something that could transform how we think about and work with mathematical formalization.


