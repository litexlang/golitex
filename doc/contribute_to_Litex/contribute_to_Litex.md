# Contribute to Litex

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
- **Litex Zulip Community:** [litex.zulipchat.com](https://litex.zulipchat.com)

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
    - Some recommended math textbooks to formalize: [The Foundations of Geometry by Hilbert](https://math.berkeley.edu/~wodzicki/160/Hilbert.pdf), [Concrete Mathematics](https://seriouscomputerist.atariverse.com/media/pdf/book/Concrete%20Mathematics.pdf), [Combinatorial Mathematics by Douglas West](https://dokumen.pub/combinatorial-mathematics-1107058589-9781107058583.html) , [Algebra by Michael Artin](https://gregoryberry.net/wp-content/uploads/2024/01/Artin-Algebra.pdf), [Analysis by Terence Tao](https://tiu-edu.uz/media/books/2024/05/28/1664976801.pdf), [Linear Algebra Done Right by Sheldon Axler](https://linear.axler.net/LADR4e.pdf), Number Theory For Beginners By Andrew Weil (There is a channel on our Zulip community https://litex.zulipchat.com for discussions about formalization of this book), [Topology by James Munkres](https://eclass.uoa.gr/modules/document/file.php/MATH707/James%20R.%20Munkres%20Topology%20%20Prentice%20Hall%2C%20Incorporated%2C%202000%20by%20James%20R.%20Munkres%20%28z-lib.org%29.pdf), [Differential Geometry of Curves and Surface](https://docenti.ing.unipi.it/griff/files/dC.pdf)
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


