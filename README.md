<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**Release v0.0.1-beta**  
*May 2025*  
*Created by Jiachen Shen*

</div>

Litex is a powerful yet easy-to-learn formal language. At its core, it is a tool that enables you to express reasoning following Litex's defined rules, while automatically verifying the correctness of your reasoning. This makes it particularly valuable for validating mathematical proofs and other rule-based systems. Unlike other formal languages that even experienced mathematicians find challenging to use, Litex recognizes that reasoning is an innate human capability - even a 5-year-old possesses basic reasoning instincts. Our mission is to make formal reasoning accessible to everyone. 

In essence, Litex represents an ambitious attempt to scale reasoning capabilities in the AI age:

**Scaling means engineering:** Like software engineering, Litex transforms individual math work into mathematical engineering through better abstraction and composition. Every mathematical concept is rigorously defined, leaving no room for ambiguity or hidden errors, while remaining concise and clear. This transitions mathematics from artisanal craft to scalable industry.

**Scaling means more people involved:** Given that Litex is orders of magnitude more concise than other formal languages, we anticipate orders of magnitude more people joining the Litex community, potentially even establishing GitHub-style collaborative development for formalized reasoning. Even children can use Litex to learn math.

**Scaling means more mathematical discovery:** Auto-formalization is emerging as a promising approach for AI to learn general-purpose reasoning and achieve AGI. Rather than having a mathematician spend a day solving a single problem, it's more efficient to enable a large model to solve 10,000 problems in one second. Litex provides the ideal infrastructure for this paradigm shift.

Mathematicians including Fields medalist Terrence Tao, world-class AI companies including DeepMind and DeepSeek, are showing great interest in the combination of formal languages and AI. Litex is my answer to this challenge. Litex has already garnered attention from leading institutions worldwide, including **CMU, Tsinghua, Peking University, Pujiang Lab, Shanghai Jiao Tong University, Fudan University**.  

## Uniqueness of Litex

Everyone have started to think and reason since childhood. We reason thousands of time every day without even noticing it. Yet, traditional formal languages, like Lean4, Coq, and Isebelle are so complex that even the smartest mathematicians find it hard to use. Why is that?

It turns out that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

There are several examples of major differences between a programming language and math:

1. There is no variable in math. Every object in math is determined once it is defined. Yet an object might change its value in programming languages.

2. There is control flow in math. "for i in range(1000)" never exists in any math proof. Nobody iterates 1000 thousand of times in his brain to prove a statement. Instead, he uses keyword "forall" to express the same meaning.

3. A function in programming is for execution, yet in math a function is just a symbol which takes in other symbols as parameters and forms a new symbol. There is no execution of function in math. All is verification.

The huge difference between math or reasoning in general and programming languages is why Litex is not designed to be a programming language, making it in first principle different from other traditional formal lanuages. Technically, Litex is a Read-Only Turing Machine, instead of a Turing Machine.

Litex sacrifices Turing completeness to focus exclusively on mathematical verification, adopting a Python-like syntax for ease of use and LaTeX-like elegance for mathematical expression (similar to how SQL sacrifices completeness to specialize in database logic). This makes Litex accessible not only to professional mathematicians but also to beginners. 

With a small set of reasoning rules and axioms, we human beings are able to build the entire world of mathematics and apply them in everyday life. That is why in Litex, there are not that many keywords and language rules. Keeping Litex small and intuitive helps it keep  aligned with how reasoning actually works. The more you understand how Litex relates to your daily reasoning, the better you'll learn it.

More importantly, Litex’s clean syntax and structured representation make it an ideal training dataset for AI reasoning, helping AI models develop more reliable mathematical reasoning capabilities.

In a nutshell, Litex is for EVERYONE, from children to experts. It scales up reasoning by making the process of writing formal reasoning as intuitive as writing in natural language.

## Resources

[Tutorial](./doc/tutorial/tutorial.md)

[Formalization of Hilbert Geometry Axioms](./examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix)

[Compare Litex with Lean](./doc/comparison_with_lean/comparison_with_lean.md)

[Website](https://litexlang.org)

[Github](https://github.com/litexlang/golitex)


## Words From The Inventor

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics, and I am also a programming language geek. I have been working on Litex since 2024 and received many valuable feedbacks from Litex enthusiasts. I hope you enjoy using Litex, too. 

For the time being (2025-05), Litex is evovling from the stage of figuring out and implementing the idea of a simple formal language, to the stage of community-driven development and user-adoption. It will be long and interesting journey, feel free to contact us.

**NOTICE: Litex is still under active development. Contribution and early adoption is welcome!**

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
