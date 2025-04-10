# Litex: A Minimalist Proof Assistant

<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

## About

_That language is an instrument of Human reason, and not merely a medium for the expression of thought, is a truth generally admitted._

_–- George Boole_

Litex is a minimalist proof assistant (formal language). With a predicted "de Bruijn factor" (the ratio of formal to informal proof difficulty) of 0.5–1.5, Litex will transform the mathematical landscape and help build better reasoning AI models.

Since even children grasp math logically and naturally, a formal language for mathematics intuitive and accessible to all can be invented. Litex aims to create such a language. Designed to be as intuitive as Python and LaTeX, Litex offers a minimal learning curve.

Litex is unique in two ways, compared with traditional proof assistants. First, it focuses solely on mathematical verification, whereas traditional proof assistants are general-purpose programming languages that introduce unrelated complexities. Second, Litex is built around common sense rather than sophisticated mathematical theories.

The potential impacts of Litex include: enabling proof verification (including LLM-generated outputs), revolutionizing proof writing and review, facilitating large-scale collaborations, creating datasets for LLM training, and enhancing LLM reasoning capabilities. With its inherently simple syntax, Litex is well-positioned to achieve these goals and attract a growing community of researchers to the world of formal languages.

Mathematics is fundamentally about abstraction, and computer science is the discipline that studies abstraction. At its core, all other impacts of Litex are extensions of this foundational idea. Technically, Litex = math + programming language + data base. The ultimate goal of Litex is to harness programming concepts and tools to tackle challenges in mathematics, making the elegance of math accessible and enjoyable for everyone.

## Why learn Litex?

Litex has the potential to greatly impact both mathematics and AI:

- **For Mathematics**: 
  - **For individual researchers**, it provides peace of mind by reducing the risk of subtle errors undermining their proofs. With it, interactive textbooks can be created, enabling learners to study more efficiently and innovate.
  
  - **For the whole mathematics community**, since Litex ensures correctness, the need for paper reviews is eliminated. This fosters trust and enables large-scale collaboration, akin to a "GitHub for Math", because strangers can trust each other's proofs and collaborate to solve problems.
  
  - **For AI-Driven Math Exploration**: AI excels at solving a wide range of problems quickly. Instead of proving single facts, mathematicians are now trying to expand AI's generalization in math, allowing it to solve thousands of issues simultaneously. AlphaProof is a great example. Litex can greatly speed up this progress, because it addresses many insurmountable bottlenecks in AI training: dataset, reward function and so on.
  

- **For AI**:
  - **More Formal Data**:
Because Litex is an order of magnitude simpler than traditional proof assistants, LLMs may require far fewer datasets to develop the ability to translate existing mathematics into Litex, accelerating formal data growth. The potential large user community also helps provide high-quality data.

  - **Automated Verification**:
Litex can automatically verify LLM outputs for math problems, providing a reliable way to validate and refine their reasoning. This capability is crucial for improving the accuracy and robustness of LLMs in mathematical tasks, e.g. It can act as a universal solution for value function for Reinforcement Learning.

  - **The bridge between symbolic and neural AI**: While neural network AIs dominate machine learning today, we must not overlook symbolic AI's profound contributions. Litex serves as a solid bridge between these two seemingly disparate fields. Integrating verification (searching) into existing AI systems that currently focus only on training (computation) can be a very promising starting point. 

Mathematics and the ability to understand it are built-in capabilities of the human brain . Litex itself is a tool of exquisite innovation. Writing in Litex is enjoyable because it eliminates extra mental burden from the language itself, allowing users to fully immerse themselves in the elegance of mathematics. 

In short, Litex can transform workflow and collaboration of mathematicians. It boost AI's reasoning with more formal data and a super efficient verifier. The core design principle of Litex is simplicity.

## Getting Started

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Litex is a language which strikes the right balance between expressiveness and simplicity. The goal in this section is to show the essential elements of the language through examples. To learn more, visit https://github.com/litexlang/golitex . There are already nearly 2000 commits in this Github repo. The official Litex website https://litexlang.org is under development. 

For the sake of pragmatism, our aim here is to show the essential elements of the language without getting bogged down in details, rules, and exceptions.

### First Example

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a syllogism. To highlight the uniqueness and innovation of Litex, I put both Litex and Lean4 code here for comparison.

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
      <code>obj Bob Human</code> <br> <br>
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

Consider `Human` as the set of all humans. Using `know`, we establish the axiom: all humans are self-aware. Since Bob is in `Human`, "Bob is self-aware" is inherently true. This reflects the classic paradigm of mathematical reasoning: from universal to specific.

Litex reduces typing by eliminating the need to name or recall individual facts. For instance, instead of naming an axiom like “axiom self_aware_all,” you simply write “know …”. When writing done factual expressions for verification, Litex automatically searches for relevant facts using the proposition name and parameters, akin to a regex-based search in a large database. In this system, facts themselves do not possess names; only propositions (collections of facts to be verified) are named. This approach significantly reduces the cognitive load and enhances efficiency in handling complex logical structures.

### Factual Expressions

In Litex, expressions are divided into two types: factual and constructive. Factual expressions declare truths, which Litex verifies, enabling "facts built on facts." Constructive expressions introduce new elements like types, objects, functions, or propositions, on which facts are established.

```
obj Bob Human:
    Bob.age = 10

obj Alice Human // Declaring a object without giving values to its members is valid.

fn add(a Real, b Real) Real:
    then:
        add(a, b) = add(b, a)   // properties(facts) about function add

prop younger(a Human, b Human):
    cond:
        a.age < b.age
```

Every fact in Litex must be tied to a concrete entity: object (`obj`), function (`fn`), or proposition (`prop`). Users must declare objects before use. Any object must belong to a set.

Functions in Litex are not executed. In the realm of mathematics, a function is essentially an entity that is eligible to precede a set of parentheses (). It shares similarities with what we refer to as a object, with the distinctive feature being its ability to be positioned before the ().

Users can think of a function as something that takes parameters that satisfy the condition of fn and combines them to form a new symbol of symbols. It works like struct in C: allows users to group together objects of satisfying certain conditions under a single name. 

```
obj Bob Human

// specific factual expression
Bob is self_aware

// conditional factual expression
when:
    Bob.age = 10    // conditions
    then:
        Bob is young    // true

// universal factual expression
forall x Human, y Human:    // declare objects in the universal expression
    cond:
        x.age < y.age   // conditions
    then:
        $younger(x,y)   // true
```

Litex supports three types of factual expressions. Once verified or known to be true, they are stored in the fact database for future retrieval for verification of subsequent factual expressions:
1. Specific (instantiated):
   - `$younger(x, y)` where `$` is followed by the proposition name `younger` and parameters `x, y`.
   - If there’s only one parameter, it can be written as `parameter is prop name`, like `Bob is young`.
   - For built-in operators (e.g., `<`), simply write expressions like `1 < 2`.
2. Conditional: Begins with the keyword `when`.
3. Universal: Begins with the keyword `forall`.
Different types of factual expressions are stored, retrieved, verified differently.

Every factual expression in Litex yields one of four outcomes:
1. True: Litex confirms the expression based on known facts.
2. False: Litex disproves the expression using known facts.
3. Unknown: Litex cannot determine the truth value due to insufficient information.
4. Error: The input is invalid (e.g., syntax errors).
This design mirrors human reasoning when evaluating proofs: confirming correctness, identifying falseness, encountering uncertainty, or spotting input errors.

```
exist_prop exist_nat_less_than(n Nat):
    have:
         obj m Nat
    then:
        m < n

know forall n Nat:
    cond:
        n > 0
    then:
        $exist_nat_less_than(n)

$exist_nat_less_than(100) // As a specific factual expression, it is true.
have m Nat: $exist_nat_less_than(2)   // Introduce new object, m, to current proof environment
```

One important type of specific factual expression is the existential factual expression. When verified, existential expressions behave identically to ordinary specific expressions. The key distinction lies in their use within a have statement, which provides a safe mechanism to introduce new objects into the current environment.

### Constructive Expressions

<!-- TODO: THIS SECTION IS OBSOLETE -->

```
// declare a type
type Human:
      member:
          obj age Nat

// declare a struct
struct Euclid_Space S:
    type_member:
        obj dim Nat
        fn __add__(v1 S, v2 S) real
    member:
        fn __at__(n Nat) Real:
            cond:
                 n < S.dim
    then:
        forall v1 S, v2 S:
              forall k Nat:
                  (v1 + v2)@k = v1@k + v2@k

struct Group G: // suppose G is a group
    type_member:
        fn __mul__(g G, g2 G) G // define *
        obj I G // define identity
        fn inv() G  // inverse a given group element
    cond:
        forall v1 G, v2 G, v3 G: // equivalent to G.__mul__ is associative
            (v1 * v2) * v3 = v1 * (v2 * v3)
        forall v G:
            v * v.inv() = G.I
            v.inv() * v = G.I
```

In Litex, a type = set + structure (This is inspired by Niklaus Wirth's "Algorithms + Data Structure = Programs"). The set defines possible values, while the structure (operations, special elements, or axioms) adds behaviors or constraints. Structures are defined by specifying `type_member` and `member`. For example, the integers (ℤ) form a type with operations (+, −, ×) and special elements (like 0). A `struct` is a "type of type" or a "set of sets sharing the same structure". `type`s and `struct`s work together to enable abstraction built on abstractions.

<!-- TODO: Interplay of set and type -->

<!-- obj s make_set[Nat]  // 把所有的Nat放到这个叫s的集合里
obj all_sets make_set[Set] // 把所有集合放到集合里。这在现代集合论里是有问题的，但是litex不会报错，因为obj是一个默认你声明的东西存在的关键词

know forall x *T :
	x in make_set[T]
	 -->

<!-- 永远永远永远记住：涉及到集合运算（type运算），先把原来的type的结构消灭掉，把它当做集合。才能进一步在新的集合上构建结构。不要尝试在新结构里保留旧结构-->

```
claim:
    forall (x Human) {x is self_aware}
    prove:
        x is self_aware // if x Human, then x is self_aware immediately

claim:
    forall (x any) x is not self_aware { x is not Human}
    prove_by_contradiction:
          x is Human  // In this situation, it is true, because we are proving by contradiction
          x is self_aware // Litex finds that x is both not self_aware and self_aware, which contradicts

prove_impl Integer Group:
    Integer.__add__ impl G.__mul__
    Integer.0 impl G.I
    forall x Integer:
        x.negative impl G.member.inv

prove_exist  exist_nat_less_than(100) 99:
    99 < 100
```

Sometimes, we want to prove a fact without letting the lengthy proof process clutter the main environment. In such cases, we use the `claim` keyword, followed by the `prove` keyword to conduct the proof within it. Ultimately, only the main fact proven under the `claim` will remain in the main environment.

Special proof statements include existential proof (proving the existence of objects) and implementation proof (showing a type's structure aligns with another type or struct). Implementation builds relationships (`type impl type`) or abstractions (`type impl struct`).

### Another example

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr> 
    <td style="border: 3px solid black; padding: 8px;">
      <code>axiom mathematical_induction(p prop):</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;cond:</code> <br>      
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$p(0)</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall (n Nat) $p(n) {$p(n+1)}</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;then:</code> <br> 
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall n Nat {$p(n)}</code> <br>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>theorem mathematical_induction {P : Nat → Prop} (base : P 0) (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;intro n</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;induction n with</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;| zero => exact base</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;| succ k ih => exact step k ih</code> <br>
    </td>
  </tr>
</table>


Litex significantly reduces the mental effort to formalize theorems compared to other languages. You don’t need to recall or type keywords like "base," "intro," or "induction." Despite its simplicity, Litex syntax is remarkably powerful and general, reflecting the inherent simplicity of math. The main contribution of Litex is uncovering the inherent simplicity of mathematics and designing an equally simple formal language based on it.

### Summary

0. Basic Elements: Propositions, objects, and functions, each with a type.
1. Type: A type = set + structure.
2. Concept: A set of types sharing the same structure.
3. Abstraction: Built via the `impl` keyword, defining relationships between types, structs, and structures.
4. Factual Expressions: Three types—specific (exist, ordinary), conditional, and universal (forall). Litex verifies new facts by searching the fact base and adds them if true.
5. Proof Methods: Direct proof and proof by contradiction, generating new facts.
6. Verification: Uses pattern-based matching of known facts, eliminating the need to name every fact.
7. Generics: Sets as parameters with conditions on types or elements.
8. Math vs. Programming: Math focuses on search and existence, not execution. Litex types are more expressive than programming types.
9. Litex vs. Standard Math: Sets (as types) cannot be passed like objects due to their structural roles.

<!-- TODO -->
<!-- 2. an array of countable numbers of objects of the same type: Array      \[ typeName \]( numberOfObjiables ) -->

<!-- 3. Expansion of Polynomials -->

<!-- need to showcase: Litex can let users to begin his proof from any level of abstraction, instead of forcing him to deal with things he does not need to care -->

<!-- 
how to represent X is R2, derivate (x,y) by y

// z EuclidSpace, z.dim = 2, z[0] 表示z的第一位
fn f(z EuclidSpace):
	f(z) = (z@0)^2 + (z@1)^2 // or f(z) = (z[0])^2 + (z[1])^2
	// 注意到微分几何里，为了让符号不乱，也是像下面这样写的
	f = (id@0)^2 + (id@1)^2 // 用函数id(z)=z 是绕过z这种具体值，直接把函数看成被操作对象

forall z EuclidSpace:
	d(f, 0)(z) = 2 * (z@0) 
    
d(f, 0) = 2 * (id@0)
    -->

## What makes Litex innovative or novel?

_Common sense is not so common._

_--Voltaire_

Steve Jobs once said, "If you define the problem correctly, you almost have the solution." Litex embodies this by exploring what a “minimalist formal proof assistant” truly means.

Existing formal languages are complex, even for mathematicians, as they include unrelated functionalities like memory state alterations. Litex, however, focuses solely on verification, excluding general-purpose computation. Its syntax mirrors everyday math, ensuring clarity and simplicity. Litex identifies the few core logical rules governing math—intuitive even to a 5-year-old.

To put it in another way, traditional proof assistant are implemented to prove some hardcore mathematical theories, while Litex is designed to solve practical problems for everyone. Within traditional proof assistants, there is a much smaller and cleaner language akin to Litex struggling to get out.

Litex’s syntax uses just ~20 keywords: `obj`, `fn`, `prop`, `type`, `interface`, `forall`, `cond`, `when`, `then`, `exist`, `have`, `prove`, `prove_by_contradiction`,  `claim`, and `know`. Every expression yields one of 4 outputs: `true`, `false`, `unknown`, or `error`.This design ensures a smooth learning curve.

By understanding the interplay between programming and math, Litex delivers a seamless, minimal, and complete experience tailored to mathematical verification.

## Key Design Choices

_Language design is a curious mixture of grand ideas and fiddly details._

_-- Bjarne Stroustrup__

Litex is significantly influenced by the Go programming language, particularly in its "set=>type=>interface" system, which closely mirrors Go's "struct=>type=>interface" paradigm. Additionally, Litex's function declaration syntax bears a resemblance to Go's. Most importantly, the minimalism design choice of Go strongly resonates with the Litex's inventor.

Inheritance (C++/Java-style) is a poor fit for Litex:

Inflexible – Inheritance hierarchies are rigid, making extension and evolution difficult.

Layer freedom – Users should begin at any abstraction level, not forced from low-level math.

Beyond Go, Litex draws inspiration from other programming languages. For instance, Python's scoping rules have shaped Litex's approach to object and function scope.

The inventor of Litex holds a deep appreciation for Lisp's "everything is a list" philosophy, which contributes to the language's conceptual integrity. This influence is evident in Litex's design, where every statement is treated as an expression a direct nod to Lisp's expressive power. The marvelous "structure and interpretation of computer programs", a book on Lisp, strongly shapes the inventor's view of what programming actually means.

Furthermore, Tex's clear distinction between "math expressions" and "plain words" inspired Litex's separation of "factual expressions" from ordinary symbols. Litex also aspires to achieve the same level of ubiquity and utility as Tex, aiming to become a widely adopted daily tool. This ambition is encapsulated in its name: Litex = Lisp + Tex, symbolizing the fusion of Lisp's expressive elegance and Tex's practicality.

## Join the Litex Project

_The best way to predict the future is to invent it._

_-- Alan Kay_

The inventor of Litex, Jiachen Shen, is a hacker with a math degree. The Litex project is starred by enthusiasts from world-class institutions, including The University of Chicago, Carnegie Mellon University, Peking University, Tsinghua University, Fudan University, Shanghai Jiao Tong University, openMMLab, deepmath.cn etc.

I create Litex for fun: turning invention and implementation into art. This is the first step in transforming the art of mathematics into the art of programming. As Knuth said in his Turing Award lecture: science is logical, systematic, calm; art is aesthetic, creative, anxious. Both math and programming live at this intersection—rigorous yet deeply human.

Therefore, I have strong belief that there is only a small gap between programming and mathematical reasoning. I also strongly believe it does not take "that many" syntax and semantics to formalize ALL math. The more I program this project, the firmer my belief becomes.

If you want to contribute to Litex, you must be able to appreciate its simplicity. Litex is a very small language. After all, as the only contributor to Litex (at least the first 1500 git commits are all pushed by me), I have no time to implement a complicated one.

There is no doubt that both the AI community and the math community will benefit from Litex. Litex is a highly interdisciplinary projects: programming languages, mathematics, and the AI community. Litex will never succeed without an active community. Feel free to issue your suggestions and ideas to help me improve this open-source project. Your feedback is invaluable.

Since Litex is still under development, it's inevitable that today's Litex might be very different than what it is in the future. Visit [the Litex website](https://litexlang.org) for more information. Contact me by litexlang@outlook.com, malloc_realloc_free@outlook.com.
