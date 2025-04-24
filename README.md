# Litex: A Minimalist Proof Assistant

<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

## About

_That language is an instrument of Human reason, and not merely a medium for the expression of thought, is a truth generally admitted._

_–- George Boole_

**Litex is a minimalist proof assistant (formal language). With a predicted "de Bruijn factor" (the ratio of formal to informal proof difficulty) of 0.5–1.5, Litex will transform the mathematical landscape and help build better reasoning AI models.**

**Litex stands out from other proof assistants because of its simplicity.** Since even children can reason logically and naturally, a formal language for anyone to reason with both rigor and intuiveness can be invented. Litex is designed to create such a language. 

**First-order logic, with its 8 core keywords (and, or, not, forall, exist, equal, if, then), forms the foundation of all mainstream mathematics. Litex builds on this foundation as a thin layer, implementing a "regular expression interpreter with customizable matching rules and math-friendly syntax sugar". Its simplicity means you can learn it with just common sense.**

Think this way: When you verify a piece of proof in your brain, what you are doing is nothing more than **matching** known facts with the facts you are now writing. Litex is a computer tool to automate this process and verify your reasoning for you. And in this way Litex helps you build new facts on top of the existing facts with 100% correctness. 

Litex is unique in two ways. First, **Litex is a domain-specific language for mathematical verification. It is not designed to be Turing complete.** Whereas traditional proof assistants are general-purpose programming languages that introduce unrelated complexities. 

Second, Litex is built around common sense rather than sophisticated mathematical theories to help a broader range of people to use formal language. **Designed to be as intuitive as Python and LaTeX, Litex offers a minimal learning curve.**

**The potential impacts of Litex include: enabling proof verification (including LLM-generated outputs), revolutionizing proof writing and review, facilitating large-scale collaborations, creating datasets for LLM training, and enhancing LLM reasoning capabilities.** With its inherently simple syntax, Litex is well-positioned to achieve these goals and attract a growing community of researchers to the world of formal languages.

**Mathematics is fundamentally about abstraction, and computer science is the discipline that tackles abstraction. The ultimate goal of Litex is to harness programming concepts and tools to tackle challenges in mathematics. It is a brave attempt to scale reasoning with the ever-expanding power of modern computing resources.**


<!-- TODO: 参考下面这个网站以获得更多数学家的角度，里面有很多数学家对数学的讨论 https://sugaku.net/content/understanding-the-cultural-divide-between-mathematics-and-ai/ -->
<!-- On the foolishness of "natural language programming". 里面有很多关于形式化语言比自然语言好的观点：litex把数学从不准确，冗余的，不同国家的人互相看不懂，抽象层过多以至于难以追踪，模块化程度为0，的自然语言，变成了非常准则，无任何冗余，世界通用，抽象层靠常用编程工具变得很追踪，模块化很高以至于人们可以在数学的github上分享 的形式化语言 -->

## Litex: Bridging Mathematics and AI in the Computational Age

The mathematics community is experiencing a revolution. After centuries of static methodology, systems like Litex are making the impossible possible:

Mathematically guaranteed correctness eliminating human error

GitHub-scale collaboration for mathematical research

AI-powered discovery solving thousands of problems simultaneously (as demonstrated by AlphaProof)

Litex uniquely connects two worlds:

For mathematicians: It automates proof verification while enabling unprecedented collaborative research at scale

For AI development: Its simplicity makes formal mathematics accessible, while providing structured training data and verifiable reward functions

For both fields: It creates a virtuous cycle - AI generates formal mathematics while Litex ensures correctness and produces new training data

This synergy heralds a new era where mathematical rigor meets computational power, and human creativity combines with machine precision to push the boundaries of discovery.


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

That is why Litex is a "regular expression interpreter with customizable matching rules (via keywords like `forall`) and math-friendly syntax sugar." It operates below any axioms, including set theory (the reason why we can use set theory to derive new facts is that we rely on matching known facts with new fact to be verified), making it intuitive yet powerful—so natural that it's rarely explained in any math textbooks. Just as Lego lets you assemble complex structures from simple pieces, Litex lets you build math from minimal (with just 8 main keywords: forall, exist, not, or, fn, prop, obj, set and several other auxiliary keywords), reusable parts -— no unnecessary complexity, just pure flexibility.

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
<!-- 2. an array of countable numbers of objects of the same type: Array      \[ typeName \](  ) -->

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

Litex is a minimalist proof assistant, designed to be simple and intuitive. It draws inspiration from various programming languages, particularly Go, Lisp, Tex, C, Python. The design philosophy emphasizes minimalism, conceptual integrity, and the KISS (Keep It Simple, Stupid) principle.

In short, Litex is fundamentally an attempt to scale reasoning with the ever-expanding power of modern computing resources. Litex embrace simplicity, the only way to be flexible enough for the unknown future and to maintain conceptual integrity, as its core design principle.

The key feature of Litex is its simplicity. Its simplicity stems of its intuitiveness. In fact, Litex is so intuitive that people with no math background can understand it. You can learn Litex in 10 minutes. However, its simplicity does not come at the cost of expressiveness.

On my(I am Jiachen Shen, the inventor of Litex) journey of inventing Litex, such intuitiveness is a double-edged sword. It's great because I do not need to rely on any textbook or paper to design Litex. It's bad because if I do get stuck, I do not have any textbook or paper to refer to.

Litex has a lower abstraction level below any existing mathematical axioms, including ZFC. Afterall, Litex is just a regex-based interpreter with customizable matching rules and math-friendly syntax sugar. Any existing mathematical axioms can be expressed in Litex. 

Think this way: When you verify a piece of proof in your brain, what you are doing is nothing more than matching known facts with the facts you are now writing. Litex is a computer tool to automate this process and verify your reasoning for you.

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
