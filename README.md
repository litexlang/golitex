# Litex: A Minimalist Proof Assistant

<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

## About

_That language is an instrument of Human reason, and not merely a medium for the expression of thought, is a truth generally admitted._

_–- George Boole_

**Litex is a minimalist proof assistant (formal language). With a predicted "de Bruijn factor" (the ratio of formal to informal proof difficulty) of 0.5–1.5, Litex will transform the mathematical landscape and help build better reasoning AI models.**

**Litex stands out from other proof assistants because of its simplicity.** If even children can reason naturally, a formal language that combines rigor and intuition must be possible -- it simply hasn’t been invented yet. Litex is designed to create precisely such a language.

Think this way: When you verify a piece of proof in your brain, what you are doing is nothing more than **matching** known facts with the facts you are now writing. Litex is a computer tool to automate this process and verify your reasoning for you. And in this way Litex helps you build new facts on top of the existing facts with 100% correctness. 

**Technically, first-order logic, with its 8 core keywords (and, or, not, forall, exist, equal, if, then), forms the foundation of all mainstream mathematics. Litex builds on this foundation as a thin layer, implementing a "regular expression interpreter with customizable matching rules and math-friendly syntax sugar". Its simplicity means you can learn it with just common sense.**

Litex is unique in two ways. First, **Litex is a domain-specific language for mathematical verification. It is not designed to be Turing complete.** Whereas traditional proof assistants are general-purpose programming languages that introduce unrelated complexities. 

Second, Litex is built around common sense rather than sophisticated mathematical theories to help a broader range of people to use formal language. **Designed to be as intuitive as Python and LaTeX, Litex offers a minimal learning curve.**

**The potential impacts of Litex include: enabling proof verification (including LLM-generated outputs), revolutionizing proof writing and review, facilitating large-scale collaborations, creating datasets for LLM training, and enhancing LLM reasoning capabilities.** With its inherently simple syntax, Litex is well-positioned to achieve these goals and attract a growing community of researchers to the world of formal languages.

**Mathematics is the science of abstraction, while computer science is the discipline that masters it. The ideal of Litex is bridging the two—using programming to solve mathematical challenges and mathematics to enhance AI reasoning. It’s a bold effort to scale reasoning with modern computing power and programming ingenuity.**

(The official Litex website https:#litexlang.org is under development.)

<!-- TODO: 参考下面这个网站以获得更多数学家的角度，里面有很多数学家对数学的讨论 https:#sugaku.net/content/understanding-the-cultural-divide-between-mathematics-and-ai/ -->
<!-- On the foolishness of "natural language programming". 里面有很多关于形式化语言比自然语言好的观点：litex把数学从不准确，冗余的，不同国家的人互相看不懂，抽象层过多以至于难以追踪，模块化程度为0，的自然语言，变成了非常准则，无任何冗余，世界通用，抽象层靠常用编程工具变得很追踪，模块化很高以至于人们可以在数学的github上分享 的形式化语言 -->

## Litex: Bridging Mathematics and AI in the Computational Age

The mathematics community is experiencing a revolution. After centuries of static methodology, systems like Litex are making the impossible possible:

- Mathematically guaranteed correctness eliminating human error.
- GitHub-scale collaboration for mathematical research.
- AI-powered discovery solving thousands of problems simultaneously (as demonstrated by AlphaProof).

Litex uniquely connects two worlds of mathematics and AI:
- For mathematicians: It automates proof verification while enabling unprecedented collaborative research at scale.
- For AI development: Its simplicity makes formal mathematics accessible, while providing structured training data and verifiable reward functions.
- For both fields: It creates a virtuous cycle - AI generates formal mathematics while Litex ensures correctness and produces new training data.

This synergy heralds a new era where mathematical rigor meets computational power, and human creativity combines with machine precision to push the boundaries of discovery.


## Getting Started

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Litex is a language which strikes the right balance between completeness, strictness, and simplicity. The goal in this section is to show the essential elements of the language through examples. For the sake of pragmatism, our aim here is to show the essential elements of the language without getting bogged down in details, rules, and exceptions.

### First Example

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle in his Prior Analytics, which formalizes deductive reasoning as follows:

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>set Human</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$self_aware(x)</code> <br> <br>
      <code>obj Bob Human</code> <br> <br>
      <code>$self_aware(Bob)</code>
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

Consider `Human` as the set of all humans. Using `know`, we establish the fact without the need to be verified by other facts: all humans are self-aware. Since Bob is in the set of `Human`, "Bob is self-aware" is inherently true.

Notice how Litex requires much less typing than Lean4 even in this simple example. An obvious advantage of Litex is that it reduces typing by eliminating the need to name or recall individual facts. When writing done factual expressions for verification, Litex automatically searches for relevant facts, akin to a regex-based search in a large database. For instance, instead of naming an axiom like “axiom self_aware_all,” you simply write “know …”. This approach significantly reduces the cognitive load and enhances efficiency in handling complex logical structures.

Although this is a simple example, it has already taught us how ANY mathematical facts are derived from known facts. Just as Lego lets you assemble complex structures from simple pieces, Litex lets you build math from minimal (with just 8 main keywords: forall, exist, not, or, fn, prop, obj, set and several other auxiliary keywords), reusable parts -— no unnecessary complexity, just pure flexibility.

Also notice Litex adopts a mixture of Python and GoLang's syntax, making it easy to pick up for users who has some programming experience.

### Factual Expressions

In Litex, expressions are divided into two types: factual and constructive. Factual expressions declare truths, which Litex verifies, enabling "facts built on facts." Constructive expressions introduce new elements like types, objects, functions, or propositions, on which facts are established.

```
obj Alice Human # Declaring a object without giving values to its members is valid.

fn add(a Real, b Real) Real: # self defined a + b
    add(a, b) = add(b, a)   # properties(facts) about function add
    add(a, b) = a + b # establish relationship between self-defined function add and built-in function +

prop less_than(a Real, b Real): # self defined a < b
    less_than(a, b) = a < b # establish relationship between self-defined proposition less_than and built-in operator <
```

Every fact in Litex must be tied to a concrete entity: object (`obj`), function (`fn`), proposition (`prop`). Users must declare objects before use. Any object must belong to a set.


Functions in Litex are not executed. In the realm of mathematics, a function is essentially an entity that is eligible to precede a set of parentheses (). It shares similarities with what we refer to as a object, with the distinctive feature being its ability to be positioned before the ().

Users can think of a function as something that takes parameters that satisfy the condition of fn and combines them to form a new symbol of symbols. It works like struct in C: allows users to group together objects of satisfying certain conditions under a single name. 

```
obj Bob Human # declare a object

# specific factual expression
$self_aware(Bob) # when there is only one parameter, it can be written as parameter is prop name
Bob is self_aware

fn age(x Human) Nat

# declare a proposition
prop young(x Human):
    age(x) < 18 # x young iff age(x) < 18

# conditional factual expression
when:
    age(Bob) = 10    # conditions
    then:
        Bob is young    # true

# universal factual expression
forall x Human, y Human:    # declare objects in the universal expression
    cond:
        age(x) < age(y)   # conditions
    then:
        $younger(x,y)   # true
```

A **proposition** is a declarative statement that can be proven true or false within a logical system. Any fact is an instance of a proposition.

Litex supports three types of factual expressions. Once verified or known to be true, they are stored in the fact database for future retrieval for verification of subsequent factual expressions:
1. Specific: A **specific fact** is a fact that is instantiated with specific values.
   - `$younger(x, y)` where `$` is followed by the proposition name `younger` and parameters `x, y`.
   - If there’s only one parameter, it can be written as `parameter is prop name` (similar to how natural language works), like `Bob is young`.
   - For built-in operators (e.g., `<`), simply write expressions like `1 < 2`.
2. Conditional: A **conditional fact** Begins with the keyword `when`, which corresponds to `if ... then ...`.
3. Universal: A **universal fact** (declared with `forall`) asserts that a property holds for all possible instances of its bound variables within a defined scope.

Every factual expression in Litex yields one of four outcomes:
1. True: Litex confirms the expression based on known facts.
2. False: Litex disproves the expression using known facts.
3. Unknown: Litex cannot determine the truth value due to insufficient information.
4. Error: The input is invalid (e.g., syntax errors).

This design mirrors human reasoning when evaluating proofs: confirming correctness, identifying falseness, encountering uncertainty, or spotting typing errors.

```
exist_prop m Nat exist_nat_less_than(n Nat):
    m < n

know forall n Nat:
    dom:
        n > 0
    then:
        $exist_nat_less_than(n)

$exist_nat_less_than(100) # As a specific factual expression, it is true.
exist m Nat st $exist_nat_less_than(2)   # Introduce new object, m, to current proof environment

exist_obj m $exist_nat_less_than(2) # introduce a new object m, and verify it satisfies the existential expression $exist_nat_less_than(2)

```

One important type of specific factual expression is the existential factual expression. When verified, existential expressions behave identically to ordinary specific expressions. The key distinction lies in 1. the user can use `exist_obj` to bring a new object, whose existance is ensured, into current scope. 2.  the user uses `exist ... st ...` statement to verify the corresponding existential expression.

### Constructive Expressions
```
interface Group G:
    fn __mul__(g G, g2 G) G # define *
    obj I G # define identity
    fn inv(g G) G  # inverse a given group element

    iff:
        forall x G, y G, z G:
            (x * y) * z = x * (y * z)
        forall x G:
            x * G::I = x
        forall x G:
            x * G::inv(x) = G::I

# Litex automatically infers the type of G from the context and verifies whether the type satisfies the Group interface, i.e. the given elements and operations satisfy the Group axioms.

{Real, __add__, 0, __neg__} impl Group # you can also write it as {Real, __add__, 0, __neg__} impl Group

type RealAsGroup {Real, __add__, 0, __neg__} impl Group: # Real = the set of all real numbers. Name RealAsGroup says how Real implements Group.

prop Group_is_abelian<G Group>(): # you call it by using $Group_is_abelian(setName)
    forall x G, y G:
        x * y = y * x # when given G, * is referred to as Group::__mul__

$Group_is_abelian(Real) # true. * is Real::_add__
```

In Litex, a interface = set + structure(functions, objects, propositions bound to the set). You can think of a interface as a set of sets that share the same structure. For example, the set of all groups is an interface. A set might have different ways to implement an interface (e.g. the set of integers, with normal addition, or with modular addition, all implement the interface of Group), that is why we need to name it. (e.g. RealAsGroup)

(This Design draws inspiration from 2 concepts: 1. Niklaus Wirth's "Algorithms + Data Structure = Programs" and "type = set + structure". 2. The  `interface` + `type` + `struct` type system in GoLang.)

(I think type system adopted by languages like Lean4 often confuses people, because an object can only belong to one type. However, in math, it is very common to have an object belong to multiple sets.)

```
know:
    $q(0)
    forall x nat:
        $q(x)
        then:
            $q(x+1)

    not $p(2)
    forall x nat:
        $p(x)
        then:
            $p(x+1)

$q(0) # true, because it matches the known specific fact $q(0)

claim:
    $q(2)
    prove_by_contradiction:
        $q(1)
        $q(2)

claim:
    $p(0)
    prove_by_contradiction:
        $p(1)
        $p(2)

know:
    forall x nat:
        $p(x)
    
    forall x nat:
        $p(x)
        then:
            $q(x)

claim:
    forall x nat:
        $q(x)
    prove:
        $p(x)
        $q(x)

prove: # open a local environment and write test codes
    know Bob is Human
    Bob is self_aware # true
```

<!-- 这里有严重的欠缺：我应该说明从know，到match，到验证的全过程，这才是litex的第一性原理，但我readme里居然没怎么呈现 -->

There are 2 ways to prove a fact: using known specific facts or using known universal facts. For example, in the example above, we use the known specific fact `$q(0)` to prove `$q(0)`. Or we can use knwon `forall x human: $mortal(x)`, `Bob \in human` to prove `$mortal(Bob)`.

Sometimes, we want to prove a fact without letting the lengthy proof process clutter the main environment. In such cases, we use the `claim` keyword, followed by the `prove` keyword to conduct the proof within it. Ultimately, only the main fact proven under the `claim` will remain in the main environment. 

As for proving a universal fact, the parameters of the universal fact is passed into the new environment. After the proof, the `known` universal fact is added to the main environment.

You can also use `prove` to open a local environment and write test codes, mimicking the behavior of `{}` in traditional programming languages.

### Useful Language Features

Computer is fundamentally about automating repetitive tasks. Litex is no exception. There are some small but useful features that make Litex more friendly to use.

1. `commutative` and `associative` keywords: These keywords are used to verify the commutative and associative properties of a function. They tell the interpreter to verify the fact in both directions.


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

0. Basic Elements: Propositions, objects, and functions, each belongs to a set.
1. Interface: A type = set + structure.
2. Abstraction: Built via the `impl` keyword, defining relationships between types, structs, and structures.
3. Factual Expressions: Three types—specific (exist, ordinary), conditional, and universal (forall). Litex verifies new facts by searching the fact base and adds them if true.
4. Proof Methods: Direct proof and proof by contradiction, generating new facts.
5. Verification: Uses pattern-based matching of known facts, eliminating the need to name every fact.
6. Math vs Programming: Math focuses on search and existence, not execution. Litex types are more expressive than programming types.
7. Litex vs. Standard Math: Sets (as types) cannot be passed like objects due to their structural roles.


### Remarks
Strictly speaking, fn and set in Litex do not carry the exact same meaning as in traditional set theory. For instance, users can define functions (e.g., union) that operate on the "set of all sets"—something prohibited in conventional set theory. Litex allows such constructions but issues warnings when potentially "dangerous" operations are attempted, giving users flexibility while discouraging unsound reasoning.

Fundamentally, Litex is a regex-based interpreter with customizable pattern-matching rules and math-friendly syntactic sugar. It operates below the level of formal mathematical axiom systems (such as ZFC), allowing users to define their own axioms. This design prioritizes expressiveness and adaptability over strict adherence to a specific foundational theory.

<!-- 可以考虑新开一个Section，专门对比lean和litex -->
<!-- 下面这是lean做勾股定理的代码，非常复杂，非常多的 hierarchy，不能直接像初中生一样不需要任何前置知识就可以理解 -->
<!-- theorem InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle{V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) : -->
<!-- ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) -->

## What makes Litex innovative or novel?

_Common sense is not so common._

_--Voltaire_

Steve Jobs once said, "If you define the problem correctly, you almost have the solution." Litex embodies this by exploring what a “minimalist formal proof assistant” truly means.

Existing formal languages are complex, even for mathematicians, as they include unrelated functionalities like memory state alterations. Litex, however, focuses solely on verification, excluding general-purpose computation. Its syntax mirrors everyday math, ensuring clarity and simplicity. Litex identifies the few core logical rules governing math—intuitive even to a 5-year-old.

To put it in another way, traditional proof assistant are implemented to prove some hardcore mathematical theories, while Litex is designed to solve practical problems for everyone. Within traditional proof assistants, there is a much smaller and cleaner language akin to Litex struggling to get out.

Litex’s syntax uses just no more than 20 keywords: `obj`, `fn`, `prop`, `type`, `interface`, `forall`, `cond`, `when`, `then`, `exist`, `have`, `prove`, `prove_by_contradiction`,  `claim`, and `know`. Every expression yields one of 4 outputs: `true`, `false`, `unknown`, or `error`.This design ensures a smooth learning curve.

By understanding the interplay between programming and math, Litex delivers a seamless, minimal, and complete experience tailored to mathematical verification.

## Key Design Choices

_Language design is a curious mixture of grand ideas and fiddly details._

_-- Bjarne Stroustrup, inventor of C++_

Litex is a minimalist proof assistant, designed to be simple and intuitive. It draws inspiration from various programming languages, particularly Go, Lisp, Tex, C, Python. Litex embrace simplicity, the only way to be flexible enough for the unknown future and to maintain conceptual integrity, as its core design principle.

Litex is an attempt to scale reasoning with the ever-expanding power of modern computing resources, and to introduce a new way of thinking (the way of thinking that is more like programming) about math.

Technically, Litex is a regex-based interpreter with customizable matching rules and math-friendly syntax sugar. Litex has a lower abstraction level below any existing mathematical axioms, including ZFC. Any existing mathematical axioms can be expressed in Litex. 

Also remember, Litex is not Turing Complete, because verification does not require execution or loops (goto statements), which further enhances its expressiveness. In short, the user will enjoy freedom and expressiveness that no other proof assistant can offer. 

(To use Litex effectively, adopt a mindset that prioritizes intuitive over rigid prerequisites: just as children learn math without first mastering axioms, Litex should allow users to work naturally and incrementally, embedding foundational systems only when needed — not as barriers to entry. Also, when the users do feel necessary to implement a new axiom, they can do so in Litex just as if they are writing on a paper.)

The inventor of Litex sees Litex as a regex-based interpreter. Every design choice around Litex categorizes into: 1. how to implement a mathematical reasoning(verification) process as a syntax and semantics sugar for regex matching, 2. what mathematical reasoning process to implement. There are not that many reasoning processes, since first-order logic is enough for most practical math problems, and every reasoning process can be translated into first-order logic.

Think this way: When you verify a piece of proof in your brain, what you are doing is nothing more than matching known facts with the facts you are now writing (how verification works? Fundamentally, just by comparing the words of two facts and using first-order logic to infer the truth of the new fact). If a known fact (universal or specific) is matched with the new fact, the new fact is proven (See the examples above). If not, the new fact is unknown.

Litex is a computer tool to automate this process and verify your reasoning for you. The more you use Litex, the more you will understand what I mean and the more you will love it. You can learn Litex in 10 minutes. However, its simplicity does not come at the cost of expressiveness.

Litex is significantly influenced by the Go programming language. Interfaces in both Go and Litex are pretty simple. No hierarchy, no inheritancee. Additionally, Litex's function declaration syntax bears a resemblance to Go's. Most importantly, the minimalism design choice of Go strongly resonates with the Litex's inventor.

Inheritance (C++/Java-style) is a poor fit for Litex:

Inflexible – Inheritance hierarchies are rigid, making extension and evolution difficult, which is common in other proof assistants.

Layer freedom – Users should begin at any abstraction level, not forced from low-level math, which is more aligned with mathematical discovery in real life.

Not Intuitive – Inheritance is not intuitive. An object can for sure belong to multiple sets, but in inheritance, an object can only belong to one type (or belong to a fixed part of inheritance hierarchy).

(In fact, GoLang is so well-designed and Litex learns so much from it, that Litex chooses GoLang to implement itself.)

Beyond Go, Litex draws inspiration from other programming languages. For instance, Python's scoping rules have shaped Litex's approach to object and function scope. The C programming language's syntax and semantics significantly influenced Litex's design. Operator overloading behavior is inspired by C++. The inventor of Litex holds a deep appreciation for Lisp's "everything is a list" philosophy, which contributes to the language's conceptual integrity. 

Furthermore, Tex's clear distinction between "math expressions" and "plain words" inspired Litex's separation of "factual expressions" from ordinary symbols. Litex also aspires to achieve the same level of ubiquity and utility as Tex, aiming to become a widely adopted daily tool. This ambition is encapsulated in its name: Litex = Lisp + Tex, symbolizing the fusion of Lisp's expressive elegance and Tex's practicality.

## Join the Litex Project: Words from the Inventor

_The best way to predict the future is to invent it._

_-- Alan Kay_

I, Jiachen Shen, a hacker and a math enthusiast. I majored in math and self-taught programming. The Litex project is starred by enthusiasts from world-class institutions, including The University of Chicago, Carnegie Mellon University, Peking University, Tsinghua University, Fudan University, Shanghai Jiao Tong University, openMMLab, deepmath.cn etc.

A good art is enjoyable to its author happy and be useful to others. This process of inventing Litex makes me happy, and I hope Litex can be useful for both math community and AI community, or even anyone from any field. As Knuth said in his Turing Award lecture: science is logical, systematic, calm; art is aesthetic, creative, anxious. Both math and programming live at this intersection, rigorous yet deeply human.

Moreover, I have strong belief that there is only a small gap between programming and mathematical reasoning. I also believe it does not take "that many" syntax and semantics to formalize ALL math. The more I program this project, the firmer my belief becomes. The real obstacle dragging me back is not the weakness of my ideas, but the loneliness of this long journey. That is why I am so grateful for any kind of support.

On my(I am Jiachen Shen, the inventor of Litex) journey of inventing Litex, its intuitiveness is a double-edged sword. It's great because I do not need to rely on any textbook or paper to design Litex. It's bad because if I do get stuck, I do not have any textbook or paper to refer to. Creativity is a definitely required skill if you want to contribute to Litex.

If you want to contribute to Litex, you must be able to appreciate its simplicity. Litex is a very small language. After all, as the only contributor to Litex (at least the first 2000 git commits are all pushed by me), I have no time to implement a complicated one. Keeping it simple yet powerful is the key to its growth and success.

There is no doubt that both the AI community and the math community will benefit from Litex. Litex is a highly interdisciplinary projects: programming languages, mathematics, and the AI community. Litex will never succeed without an active community. Feel free to issue your suggestions and ideas to help me improve this open-source project. Your feedback is invaluable.

Since Litex is still under development, it's inevitable that today's Litex might be very different than what it is in the future. Visit [the Litex website](https:#litexlang.org) for more information.

If you're interested in programming language development, open-source maintenance, large-scale software systems, mathematics, formal methods, or LLM reasoning, I'd love to discuss any of these topics with you.
Contact me by <litexlang@outlook.com>, <malloc_realloc_free@outlook.com>.
