# The Litex Reference Manual

<!-- reference 未来需要有的部分 introduction, concepts overview, api reference, language reference -->

**Release v0.1.1-beta**  
*May 2025*  
*Created by Jiachen Shen*

This manual is a reference for Litex, written for potential contributors and users who want to understand how Litex works inside.

## Words from the Inventor

_The best way to predict the future is to invent it._

_-- Alan Kay_

I, Jiachen Shen, a hacker and a math enthusiast, am the creator of Litex. I majored in math and self-taught programming. I have been working on Litex since 2024, and I am still working on it. I really like designing and engineering new languages. I even more like working on my language which serves people's needs.

A good art is what makes its creator happy and makes its users find it useful.[^1] I hope Litex can be a good art for both me and its users.

Litex is for solving the problem of formalizing math. Traditional formal languages are too complex and too far removed from everyday mathematical notation. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. The fundamental reason for this complexity is that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers.

Unlike Lean (a full Turing-complete language), Litex is a read-only Turing machine, sacrificing generality for clarity. Using match and substitution, Litex works just like how human beings check facts. Think of it like SQL for databases, but for everyday math.

This reference is a guide for Litex hard-core users, contributors, developers, and anyone who wants to understand the design principles of Litex. It is not a tutorial.

## Litex view of math

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_-- David Hilbert_

Math is built on top of a small sets of reasoning rules and axioms. There are basically two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

OK, you have already known the basic idea of Litex.

Another group of reasoning rules are about real numbers, like 1, 3.5 or 4.123456789. These objects are different from the user-defined objects, as 1. their literal representation contains information 2. it is impossible for the user to declare them one by one and must be builtin. Verification of these objects is done by builtin rules and the users do not need to worry about them.

## Difference Between A Programming Language and Math

There are several examples of major differences between a programming language and math:

1. There is no variable in math. Every object in math is determined once it is defined. Yet an object might change its value in programming languages.

2. There is control flow in math. "for i in range(1000)" never exists in any math proof. Nobody iterates 1000 thousand of times in his brain to prove a statement. Instead, he uses keyword "forall" to express the same meaning.

3. A function in programming is for execution, yet in math a function is just a symbol which takes in other symbols as parameters and forms a new symbol. There is no execution of function in math. All is verification.

It turns out that traditional formal languages, like Lean4, Coq, and Isabelle, attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

The huge difference between math or reasoning in general and programming languages is why Litex is not designed to be a programming language, making it in first principle different from other traditional formal languages. Technically, Litex is a Read-Only Turing Machine, instead of a Turing Machine.

Litex sacrifices Turing completeness to focus exclusively on mathematical verification, adopting a Python-like syntax for ease of use and LaTeX-like elegance for mathematical expression (similar to how SQL sacrifices completeness to specialize in database logic). This makes Litex accessible not only to professional mathematicians but also to beginners. 

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

The C programming language's syntax and semantics significantly influenced Litex's design. Operator overloading behavior is inspired by C++. The inventor of Litex holds a deep appreciation for Lisp's "everything is a list" philosophy, which contributes to the language's conceptual integrity. Also, since C uses postfix like L to make number as type the user want to overloaded  type of a number literal(e.g. 1L represents a long integer), Litex uses postfix to do type inference(e.g. 1r represents 1 as R number). No user defined type overloading is allowed.

(Syntactically, Litex learn from python and go. Semantically, Litex learn from Lisp, C and awk. As a daily tool, Litex learn from Tex and python jupyter notebook. Litex design principle is a mixture of all of them.)

fn_template is inspired by C++'s template over function. It is a describing the properties of a function. However, there are still differences. No need to introduce <> : Because parameters can be passed in the parameter list (so-called requirements for types are essentially individual facts in Litex. Things that are sets and things that are not sets are fundamentally no different in terms of fact handling. This approach is inherently different from C++'s type system.) Here we can see the fundamental difference of "set system" in Litex and "type system" in C++ and other programming languages.

The import keyword sort of works like #include in C. #include embed the whole file thoroughly into the line where it is used. Litex run the whole file thoroughly in the line where it is used. If the import statement changes its line, its result might change. There are both "thoroughly" and "depend on the line where it is used" in both keywords.

Furthermore, Tex's clear distinction between "math expressions" and "plain words" inspired Litex's separation of "factual expressions" from ordinary symbols. Litex also aspires to achieve the same level of ubiquity and utility as Tex, aiming to become a widely adopted daily tool. This ambition is encapsulated in its name: Litex = Lisp + Tex, symbolizing the fusion of Lisp's expressive elegance and Tex's practicality.

The best to test Litex is by translating "real-world" into Litex. I use Professor Terrence Tao's Analysis I and II to test Litex. The set theory chapter of Analysis I helps a lot to remind me what functionalities are missing at each stage of implementing Litex.

The user can divide the problem into independent tasks and store them in different packages to make execution faster.

*The Litex interpreter basically takes the top-down approach to verify a fact, which means it basically start from proposition and try to find a fact that can be used to prove the proposition, instead of coming from the bottom up, from related symbols to derive new facts and then use them to prove the proposition.*

There are many "design balances" in Litex. Math is so common that anybody has some basic knowledge of it. On the other hand, some branch of math can be so hard that only experts can understand. So there is a very huge gap between two groups of Litex users: innocent non-professionals, AI researchers who know some math, and math experts. What they want Litex to be is different. Since Litex is a pragmatic language and I wish it could have as many users as possible, any time I encounter those "hard choices", I always put the innocent group of users' demand first.

Litex is fundamentally a read-only Turing machine. Once any fact is stored, it can not be removed or changed. The amount of data stored in memory is in proportion to the amount of code that the user write. Such design makes Litex align with everyday math.

Litex gets its name from Lisp and Tex. Lisp is a programming language that is very close to math. Tex is a typesetting system that is very close to math. Both of them greatly inspired Litex, making Litex also a formal language that is very close to math.

Litex intentionally has few keywords and minimal syntax sugar to encourage consistent programming habits - there should be only one way to express a given logic. This makes code more readable and prevents users from getting overwhelmed by too many expression choices.

Difference and similarity between standard library and kernel:

1. similarity: some facts can be both implemented in standard library and kernel.

2. difference:

- kernel development is much harder to just write litex code. Litex code is much easier to read and write for non-experts.
- litex code can be written by much much more people, because Litex users are much more than Litex kernel developers.
- The standard library must be loaded into memory, every time we initialize the kernel, which might sort of waste some time every time.
- Striking the right balance between whether a feature should be implemented in the standard library or the kernel is hard. The right balance is beneficial for both users(has enough features to express logic they want to express easily) and developer(has minimal features for easier development and maintenance).
- In my process of implementing Litex, I want it to be minimalistic. That why I only implement the most basic features in the kernel. Sometimes I do not know whether a feature should be implemented in the kernel, or actually can be implemented by the user himself. If a piece of logic can be implemented by the user himself, then it should not be implemented in the standard library, unless implementing a new feature as syntax sugar can be very handy for the user. Some features, like addition of literal numbers like 1 + 1 = 2 and counting and prove forall by iteration can never be implemented by the user because taking use of literal information is not embedded as basic feature of Litex. 

Here is difference between Litex (or math) and programming languages:

import in Litex, i.e. all the facts in the imported file are executed at the line where it is used. In programming languages, the imported file does not need to be executed at the line where it is used, it just needs to be loaded into memory and when a function is called, then that function is executed.



## Conclusion

_That language is an instrument of Human reason, and not merely a medium for the expression of thought, is a truth generally admitted._

_–- George Boole_

As George Boole said, language not only embodies our thoughts, but more importantly, it shapes how we think. I hope Litex can help you think better in math.

## Language Design Explanations

_If you define the problem correctly, you almost have the solution._

_-- Steve Jobs_

1. set system in Litex

prop P(x SetX, y SetY) 

is the "short form of"

prop P(x, y):
    dom:
        x $in SetX
        y $in SetY

So the "set system" (in other languages it is called type system) of Litex is actually a syntax sugar. Litex syntax requires you to write the first form for simplicity and strictness.

The reason why you are not permitted to write prop P(x, y) directly without specifying the domain is that, it might lead to serious strictness in the verification process. And since in naive set theory, the definition of proposition and the definition of functions all require you to specify the domain, Litex does so too.

We can objects in parameter list free objects.

That is why free variables can appear in the set of other free objects.

prop is_group(G set, mul function(G, G)G, e G, inv function(G)G)

is the short form of 

prop is_group(G, mul, e, inv):
    dom:
        mul $in function(G, G)G
        e $in G
        inv $in function(G)G

2. function as function name of a function

definition of functions whose return value is a function

fn f(param_list) fn(return_fn_set_list)return_fn_return_set

Here fn(sets)return_set should not include free objects in parameter list of f, because that is how the definition of function in naive set theory works.

f(param_list_1)(param_list_2) is how the function is applied.

param_list_1 needs to satisfy the dom of param_list

param_list_2 needs to be in the return_fn_set_list.

Maybe I need to add new keyword dom_of(), which takes in a prop name or fn name, and returns the domain of the prop or fn. A new keyword ret_set_of(), which takes in fn name, and returns the return set of the fn.

fn g(x SetX) y SetY:
    dom:
        $some_prop(x)

dom_of(g) has the following property:
forall x SetX:
    then:
        x $in dom_of(g)
    iff:
        $some_prop(x)

ret_set_of(g) has the following property:
ret_set_of(g) = SetY

## Use Iteration to prove forall

1. `is_indexable_set` (countable set)
   `index_set` might simultaneously include the properties of `set` and `is_indexable_set`.

2. `is_finite_set` applies to `indexable_set` (finite set, for the sake of verification through traversal)
   `finite_set` might simultaneously include the properties of `set` and `is_finite_set`.

3. `len` can only apply to `finite_set` (to provide an upper bound for traversal)

4. `[]`, `[[]]` can apply to `indexable_set`, but not to `set` (uniqueness of indexing)

The essence of index on `set` is:
There exists a function `fn index(N)setName`, and we know the `exist_prop m N` such that
`forall x, setName x = index(m)` (existence of index), and
if `x = index(m)` and `x = index(n)`, then `m = n` (uniqueness of index)

5. `prove_is_indexable_set` proves or constructs an `indexable_set`.
   `prove_forall_on_indexable_set` uses traversal to prove `forall`.
   This method is different from proving `forall` descriptively.

If we are only implementing 1-4, then there’s no need to make 1-4 built-in, because I can define them in Litex.
What’s truly important is point 5.
Without point 5, there is no traversal capability; and verification through traversal is independent of all existing logics.
It is precisely because traversal-based verification is needed that I need to introduce 1-5 to provide a unified syntax for users to define `indexable_set`.
Just using `or` to verify one by one is not sufficient, because `or` cannot work together with `len`.
In essence, the act of **counting** relies on extracting information from **literals**,
while LiTeX’s main functionality does **not** have the ability to **read literal information**.


[^1]: [Computer programming as an art](https://dl.acm.org/doi/10.1145/1283920.1283929)