# The Litex Proof System

<div align="center">
<img src="assets/logo.png" alt="The LiTeX Logo" width="300">

<small>The Litex logo is a binary tree for two symbolic reasons: 1) As as data structure, binary trees are a perfect demonstration of how abstraction is handled, and the concept abstraction plays a fundamental role in both mathematics and programming.  2) As a diagram of procedures, it evokes the sense of "something leads to another thing" in mathematical discovery and software development. </small>

</div>

## About

_That language is an instrument of human reason, and not merely a medium for the expression of thought, is a truth generally admitted.
– George Boole_

Litex is a simple, user-friendly, universal formal language, designed to better manage the rising level of abstraction in mathematics and to bring the mathematical community into the digital age. It is daily tool to effortlessly to read, write, verify, and share mathematics.

**Since even children can express mathematics naturally, there must exist a design for a formal language that allows anyone to quickly understand and use it. The goal of Litex is to invent such a language.** While twisted syntax and semantics of traditional formal languages often causes a significant mental drain and a huge loss of clarity of proofs, Litex adopts a minimalism approach in language design so that the complexity of writing mathematics does not exceed that of mathematical reasoning itself, allowing users to focus without being distracted by limitations imposed by formal languages.

## Design principles of Litex

_Conceptual integrity is central to product quality.
-- Fred Brooks, Turing award recipient_

### Similarities and differences between math and programming
Litex is the bridge between the programming world and math world. The reason Litex can achieve a uniform language with such concise syntax and semantics to express the complex world of mathematics is that it clearly recognizes both the differences and commonalities between mathematics and programming.We start by investigating similarities and differences between math and programming.

#### Similarities

_Mathematics... is nothing more than a game played according to certain simple rules with meaningless marks on a paper.
-- David Hilbert_

##### The tasks
1. The basic elements are symbols with properties. In most cases property means relationship with other symbols.
2. They both follow a rather small rule sets that everyone understands but turns out to be rather difficult and complicated when symbols combined with one another and leads to new symbols and rules leads to new rules(procedures combined with other procedures and leads to new procedures)
3. Fundamentally, CS == science of abstraction and math == abstraction.
Stroustrup: My best tool for efficiency and performance is abstraction.

##### The practice od programming and doing math
1. write code 
2. run and debug
3. read others' code and share my code


#### Differences

_The computer revolution is a revolution in the way we think and in the way we express what we think. The essence of this change is the emergence of what might best be called procedural epistemology­ the study of the structure of knowledge from an imperative point of view, as opposed to the more declarative point of view taken by classical mathematical subjects. Mathematics provides a framework for dealing precisely with notions of "what is." Computation provides a framework for dealing precisely with notions of "how to."
-- Structure and Interpretation of Computer Programs_

##### The tasks
1. Codes are used to be executed, to have effects of any forms including arithmetic calculation, data manipulation, system control, user interaction and more. Execution in math verification means searching old relationships and build new relationships on top of them. Since building relationships is only one form of effects that programs can have, we can use programming to do math verification. So math can be viewed as a domain language which does not need to be as universal as programming languages. Functionalities like doing arithmetic operations can be implemented as plugins instead of the main part of the language. We take advantage of this property to create a language that is more close to math than traditional turing-complete-language formal languages by restricting ourselves to functionalities that mathematical reasoning only needs.
2. Math is for explaining, Programming is for making a difference.
3. As formal 
4. 

#### Relationships with mainstream programming languages

_Simplify, Simplify, Simplify.
- Steve Jobs_

_If I have seen further, it is by standing on the shoulders of giants.
-- Isaac Newton_

The design of Litex is inspired mainly by designs of existing programming languages like Python, GoLang, C, C++, Rust, JavaScript/TypeScript, Lisp instead of theoretical logic. I implemented this language for everyday usage, not mental entertainment. Unlike predecessors, Litex uses programming principles to understand mathematical reasoning, rather than the other way around.

Main syntax design includes
1. Python scope, Python "less typing approach"
2. Go type syntax, package management
3. Concept inspired by C++ Concept, Python Protocol, Go Generics
4. Tex separation of logical expressions (normal words) and mathematical expressions.
5. Everything is a symbol and everything(var, fn, prop) is first-citizen inspired by Lisp and its descendants.
6. Introduce OOP to math. OOP built by interface instead of inheritance.

Corresponding between math and programming
1. basic element of math: var, fn, prop. they are all represented as symbols
2. Math set == type. types are used to define members, including methods, propositions, operator overloads. this is where oop lies.
3. a class of sets: concept
4. fact: forall => introduce new vars, if => introduce further condition, basic prop: called just as if a function that returns bool
5. every expression return 4 kinds of values: True, Unknown, False, Error
6. symbols can be combined to be new symbols. The way is using operators(functions). fn in litex does not execute, it is just a way of combining previously defined symbols.
7. prop combined with other prop leads to new prop
8. prop is named fact. there are also unnamed facts.
9. exist is a special prop. it should be referred to as how normal props are referenced.
10. programmers work with one another. package system helps you maintain your own proofs and easily import others' result.
11. when user input a fact, it's verified by the interpreter. If it's true, it's remembered for future use. Otherwise nothing happens.
11. forall facts can be "called" to verify a input fact without giving it a name.

#### Simplicity is the core of Litex

_Beautiful is better than ugly.
Explicit is better than implicit.
Simple is better than complex.
The Zen of Python_

_The most important single aspect of software development is to be clear about what you are trying to build.
-- Bjarne Stroustrup, inventor of C++_


<!-- LiTeX is a formal proof management system that makes expressing and verifying mathematics accessible to EVERYONE. Unlike traditional formal languages that force users to distort their mathematical expressions to fit what the formal language can represent, LiTeX seamlessly bridges the gap between a user’s thought process and the expression of their logic by combining the structured clarity of LaTeX for mathematical notation with Lisp’s philosophy of “Everything is a symbol” (This is also the origin of LiTeX's name: a combination of Lisp semantics and LaTeX syntax) .

The current state of LiTeX is that, it requires significantly less typing—about 50% less than LaTeX and 80% less than Lean4 to implement basic set theory, syllogisms, and fundamental natural number theory. For example, I chose to implement the opening chapters of Professor Terrence Tao’s _Analysis I_ as a case study. You can see a comparison of Lean4, LaTeX, and LiTeX on the LiTeX website. Please visit https://litexlang.org/ for more details.

The project has been adopted early by several prominent entities, including being used as training material by DeepMath and OpenMMLab, leading Chinese institutions specializing in large mathematical models and language models, and as an interactive textbook by the Department of Mathematics at Fudan University.

It’s exciting to see that, due to its intuitive syntax and shallow learning curve, LiTeX is not just an auxiliary tool but practical for everyday tasks. This opens up the potential for a much larger user base. With its low time cost, LiTeX can transform most mathematics textbooks into interactive ones and translate classical theorems. In the long term, LiTeX will enable large-scale mathematical collaborations, similar to how programmers collaborate on GitHub. Larger, more logically coherent datasets will make mathematical models and rule-based reasoning systems stronger and better at reasoning.

Developing a new programming language often starts as the effort of a single individual, but its growth and long-term success depend on the strength of the community around it. A thriving language needs user feedback, collaborative creativity from developers, and tools to support its ecosystem, such as package management, website resources, and plugins for mainstream IDEs like VSCode. With the support of this funding, I will be able to focus on improving the user experience and iterating on LiTeX to make it more accessible and robust. -->


## About the author and join Litex Project
The inventor of Litex Jiachen Shen is a hacker with a math degree. The development and design process of Litex is no different than most softwares: design, implement, test, debug, publish, receive feedback and redesign. The original version of Litex is very different to what it is today. Since Litex is still under development, it's inevitable that today's Litex might be even more different than what it is in the future. The language will never be a success without its users and contributors. Feel free to issue your suggestions and ideas to help me improve this open-source project—your feedback is invaluable.

---

## Setting up Node.js and npm to run tslitex

This LiTeX interpreter is written in TypeScript. So Node.js is essential for running litex projects because it provides the JavaScript runtime environment needed to execute TypeScript (.ts) files. Here's a concise guide to setting up Node.js and other tools:

1. Install:

- Visit [nodejs.org](https://nodejs.org/). Download the latest LTS (Long Term Support) version
- Visit [git](https://git-scm.com/). Download the latest git.

2. Verify Installation:

   ```bash
   node --version
   npm --version
   git --version
   ```

3. Run the Project:
   ```bash
   git clone https://github.com/litexlang/tslitex.git
   cd ./tslitex
   ts-node L_Test.ts examples/syllogism.litex
   ```

That's it! These steps will get you set up with Node.js and ready to run your litex project.

## A Tour of LiTeX

The following example compares the implementation of syllogism across three different languages. The LaTeX version represents natural language, Lean4 illustrates the capabilities of current mainstream formal languages, and LiTeX exemplifies a language that is both formal enough to enable rigorous checking and flexible enough to let users express mathematics as if they were speaking in natural language.

```
/* LaTeX version
Define a property called "human", which takes in one parameter.
Define a property called "mortal", which takes in one parameter.
Define a variable called "Socrates", which has property human.
*/

/* Lean4 version
variable (Human : Type)
variable (Mortal : Human → Prop)
variable (Socrates : Human)
*/

/* LiTeX version */
concept something is human;
concept something is mortal;
let Socrates: Socrates is human;

/* LaTeX version
It is known fact that all human is mortal.
Claim: Socrates is mortal.
*/

/* Lean4 version
axiom all_humans_are_mortal : ∀ (x : Human), Mortal x
theorem socrates_is_mortal : Mortal Socrates := by
  apply all_humans_are_mortal
#check socrates_is_mortal
*/

/* LiTeX version */
know if x: x is human {
  x is mortal
};
Socrates is mortal;

/* LaTeX version
Claim: all human is mortal.
*/

/* Lean4 version
def all_humans_will_die : Prop := ∀ (x : Human), Mortal x
theorem prove_all_humans_will_die : all_humans_will_die := all_humans_are_mortal
*/

/* LiTeX version */
if x: x is human {x is mortal};

/* LaTeX version
Define a variable called "god", it has property that it is not mortal.
Prove by contradiction: god is not human.
*/

/* Lean4 version
#check prove_all_humans_will_die
variable (God : Type)
variable (god : God)
axiom god_is_immortal : ¬ Mortal God
theorem god_is_not_human : God ≠ Human :=
  by
  intro h
  have god_is_mortal : Mortal God := all_humans_are_mortal god,
  contradiction
*/

/* LiTeX version */
let god: not god is mortal;
prove_by_contradiction not god is human {
  god is mortal;
}  god is human;
not god is human;
```

### Explanations

Some core functionalities of LiTeX are included in this example

- **Concept Definition**: New concepts called `mortal` and `human` are declared. They both have parameter size one. In addition, all variables that has property `human` has property `mortal`. There are many ways of calling a concept: if the concept C like mortal is only related to one parameter, you can either use xxx is C or $C(xxx). If the concept like '1 < 2' is related to multiple parameters, you should use $C(v1,v2...). If the concept like '1 < 2' is related to just 2 symbols, you can write var1 C var2.
- **Variable Definition**: A variable called `Socrates` is introduced. Socrates has property `human`. Another variable called `god` is introduced, with property `not mortal`.
- **Expression Validation**: Expressions like `Socrates is mortal` are called `factual expression to be checked`. LiTeX checks their validation based on `known facts` . For example, we have already known `if x: human(x) {mortal(x)};` and `Socrates is human`, so `Socrates is mortal` is true . If an `factual expression to be checked` can not be checked by LiTeX interpreter, LiTeX prints out `unknown`. Notice `factual expression` can work both as requirement for another factual expression (e.g. `human(x)` is requirement for another fact `if x: human(x) { mortal(x)};` ) or as an `factual expression to be checked`.
- **Proof**: in LiTeX, there are 2 ways of proving a result: `prove` or `prove_by_contradiction`. In the example, we prove `not human(god)` by using `prove_by_contradiction`.
- **Expression Values**: After checking, there are 4 types of outcomes: `true`, `unknown`, `error`, `false`.

### Comparison with Lean4

1. Unlike Lean4, a variable (or symbol) in LiTeX can possess multiple properties rather than being limited to a single type. In LiTeX, concept declarations are distinctly separated from variable declarations. For instance, concepts like "human" or "mortal" are defined using the `def` keyword, while variables such as "Socrates" are declared with `let`.

2. LiTeX employs a declarative syntax that eliminates the need to explicitly "name" facts for later use in proofs. Users do not need to inform the interpreter about which facts are being used to establish a proof. This removes the necessity of naming every fact, a practice common in languages like Lean4, where naming is required to direct the interpreter to specific facts. In LiTeX, this redundancy is avoided as the language automatically verifies expressions.  
   For example, constructs like `theorem socrates_is_mortal` or `apply all_humans_are_mortal` become unnecessary. Similarly, commands like `#check` are redundant because, in LiTeX, any expression not starting with a keyword is assumed to be "an expression to be checked."  
   In summary, a simple statement like "Socrates is mortal" in LiTeX achieves multiple objectives:

   1. LiTeX performs a tree search through the fact base to verify its validity.
   2. If validated, the expression itself is recorded as a new fact.

In everyday mathematical writing, we typically state facts directly, leaving readers to infer which previously established results are being used. Occasionally, we might explicitly write “because xxx, therefore yyy” to spare readers the effort of making these inferences, but such instances are relatively rare. If every step required an explicit “because xxx,” we would need to assign names to every fact for later reference—an approach mandated by Lean 4 but unnecessary in LiTeX. This naming requirement forces readers and writers to memorize and invent numerous labels, detracting from the core reasoning process. The challenge becomes even more pronounced when working with someone else’s code, as users must first familiarize themselves with all the named facts before they can begin reasoning effectively. As the old saying goes: the most difficult thing in CS is naming, LiTeX spares you from that huge effort.

3. By eliminating the need for explicitly naming facts for reuse in proofs, LiTeX produces more concise and streamlined code compared to Lean4.

For more illustrative examples, please visit the ./examples directory.

---

### Expression Values

- **True**: The current expression is validated as true by the LiTeX interpreter.
- **Unknown**: The interpreter cannot verify the expression using known facts.
- **Error**: Indicates syntax or semantic errors.
- **False**: The negation of the current expression is validated as true.

# Logical Concept System Examples

## Concept Definition

```
concept $p(x);
concept x is p1;
concept $q(x,y);
concept $p2(x) {
  // properties of a defined concept are written in the following block.
  if x: x is p1  {
    x is p2
  }
}
concept $p3(x) {if x: $p3(x)  {$p(x)} , if x: $p(x)  {$p3(x)} }
let x,y: $p3(x), $p(y);
$p(x), $p3(y);
concept $p(x); // error: you can not declare a concept twice.
```

## Expression Checking

```
// read a tour of LiTeX
```

## Variable Introduction

```
// read a tour of LiTeX
```

## Not Operator

```
// read a tour of LiTeX
```

## If-type Factual Expression

`if-type factual expressions` works as for-any expressions in math.

```
concept $p1(x); concept $p(x); concept $p2(x) {
  if x: x is p2  {x is p1}  // properties of p2
}
if x: x is p2  {x is p1}; // True
if x: x is p  {x is p1}; // Unknown
if x : x is p  {x is p}; // Always true
```

## Prove and Contradiction

```
concept $p3(x); concept $p2(x); concept $p1(x);
know if x: $p3(x) {$p2(x)}, if x : $p2(x)  {$p1(x)} ;
prove if x : x is p3  {x is p1} {
  x is p2;
}
let v1,v2: v1 is p2; // prove factual-expression {proofs}
prove v1 is p1 {v1 is p2;}
know not $p1(v2);
prove_by_contradiction not $p3(v2) {v2 is p2;}  v2 is p1;
```

## Parameter Passing with Subset Demonstration

```
concept $set(x); concept $subset(A,B); concept $in(x,A);

// Subset definition: if x is in A, then x must be in B
know if A,B: $subset(A,B) {if x: $in(x,A) {$in(x,B)}};

// Alternative subset definition
know if A,B: if x: $in(x,A) {$in(x,B)} {$subset(A,B)};

// Example usage
let A,B,C,D,E,F;
know $subset(A,B);
let x: $in(x,A);
$in(x,B)[A,B;x];  // Proof of membership
```

## Transitivity Demonstration

```
// Define a less-than relation with transitivity
def $<(x,y);
know if x,y,z: $<(x,y), $<(y,z)  {$<(x,z)};

// Example of transitive property
let a,b,c: $<(a,b), $<(b,c);
$<(a,c)[a,b,c];  // Proving transitivity
```

## composite symbol declaration (use natural number definition as example)

```
concept $natural(x);
concept $nat_eq(x,y);

let 0: 0 is natural;

operator \++{n}: n is natural;

know if n: n is natural {
    \++{n} is natural;
};

know if x {
    not $nat_eq(0, \++{x});
};

know if x,y: $nat_eq(x,y) {
    $nat_eq(\++{x}, \++{y});
};

know if x,y: $nat_eq(\++{x}, \++{y}) {
    $nat_eq(x,y);
};


```

## TODO

### Object Oriented Programming

It's hard for a programmer to write clean and "elegant" code. It's even harder for a group of programmers work together and at the same write good code. When It comes to write "math code", i.e. proofs, things are even more complicated. Operators like +, \* overloads everywhere, Sometimes a symbol can have many meanings in the same paper, different people might give seemingly completely different definition and naming to two equivalent concepts.

To help mathematicians share and organize their thoughts better, LiTeX is going to introduce an object oriented way of writing math, which can make the writing and reading process even more intuitive and maintainable. Different syntax, even if they are equivalent, have enormously different "psychological" hint to users, I hope I can design that better.

See examples/oop_set_theory.litex for example.

### function can return concept, variable, relation, function

Math is a very generic language. Compared with traditional programming languages, LiTeX should be designed to be much more flexible to meet people's needs. It's extremely hard to strike the right balance between flexibility (easy for one man to write code) and organizable (easy for others to understand and work on the code). However, the basic idea behind math is pretty clear. As the simple notion of "Turing Machine" is theoretically equivalent to modern computers, the basic idea and element of math is pretty simple: 1. everything is a symbol 2. everything means a variable or a concept or a function or a relation. To make "something is related to something" and "something generates another thing" easier to express, I allow functions to have return all of them.

## More about LiTeX

### Advancing Collaborative Mathematics

LiTeX introduces rigorous verification into mathematical collaboration, enabling confident contributions to large-scale projects. Like distributed version control in software, its verification engine ensures correctness and facilitates trust across the mathematical community.

### Enhanced Verification Workflow

By automating logical inconsistency detection, LiTeX reduces verification overhead in mathematical research. Researchers and reviewers can focus on innovative aspects rather than mechanical verification, maintaining rigor while accelerating review.

### Accessible Formal Mathematics

Through its carefully designed specification language, LiTeX bridges intuitive mathematical thinking and formal verification. The natural syntax maintains precision while remaining accessible to both researchers and students, promoting broader adoption of formal methods.

### Educational Integration

LiTeX serves as an advanced educational tool offering:

- Interactive math textbook: Theorem, Concept dependency visualization
- Flexible proof granularity at multiple levels
- Clear exposition of mathematical relationships
- Systematic mathematical intuition building

### Universal Verification Framework

LiTeX's methodology extends beyond mathematics to any domain with formal verification requirements:

- Software verification and validation
- Protocol correctness proofs
- Hardware design verification
- Formal specification validation
- Business rule consistency checking
- System architecture verification

### Mathematical Knowledge Base Development and AI Integration

The platform advances artificial intelligence systems through:

1. **Structured Knowledge Base**

   - Formally verified mathematical content
   - Hierarchical theorem relationships
   - Explicit proof strategies and patterns
   - Standardized verification procedures

2. **AI Training Enhancement**

   - High-quality, verified training datasets
   - Precise reasoning patterns and workflows
   - Structured logical dependencies
   - Mathematical reasoning templates
   - Custom verification rule sets
   - Automated consistency checking
   - Scalable verification frameworks

3. **Model Improvement Framework**
   - Systematic error detection
   - Reasoning path validation
   - Logical consistency enforcement
   - Performance benchmarking
   - Verification-guided training
