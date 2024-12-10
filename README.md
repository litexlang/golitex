# LiTeX

## Introduction

**LiTeX** is a **formal proof management system** inspired by **Lisp semantics** and **LaTeX syntax**. Its goal is to help **anyone** express and verify mathematics at **any level** as **elegantly** and **intuitively** as if they were using **natural language**. In many cases, LiTeX enables users to write the same piece of math in 10% lines of code compared with other formal languages, which is even shorter and efficient than words written in LaTeX.

The goal of **LiTeX** is to introduce rigorous verification into mathematical collaboration, enabling confident contributions to large-scale projects. It makes interactive textbook/paper possible and allows math researchers to focus on innovative aspects rather than mechanical verification. Details are available at [LiTeX GitHub Repository](https://github.com/litexlang/tslitex).

Feel free to share your suggestions and ideas to help me improve this open-source project—your feedback is invaluable!

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

LiTeX is a very simple and powerful language. It takes Lean4 nearly 100 lines of code to implement syllogism from scratch, but LiTeX can write that in a way that even people who have not learned LiTeX can understand. Here is how:

```
def mortal(something);
def human(something);
know if x: human(x) {
  mortal(x)
};

let Socrates: Socrates is human;
Socrates is mortal;
if x: x is human {x is mortal};

let god: not god is mortal;
prove_by_contradiction not human(god) {
  god is mortal;
} god is mortal;
```

Some core functionalities of LiTeX are included in this example

- **Concept Definition**: New concepts called `mortal` and `human` are declared. They both have parameter size one. In addition, all variables that has property `human` has property `mortal`.
- **Variable Definition**: A variable called `Socrates` is introduced. Socrates has property `human`. Another variable called `god` is introduced, with property `not mortal`.
- **Expression Validation**: Expressions like `Socrates is mortal` are called `factual expression to be checked`. LiTeX checks their validation based on `known facts` . For example, we have already known `if x: human(x) {mortal(x)};` and `Socrates is human`, so `Socrates is mortal` is true . If an `factual expression to be checked` can not be checked by LiTeX interpreter, LiTeX prints out `unknown`. Notice `factual expression` can work both as requirement for another factual expression (e.g. `human(x)` is requirement for another fact `if x: human(x) { mortal(x)};` ) or as an `factual expression to be checked`.
- **Proof**: in LiTeX, there are 2 ways of proving a result: `prove` or `prove_by_contradiction`. In the example, we prove `not human(god)` by using `prove_by_contradiction`.
- **Expression Values**: After checking, there are 4 types of outcomes: `true`, `unknown`, `error`, `false`.

---

### Expression Values

- **True**: The current expression is validated as true by the LiTeX interpreter.
- **Unknown**: The interpreter cannot verify the expression using known facts.
- **Error**: Indicates syntax or semantic errors.
- **False**: The negation of the current expression is validated as true.

## Syntax

# Logical Concept System Examples

## Concept Definition

```
def p(x);
def x is p1;
def q(x,y);
def p2(x) {
  // properties of a defined concept are written in the following block.
  if x: x is p1  {
    x is p2
  }
}
def p3(x) {if x: p3(x)  {p(x)} , if x: p(x)  {p3(x)} }
let x,y: p3(x), p(y);
p(x), p3(y);
def p(x); // error: you can not declare a concept twice.
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
def p1(x); def p(x); def p2(x) {
  if x: x is p2  {x is p1}  // properties of p2
}
if x: x is p2  {x is p1}; // True
if x: x is p  {x is p1}; // Unknown
if x : x is p  {x is p}; // Always true
```

## Prove and Contradiction

```
def p3(x); def p2(x); def p1(x);
know if x: p3(x) {p2(x)}, if x : p2(x)  {p1(x)} ;
prove if x : x is p3  {x is p1} {
  x is p2;
}
let v1,v2: v1 is p2; // prove factual-expression {proofs}
prove v1 is p1 {v1 is p2;}
know not p1(v2);
prove_by_contradiction not p3(v2) {v2 is p2;}  v2 is p1;
```

## Parameter Passing with Subset Demonstration

```
def set(x); def subset(A,B); def in(x,A);

// Subset definition: if x is in A, then x must be in B
know if A,B: subset(A,B) {if x: in(x,A) {in(x,B)}};

// Alternative subset definition
know if A,B: if x: in(x,A) {in(x,B)} {subset(A,B)};

// Example usage
let A,B,C,D,E,F;
know subset(A,B);
let x: in(x,A);
in(x,B)[A,B;x];  // Proof of membership
```

## Transitivity Demonstration

```
// Define a less-than relation with transitivity
def <(x,y);
know if x,y,z: <(x,y), <(y,z)  {<(x,z)};

// Example of transitive property
let a,b,c: <(a,b), <(b,c);
<(a,c)[a,b,c];  // Proving transitivity
```

## composite symbol declaration (use natural number definition as example)

```
def natural(x);
def nat_eq(x,y);

let 0: 0 is natural;

let_composite \++{n}: n is natural;

know if n: n is natural {
    \++{n} is natural;
};

know if x {
    not nat_eq(0, \++{x});
};

know if x,y: nat_eq(x,y) {
    nat_eq(\++{x}, \++{y});
};

know if x,y: nat_eq(\++{x}, \++{y}) {
    nat_eq(x,y);
};

know if P: is_property(P), P(0), if n: n is natural, P(n) {
    P(\++{n});
} {
    if m: m is natural {
        P(m);
    };
};

```

## Potential of LiTeX

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

LiTeX integrates verification with collaboration to create a robust platform for mathematics education and research, promoting both rigor and broad participation in mathematical advancement.

```

```
