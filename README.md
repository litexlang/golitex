# The LiTeX Proof System

<div align="center">
<img src="assets/logo.png" alt="The LiTeX Logo" width="300">

<small>The LiTeX logo is a tree for two symbolic reasons: 1) binary tree is the basic data structure of Lisp , and LiTeX is strongly influenced by Lisp 2) it evokes the sense of "something leads to another thing" in mathematical discovery.</small>

</div>

## About

_Mathematics... is nothing more than a game played according to certain simple rules with meaningless marks on a paper.
-- David Hilbert_

LiTeX is a formal proof management system that makes expressing and verifying mathematics accessible to everyone, from elementary students to university professors. With a design as intuitive as natural language, LiTeX requires significantly less typing—about 50% less than LaTeX and 80% less than Lean4 (see examples/setTheory.litex for details). That's why unlike other formal proof languages, LiTeX is practical for everyday tasks, not just an auxiliary tool.

_The computer revolution is a revolution in the way we think and in the way we express what we think. The essence of this change is the emergence of what might best be called procedural epistemology­ the study of the structure of knowledge from an imperative point of view, as opposed to the more declarative point of view taken by classical mathematical subjects. Mathematics provides a framework for dealing precisely with notions of "what is." Computation provides a framework for dealing precisely with notions of "how to."
-- Structure and Interpretation of Computer Programs_

LiTeX seamlessly bridges the gap between a user’s thought process and the expression of their logic by combining the structured clarity of LaTeX for mathematical notation with Lisp’s philosophy of “everything is a symbol.” This fusion empowers users to express complex ideas intuitively and fluidly.

Another factor that sets LiTeX from other proof systems apart is its commitment to declarative syntax. Users simply write what they believe to be true, leaving it to the interpreter to verify correctness. By striking a perfect balance between the imperative mindset of computer programming and the declarative elegance of mathematical writing, LiTeX redefines accessibility and intuitiveness in formal languages.

<font color="red">Feel free to share your suggestions and ideas to help me improve this open-source project—your feedback is invaluable!</font>

The basic elements of **LiTeX** called `symbols` have roots in Lisp's fundamental approach, drawing inspiration from its powerful macro system to handle literal manipulations in math. `Symbols` can have `facts` related to them, with some facts leading to further facts—mirroring how mathematical reasoning naturally progresses. Read `A Tour of LiTeX` below for further information.

## Why LiTeX matters

**LiTeX** transforms mathematical collaboration by introducing rigorous verification into research workflows. By automating mechanical proof validation, the system enables mathematicians to focus on innovative aspects rather than tedious verification. It also makes interactive textbooks and large-scale collaborative projects possible. Full details are available at the [LiTeX GitHub Repository](https://github.com/litexlang/tslitex).

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
  x is mortal;
};
/* Socrates is mortal; */

/* LaTeX version
Claim: all human is mortal.
*/

/* Lean4 version
def all_humans_will_die : Prop := ∀ (x : Human), Mortal x
theorem prove_all_humans_will_die : all_humans_will_die := all_humans_are_mortal
*/

/* LiTeX version */
/* if x: x is human {x is mortal}; */

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

- **Concept Definition**: New concepts called `mortal` and `human` are declared. They both have parameter size one. In addition, all variables that has property `human` has property `mortal`. There are 2 ways of calling a concept: if the concept C like mortal is only related to one parameter, you can either use xxx is C or $C(xxx). If the concept like '1 < 2' is related to multiple parameters, you should use $C(v1,v2...).
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
concept $p3(x) {if x: p3(x)  {p(x)} , if x: p(x)  {p3(x)} }
let x,y: p3(x), p(y);
p(x), p3(y);
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

def_composite \++{n}: n is natural;

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
