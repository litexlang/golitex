# LiTeX

**LiTeX** is a **formal proof management system** inspired by **Lisp semantics** and **LaTeX syntax**. Its goal is to help **ANYONE** express and verify mathematics at **ANY LEVEL** as **ELEGANTLY** and **INTUITIVELY** as if they were using natural language. LiTeX transforms mathematical proof writing from a solitary endeavor into a collaborative experience, combining the rigor of formal verification with the familiarity of natural mathematical discourse. Whether you're a student learning basic algebra, a professor teaching advanced topology, or a researcher pushing the boundaries of mathematical knowledge, LiTeX provides the tools to express, verify, and share mathematical ideas with confidence. Details are available at [LiTeX GitHub Repository](https://github.com/litexlang/tslitex).

Feel free to share your suggestions and ideas to help us improve this open-source project—your feedback is invaluable!

---

## Setting up

1. Follow the instructions at [Deno Installation](https://docs.deno.com/runtime/getting_started/installation/) to download the latest version of **Deno**, the open-source runtime for TypeScript and JavaScript.
2. Run the following commands:
   ```bash
   cd ./tslitex
   deno run run.ts # Enter interactive mode
   deno run --allow-all run.ts YOUR_FILE_NAME # Run your file first, then enter interactive mode.
   ```

---

## A Tour of LiTeX

Let’s explore its syntax with examples, starting with syllogism:

### Example:

```plaintext
def mortal(something);
def something is human => {something is mortal};
let Socrates: Socrates is human;
Socrates is mortal;

if x : x is human => {x is mortal};
let god : god is not mortal;
prove_by_contradiction god is not human {god is mortal;} contradiction god is mortal;
```

Some core functionalities of LiTeX are included in this example

- **Concept Definition**: A new concept called `mortal` takes in one parameter. Another concept called `human` has corollary that it's `mortal`.
- **Variable Definition**: Two variable, `Socrates` and `Plato`, are introduced. Socrates has property that `Socrates is human` is true.
- **Expression Validation**: The user input an expression `if x : x is human => {x is mortal};`. LiTeX interpreter checks whether given expressions are true based on facts that the user already claimed. For example, we have already known `something is human => {something is mortal};`, so `x is mortal` is true under assumption `x is human`.
- **Proof**: in LiTeX, there are 2 ways of proving a result: prove or prove_by_contradiction.
- **Expression Values**: After checking, there are 4 types of outcomes: true, unknown, error, false.

---

### Expression Values

- **True**: The current expression is validated as true by the LiTeX interpreter.
- **Unknown**: The interpreter cannot verify the expression using known facts.
- **Error**: Indicates syntax or semantic errors.
- **False**: The negation of the current expression is validated as true.

## Syntax

#### Define New Concepts

```plaintext
def p(x);
def x is p1;
def q(x,y);
def p2(x) {if x: x is p1 => {x is p2} }
```

#### Check Expressions

```plaintext
Aristotle is human;
human(Aristotle);
Plato, Aristotle are human;
q(Plato, Aristotle);
Aristotle is not human; // False
let somebody; somebody is human; // Unknown
if x: x is not p1 => {x is not p2}; // True
```

#### Introduce New Variables

```plaintext
let x,y,z;
let 变量, 10.2, \_nonsense, 你好 world, I-AM-MEANINGLESS;
let a,b,c: a is p, q(b,c);
```

#### Assume Expressions

```plaintext
know if x: x is p2 => {x is p2};
know p(x), q(a,b);
know if x is p2 => {x is p2};
```

---

#### Not

```plaintext
let v1, v2, v3, v4, v5: not p(v1), v2 is not p, not v3 is p, v4,v5 are not p;
not p(v1);
let v6;
not p(v6); // Unknown
know not p(v6);
not p(v6); // True
```

#### If & Forall

```plaintext
if x: x is p2 => {x is p1}; // True
if x: x is p => {x is p1}; // Unknown
if x : x is p => {x is p}; // Always true
```

#### Prove & Prove by Contradiction

```plaintext
prove if x : x is p3 => {x is p1} {x is p2;}

let v10,v12: v10 is p2;
// prove factual-expression {proofs}
prove v10 is p1 {v10 is p2;}

// prove_by_contradiction factual-expression {proofs} contradiction expression;
know v12 is not p1;
prove_by_contradiction v12 is not p3 {v12 is p2} contradiction v12 is p1;
```

#### Exist & Have

```plaintext
def E(x): p(x) exist y {q(x,y)};
have E(x): v11; // Failed: p(v10) is unknown
know p(v11);
have E(x): v11; // True
q(x,v11);
```

#### Define Inline While Proving

```plaintext
if x: p(x) => {p(x)} [p1_1];
let v15: p(v15)[p1_2];
p1_1(x);
def nothing();
know if nothing() => {exist x,y {q(x,y)} [p1_3]};
have p1_3(): v16,17;
q(v16,v17); // True
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

- Interactive theorem dependency visualization
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
