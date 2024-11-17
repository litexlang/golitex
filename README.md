## LiTeX

**LiTeX** is a formal proof management system inspired by **Lisp semantics** and **LaTeX syntax**. Its goal is to help **ANYONE** express and verify mathematics at **ANY LEVEL** as **ELEGANTLY** and **INTUITIVELY** as if they were using natural language.

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

## Getting Started

LiTeX is inspired by Lisp semantics and LaTeX syntax to enable intuitive and natural language-like expression of proofs. More details are available at [tslitex GitHub Repository](https://github.com/malloc-realloc/tslitex).

---

## A Tour of LiTeX

Let’s explore its syntax with examples, starting with syllogism (三段论):

### Example:

```plaintext
def mortal(something);
def something is human => {something is mortal};
let Socrates , Plato: Socrates is human;
Socrates is mortal;
if x : x is human => {x is mortal};
let god : god is not mortal;
prove_by_contradiction god is not human {god is mortal;} contradiction god is mortal;
```

---

### Expression Values

- **True**: The current expression is validated as true by the LiTeX interpreter.
- **Unknown**: The interpreter cannot verify the expression using known facts.
- **Error**: Indicates syntax or semantic errors.
- **False**: The negation of the current expression is validated as true.

---

### Syntax

#### Define New Concepts

```plaintext
def p(x);
def x is p1;
def x is p2 => {x is p1};
def x is p3 <=> {x is p2};
def x is p4: x is p3 => {x is p1};
def q(x,y);
def E(x): p(x) exist y {q(x,y)};
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

### Logical Constructs

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
