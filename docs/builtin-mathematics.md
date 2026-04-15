# Builtin environment: mathematical summary

This document restates the Lit fragments concatenated into the kernel’s initial environment from `src/builtin_code/` in mathematical language, so axioms and conclusions can be checked against the intended semantics (mainly the ordered field \(\mathbb{R}\) plus a fragment of set theory).

---

## 1. Fundamental comparison (`fundamental_comparison`)

### 1.0 Decomposition of \(\le\) and \(\ge\)

\[
a \le b \Rightarrow (a = b \lor a < b),\qquad
a \ge b \Rightarrow (a = b \lor a > b).
\]

### Part A — Basic order and the nonnegative cone

#### 1.1 Order via differences for \(\le\) and \(<\)

\[
a \le b \iff 0 \le b - a,\qquad
a < b \iff 0 < b - a.
\]

#### 1.2 Squares: weak nonnegativity and strict positivity when \(a \neq 0\)

Facts of the form \(0 \le a^n\) for literal even integer \(n\), \(0 \le a\cdot a\) with equal factors, and \(0 \le a^n\) for literal integer \(n\) from \(0 \le a\) (with \(0 < a\) when \(n<0\)) are checked by the Rust builtin `verify_order_atomic_fact_numeric_builtin_only` (see `number_compare.rs`), not by a Lit `know` block in `fundamental_comparison.rs`.

The Lit fragment still asserts, if \(a \neq 0\):

\[
0 < a^2,\quad 0 < a\cdot a.
\]

#### 1.3 Closure of nonnegative (positive) quantities under addition, multiplication, division

If \(0 \le a\) and \(0 \le b\), then \(0 \le a+b\) and \(0 \le ab\); if \(0 < a\) and \(0 < b\), then \(0 < ab\); strict sum from \((0 < a \land 0 \le b) \lor (0 \le a \land 0 < b)\); quotient rules \(0 \le a/b\) when \(0 \le a\) and \(0 < b\), and \(0 < a/b\) when both are strictly positive—these closure steps are implemented in Rust (`verify_order_atomic_fact_numeric_builtin_only`), not in the remaining Lit `know` text for fundamental comparison.

### Part B — Real line order facts (`common_comparison_properties`, loaded after Section 1)

#### 1.5 Total order and disjunctive forms

For all \(a,b\), several equivalent disjunctions for a total order are given (e.g. \(a<b \lor a=b \lor a>b\)).

#### 1.6 Existential witnesses (standard \(\mathbb{R}\) intuition: dense, no endpoints)

For each \(a\) there is asserted a \(b\) with relations such as \(a>b\), \(a<b\), \(a=b\), \(a\neq b\), \(a\ge b\), \(a\le b\), and the same patterns with \(a,b\) swapped; there are also global existence claims for pairs \((a,b)\) realizing various order relations. **Note:** these hold on standard \(\mathbb{R}\); if the base domain changes, reassess whether they are too strong.

#### 1.7 Integral domain (zero product)

\[
ab = 0 \Rightarrow (a = 0 \lor b = 0).
\]

#### 1.8 Transitivity (via proposition symbols)

The kernel declares proposition predicates such as \(a\_lt\_c(a,b,c)\equiv (a<c)\), and knows:

\[
a<b,\ b<c \Rightarrow a<c;\quad
a\le b,\ b\le c \Rightarrow a\le c;
\]
\[
a>b,\ b>c \Rightarrow a>c;\quad
a\ge b,\ b\ge c \Rightarrow a\ge c.
\]

---

## 2. Common comparison properties (`common_comparison_properties`)

Section 1 Part B (trichotomy, witnesses, zero-product, transitivity) still comes from Lit fragments in this module. The **algebraic closure** facts below (2.1–2.4) are checked in Rust (`order_algebra_builtin.rs`, via `verify_order_atomic_fact_numeric_builtin_only`); only **2.5** remains as Lit `know` text in `BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES`.

### 2.1 Multiplication by nonnegative (nonpositive) factors preserves (reverses) order

If \(0\le x\) and \(a\le b\), then \(ax\le bx\) and \(xa\le xb\). If instead \(x\le 0\) and \(v\le u\), then \(ux\le vx\) and \(xu\le xv\) (same syntactic shape \( \cdot x\) / \(x\cdot\cdot\) with the complementary hypothesis on coefficients).

### 2.2 Addition

If \(a\le b\) and \(c\le d\), then \(a+c\le b+d\). If \(a\le b\) and \(c\le d\), then \(a-d\le b-c\).

Strict sums: \(a+c<b+d\) from \((a<b \land c<d)\), or \((a<b \land c\le d)\), or \((a\le b \land c<d)\).

### 2.3 Multiplication by strictly positive (strictly negative) factors

Analogous strict rules with \(<\) on outer order and \(0<x\) or \(x<0\) with the matching flip on coefficients.

### 2.4 Division by nonzero factors

If \(0<c\) and \(a\le b\), then \(a/c\le b/c\); if \(a<b\) then \(a/c<b/c\). If \(c<0\) and \(a\le b\), then \(b/c\le a/c\); if \(a<b\) then \(b/c<a/c\).

### 2.5 Equivalent restatements of the difference characterization

\[
a\le b \iff a-b\le 0,\qquad a<b \iff a-b<0.
\]

(On a typical ordered field this matches Section 1 Part A; it is duplicated to support order-closure proofs.)

---

## 3. Common functions (`common_functions`)

### 3.1 Absolute value

\[
|x| = \begin{cases} x & x\ge 0 \\ -x & x<0 \end{cases}
\]

Known: \(0\le |x|\); \(|x|=x \lor |x|=-x\); \(|xy|=|x|\,|y|\).

### 3.2 Maximum and minimum

\(\max(x,y)\) and \(\min(x,y)\) are defined by cases; bounds and disjunctions stating which branch is taken are known (e.g. \(x\le \max(x,y)\), \(\max(x,y)=x \lor \max(x,y)=y\), etc.).

---

## 4. Type families (`builtin_families`)

- \(\texttt{seq}(s) = \mathrm{Fn}(\mathbb{N}_{\mathrm{pos}}, s)\): infinite sequences indexed by positive integers.  
- \(\texttt{finite\_seq}(s,n) = \{ f : \{k\in\mathbb{N}_{\mathrm{pos}} \mid k\le n\} \to s \}\) (semantically: finite sequences bounded by length \(n\); surface syntax `fn(x N_pos: x <= n) s`).

---

## 5. Set operators (`set_operators`)

Write \(\in(z,A)\) for membership; \(\cup,\cap\) for union and intersection (keywords `union` / `intersect`); \(A\setminus B\) for `set_minus`; symmetric difference as `set_diff`.

### 5.1 Membership, union, and intersection

- \(z\in A \Rightarrow z\in A\cup B\); \(z\in B \Rightarrow z\in A\cup B\).  
- \(z\in A\cup B \Rightarrow z\in A \lor z\in B\).  
- \(z\in A \land z\in B \Rightarrow z\in A\cap B\); \(z\in A\cap B \Rightarrow z\in A \land z\in B\).  
- \(\neg z\in A \Rightarrow \neg z\in A\cap B\) (and similarly for \(B\)).

### 5.2 Inclusion and algebraic laws

- \(A\cap B\subseteq A\), \(A\cap B\subseteq B\); \(A\subseteq A\cup B\), \(B\subseteq A\cup B\).  
- Commutativity and associativity; absorption \(A\cup(A\cap B)=A\), \(A\cap(A\cup B)=A\); idempotence; empty set as neutral element.  
- Distributivity: \(A\cap(B\cup C)=(A\cap B)\cup(A\cap C)\), \(A\cup(B\cap C)=(A\cup B)\cap(A\cup C)\).

### 5.3 Difference and symmetric difference

- \(z\in A \land z\notin B \Rightarrow z\in A\setminus B\); converses yield \(z\in A\) and \(z\notin B\).  
- \(A\setminus B\subseteq A\).  
- \(\mathrm{set\_diff}(A,B) = (A\setminus B)\cup(B\setminus A)\).

### 5.4 Generalized union `cup(F)`

If \(Y\in F\) and \(z\in Y\), then \(z\in \bigcup F\) (written `cup(F)` in the source).

### 5.5 Finite-set counting

If \(A,B\) are `finite_set` and \(A\subseteq B\), then \(\mathrm{count}(A)\le \mathrm{count}(B)\); if \(A\supseteq B\) then \(\mathrm{count}(A)\ge \mathrm{count}(B)\).

---

## 6. How to use this document

- This is a **semantic summary**, not a substitute for the source; if Lit inside the Rust strings disagrees with this file, `src/builtin_code/*.rs` wins.  
- Section 1.1 and Section 2.5 (difference characterization vs. \(a-b\le 0\)) overlap on purpose so different proof paths in the kernel can reuse the same facts.  
- If you shrink the axiom set (e.g. drop redundant difference characterizations or duplicate square laws), update this document when you change the source.
