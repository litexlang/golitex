# Litex System Map And Glossary

This page is the complete reader-facing map of Litex's core public syntax.
It lists every glossary entry counted by the current Syntax Reference:
**72 Object forms, 52 Fact forms, and 63 Statement forms**.

```text
Object -> Fact -> Statement -> growing proof context
```

- An **Object** is a mathematical value or expression.
- A **Fact** is a proposition about objects.
- A **Statement** defines something, verifies something, controls a proof, or
  changes the current environment.
- The **proof context** contains the names, definitions, verified facts, and
  inferred consequences available to the next statement.

Each row answers four questions: what the form means in ordinary mathematics,
what its Litex shape is, what it looks like in use, and whether it changes the
proof context. These are public glossary entries, not internal AST counts.

Jump to [Objects](#object-glossary), [Facts](#fact-glossary),
[Statements](#statement-glossary),
[definition forms](#how-definitions-are-written), or
[verification](#how-verification-works).

## Object Glossary

An object does not change the proof context by itself. It becomes relevant when
a statement binds it, defines it, or uses it inside a fact.

### Names And Bound Objects (10)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| A previously introduced object | `name` | `x` | No change; resolves an existing binding. |
| A name exported by a module or source | `Module::name` | `Nat::zero` | No change; resolves a qualified binding. |
| A universally quantified parameter | `forall name Set:` | `x` in `forall x R:` | Creates a local parameter inside the `forall`. |
| A parameter of a definition | `kind name(param Set):` | `x` in `prop p(x R):` | Creates a local parameter while the definition is checked. |
| An existential witness variable | `exist name Set st {...}` | `x` in `exist x R st {x = 1}` | Binds a witness only inside the existential body. |
| The variable of a set comprehension | `{name Set: facts}` | `x` in `{x R: x >= 0}` | Binds an element only inside the comprehension. |
| A function parameter | `fn(name Set) ReturnSet` | `x` in `fn(x R) R` | Binds an input inside the function type or body. |
| An induction parameter | `by induc name from base:` | `n` in `by induc n from 0:` | Binds the induction variable in the generated subproofs. |
| An executable implementation parameter | `have algo for f(name):` | `x` in `have algo for f(x):` | Binds an input while the implementation is checked. |
| A struct field name | a field declared inside `struct Name:` | `x` in a `struct Point` field condition | Adds no binding by itself; the enclosing `struct` stores the field. |

### Numeric And Operator Objects (12)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| An exact normalized number | numeric literal | `2`, `3.5` | No change; forms a numeric object. |
| Addition | `a + b` | `x + y` | No change; forms an arithmetic object. |
| Subtraction | `a - b` | `x - y` | No change; forms an arithmetic object. |
| Multiplication | `a * b` | `x * y` | No change; forms an arithmetic object. |
| Division | `a / b` | `x / y` | No change; requires the divisor to be usable and nonzero when checked. |
| Integer remainder | `a % b` | `n % 2` | No change; forms an integer remainder object. |
| Exponentiation | `a^n` | `x^2` | No change; forms a power object. |
| Absolute value | `abs(a)` | `abs(x)` | No change; forms a numeric object. |
| Square root | `sqrt(a)` | `sqrt(x)` | No change; forms a numeric object subject to its domain conditions. |
| Logarithm with an explicit base | `log(base, a)` | `log(2, x)` | No change; forms a numeric object subject to base and argument conditions. |
| Maximum of a finite set | `finite_set_max(S)` | `finite_set_max(S)` | No change; requires a suitable nonempty finite set when checked. |
| Minimum of a finite set | `finite_set_min(S)` | `finite_set_min(S)` | No change; requires a suitable nonempty finite set when checked. |

### Set, Function, And Tuple Objects (28)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| A builtin number set or common numeric subset | `N_pos`, `N`, `Z`, `Q`, `R`, and sign/nonzero variants | `R_pos`, `Q_nz`, `Z_neg` | No change; resolves a builtin set object. |
| Binary union | `union(A, B)` | `union(A, B)` | No change; forms a set object. |
| Binary intersection | `intersect(A, B)` | `intersect(A, B)` | No change; forms a set object. |
| Relative set subtraction | `set_minus(A, B)` | `set_minus(A, B)` | No change; forms a set object. |
| Symmetric difference | `set_diff(A, B)` | `set_diff(A, B)` | No change; forms a set object. |
| Union over a family of sets | `big_union(F)` | `big_union(F)` | No change; forms a set object from a family. |
| Intersection over a family of sets | `big_intersect(F)` | `big_intersect(F)` | No change; forms a set object from a family. |
| Power set | `power_set(A)` | `power_set(A)` | No change; forms the set of subsets of `A`. |
| A displayed finite set | `{a, b, ...}` | `{1, 2, 3}` | No change; forms a finite-set object. |
| A subset defined by a condition | `{x S: facts}` | `{x R: x >= 0}` | No change; forms a set object with a local binder. |
| Replacement by a functional relation | `replacement(P, A)` | `replacement(P, A)` | No change; requires a usable binary predicate and unique outputs. |
| A function space with optional domain conditions | `fn(params: facts) ReturnSet` | `fn(x R: x >= 0) R` | No change; forms a set of functions. |
| An anonymous function value | `fn(params) ReturnSet {body}` | `fn(x R) R {x + 1}` | No change; forms a function object after its body is checked. |
| Function application, including curried application | `f(args)` | `f(2)`, `f(x)(y)` | No change; forms the returned object when arguments satisfy the domain. |
| Cartesian product | `cart(A, B, ...)` | `cart(A, B)` | No change; forms a product set. |
| Number of factors in a Cartesian product | `cart_dim(C)` | `cart_dim(cart(A, B))` | No change; forms a positive-integer object. |
| Projection from a Cartesian product | `proj(C, i)` | `proj(cart(A, B), 1)` | No change; forms a projection function. |
| A tuple value | `(a, b, ...)` | `(1, 2)` | No change; forms an ordered tuple object. |
| Tuple length | `tuple_dim(t)` | `tuple_dim((1, 2))` | No change; forms a positive-integer object. |
| Finite-set cardinality | `finite_set_size(S)` | `finite_set_size({1, 2})` | No change; forms a natural-number object. |
| Image or range of a function | `fn_range(f)` | `fn_range(f)` | No change; forms a set object. |
| Image of a function restricted to an explicit domain | `fn_range(fn(x A) T {f(x)})` | `fn_range(fn(x A) T {f(x)})` | No change; forms the image over `A`. |
| Sum of a function over a finite set | `finite_set_sum(S, f)` | `finite_set_sum({1, 2}, f)` | No change; forms a numeric object when the set and function are usable. |
| Finite indexed sum | `sum(first, last, f)` | `sum(1, n, f)` | No change; forms a numeric object. |
| Finite indexed product | `product(first, last, f)` | `product(1, n, f)` | No change; forms a numeric object. |
| Product of a function over a finite set | `finite_set_product(S, f)` | `finite_set_product({1, 2}, f)` | No change; forms a numeric object when the set and function are usable. |
| A half-open integer range | `range(a, b)` | `range(0, 3)` | No change; forms the integers from `a` up to but not including `b`. |
| A closed integer range | `closed_range(a, b)` or `a...b` | `closed_range(0, 3)`, `0...3` | No change; forms the integers from `a` through `b`. |

### Sequence, Matrix, Interval, Struct, And Template Objects (22)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| Length-`n` sequences with values in a set | `finite_seq(S, n)` | `finite_seq(R, 3)` | No change; forms a finite-sequence set. |
| Infinite positive-integer-indexed sequences | `seq(S)` | `seq(R)` | No change; forms a sequence set. |
| A displayed finite sequence | `[a, b, ...]` | `[1, 2, 3]` | No change; forms a finite-sequence value. |
| Sequence, tuple, or indexed-object access | `a[i]` | `a[1]` | No change; forms the selected coordinate when the index is valid. |
| Matrices with fixed entry set and dimensions | `matrix(S, rows, columns)` | `matrix(R, 2, 2)` | No change; forms a matrix set. |
| A displayed matrix | `[[...], [...]]` | `[[1, 0], [0, 1]]` | No change; forms a matrix value after shape and entries are checked. |
| Matrix addition | `A '+ B` | `A '+ B` | No change; forms a matrix object with compatible dimensions. |
| Matrix subtraction | `A '- B` | `A '- B` | No change; forms a matrix object with compatible dimensions. |
| Matrix multiplication | `A '* B` | `A '* B` | No change; forms a matrix object with compatible inner dimensions. |
| Scalar multiplication of a matrix | `c *' A` | `2 *' A` | No change; forms a matrix object. |
| Matrix power | `A '^ n` | `A '^ 2` | No change; forms a matrix object when `A` is square. |
| An open real interval | `'(a, b)` | `'(0, 1)` | No change; forms a set object. |
| A left-open, right-closed real interval | `'(a, b]` | `'(0, 1]` | No change; forms a set object. |
| A left-closed, right-open real interval | `'[a, b)` | `'[0, 1)` | No change; forms a set object. |
| A closed real interval | `'[a, b]` | `'[0, 1]` | No change; forms a set object. |
| An open lower-bounded ray | `'(a,)` | `'(0,)` | No change; forms a set object. |
| A closed lower-bounded ray | `'[a,)` | `'[0,)` | No change; forms a set object. |
| An open upper-bounded ray | `'(,b)` | `'(,0)` | No change; forms a set object. |
| A closed upper-bounded ray | `'(,b]` | `'(,0]` | No change; forms a set object. |
| The set-like view defined by a struct | `&Struct` or `&Struct<args>` | `&Point`, `&Group<S>` | No change; resolves a struct view object. |
| Explicit access to a field through a struct view | `&Struct{obj}.field` | `&Point{p}.x` | No change; forms the field object after membership is checked. |
| An instantiated template | `\Template<args>` | `\T<R>` | No change; materializes the template instance for use. |

The preview default-view spellings `p &Point` and `p.x` are documented in
[Struct Objects And Explicit Or Default-View Field Access](Manual.md#struct-objects-and-explicit-or-default-view-field-access-preview).
They are not part of the 72-entry core count.

## Fact Glossary

A fact is a proposition. A fact shape does not change the context merely by
being nested inside another form. When a top-level factual statement verifies,
Litex stores the accepted fact and then runs inference.

### Common Fact Forms (10)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| One indivisible predicate or relation | atomic fact | `x = y`, `x $in A`, `$p(x)` | When verified as a statement, stores the atomic fact and runs inference. |
| Conjunction | `atomic and atomic ...` | `x = 1 and y = 2` | When verified, stores the component atomic facts and their consequences. |
| A chain of adjacent binary relations | `a rel b rel c` | `0 <= x <= 1`, `A $subset B $subset C` | When verified, stores the adjacent relations exposed by the chain. |
| Disjunction | `branch or branch ...` | `x = 0 or x != 0` | When verified, stores the disjunctive fact; it does not choose a branch. |
| Existence | `exist params st {facts}` | `exist x R st {x = 1}` | When verified, stores the existential fact, not a named witness. |
| Unique existence | `exist! params st {facts}` | `exist! x R st {x = 0}` | When verified, stores existence together with the uniqueness claim. |
| Non-existence | `not exist params st {facts}` | `not exist x R st {x != x}` | When verified, stores the negated existential fact. |
| Universal implication | `forall params: assumptions =>: conclusions` | `forall x R: x = x` | When verified, stores a reusable known `forall` fact. |
| Universal equivalence | `forall params: =>: left <=>: right` | `forall x, y R:`<br>`=>:`<br>`x > y`<br>`<=>:`<br>`y < x` | When verified, stores both reusable directions of the equivalence. |
| Negated universal statement | `not forall params: facts` | `not forall x R:`<br>`x > 0` | When verified, stores the negated universal fact. |

### Atomic Facts (34)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| A user-defined or abstract predicate holds | `$predicate(args)` | `$prime(n)` | When verified, stores the positive predicate fact and runs inference. |
| Equality | `a = b` | `x = y` | When verified, stores the equality and makes it available to equality-aware matching. |
| Strict less-than | `a < b` | `x < y` | When verified, stores the order fact and inferred consequences. |
| Strict greater-than | `a > b` | `x > y` | When verified, stores the order fact and inferred consequences. |
| Less-than or equal | `a <= b` | `x <= y` | When verified, stores the order fact and inferred consequences. |
| Greater-than or equal | `a >= b` | `x >= y` | When verified, stores the order fact and inferred consequences. |
| An object is a set | `$is_set(A)` | `$is_set(A)` | When verified, stores the set predicate and inferred set properties. |
| A set is nonempty | `$is_nonempty_set(A)` | `$is_nonempty_set(A)` | When verified, stores nonemptiness and inferred set properties. |
| A set is finite | `$is_finite_set(A)` | `$is_finite_set(A)` | When verified, stores finiteness and inferred set properties. |
| Membership | `x $in A` | `x $in A` | When verified, stores membership and routine type or set consequences. |
| An object has Cartesian-product shape | `$is_cart(C)` | `$is_cart(C)` | When verified, stores the Cartesian-product predicate. |
| An object has tuple shape | `$is_tuple(t)` | `$is_tuple(t)` | When verified, stores the tuple predicate. |
| Subset inclusion | `A $subset B` | `A $subset B` | When verified, stores the inclusion and inferred set consequences. |
| Superset inclusion | `A $superset B` | `A $superset B` | When verified, stores the inclusion and inferred set consequences. |
| Proper subset inclusion | `A $proper_subset B` | `A $proper_subset B` | When verified, stores strict inclusion and its ordinary subset consequences. |
| Proper superset inclusion | `A $proper_superset B` | `A $proper_superset B` | When verified, stores strict inclusion and its ordinary superset consequences. |
| Two functions agree on a set | `$fn_eq_in(f, g, A)` | `$fn_eq_in(f, g, A)` | When verified, stores pointwise equality on `A`. |
| Two functions are globally equal | `$fn_eq(f, g)` | `$fn_eq(f, g)` | When verified, stores global function equality. |
| A user-defined predicate does not hold | `not $predicate(args)` | `not $prime(n)` | When verified, stores the negative predicate fact. |
| Disequality | `a != b` | `x != y` | When verified, stores disequality and its routine consequences. |
| Negated strict less-than | `not a < b` | `not x < y` | When verified, stores the negative order fact. |
| Negated strict greater-than | `not a > b` | `not x > y` | When verified, stores the negative order fact. |
| Negated less-than or equal | `not a <= b` | `not x <= y` | When verified, stores the negative order fact. |
| Negated greater-than or equal | `not a >= b` | `not x >= y` | When verified, stores the negative order fact. |
| An object is not a set | `not $is_set(A)` | `not $is_set(A)` | When verified, stores the negative set predicate. |
| A set is not nonempty | `not $is_nonempty_set(A)` | `not $is_nonempty_set(A)` | When verified, stores the negative nonemptiness fact. |
| A set is not finite | `not $is_finite_set(A)` | `not $is_finite_set(A)` | When verified, stores the negative finiteness fact. |
| Non-membership | `not x $in A` | `not x $in A` | When verified, stores non-membership. |
| An object is not a Cartesian product | `not $is_cart(C)` | `not $is_cart(C)` | When verified, stores the negative Cartesian-product predicate. |
| An object is not a tuple | `not $is_tuple(t)` | `not $is_tuple(t)` | When verified, stores the negative tuple predicate. |
| Failure of subset inclusion | `not A $subset B` | `not A $subset B` | When verified, stores the negated inclusion. |
| Failure of superset inclusion | `not A $superset B` | `not A $superset B` | When verified, stores the negated inclusion. |
| Failure of proper-subset inclusion | `not A $proper_subset B` | `not A $proper_subset B` | When verified, stores the negated strict inclusion. |
| Failure of proper-superset inclusion | `not A $proper_superset B` | `not A $proper_superset B` | When verified, stores the negated strict inclusion. |

### Facts Inside Larger Facts (8)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| A simple branch made from atomic facts, conjunctions, or chains | atomic, `and`, or chain | `x = 1`, `x = 1 and y = 2`, `0 <= x <= 1` | Local to the containing fact until that whole fact is verified. |
| A disjunctive branch | atomic, `and`, chain, or `or` | `x = 0 or x != 0` | Local to the containing fact; does not select a branch. |
| A conclusion that may itself assert existence | atomic, `and`, chain, `or`, or `exist` | `exist y R st {y = x}` inside a `forall` conclusion | Becomes part of the enclosing universal conclusion. |
| One atomic existential condition | `st {atomic}` | `exist x R st {x = 1}` | Scoped to the existential body; no named witness is added. |
| Conjoined existential conditions | `st {atomic and atomic}` | `exist x, y R st {x = 1 and y = 2}` | Scoped to the existential body. |
| A chained existential condition | `st {chain}` | `exist x R st {0 <= x <= 1}` | Scoped to the existential body. |
| Disjunctive existential conditions | `st {branch or branch}` | `exist x R st {x = 0 or x = 1}` | Scoped to the existential body. |
| A compact universal condition inside an existential | `forall! params => {facts}` inside `st {...}` | `exist f fn(x R) R st {forall! x R => {f(x) = x}}` | Scoped to the containing existential fact. |

## Statement Glossary

Statements are the actions that build a Litex file. Unlike an object or a fact
shape, a successful statement may commit names, definitions, verified facts,
proof interfaces, implementations, module declarations, or strategy state.

### Definition And Context Statements (22)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| Verify and record a mathematical fact | a bare fact | `1 + 1 = 2` | After successful verification, stores the fact and runs inference. |
| Define a predicate by equivalent conditions | `prop name(params): clauses` | `prop is_one(x R):`<br>`x = 1` | Stores a concrete predicate definition. The clauses are a definition, not a theorem proved at declaration time. |
| Give an existing concrete predicate another name | `alias prop new <=> existing` | `alias prop one_prop <=> is_one` | Stores a copied concrete predicate definition under the new name. |
| Declare a predicate symbol without a definition | `abstract_prop name(params)` | `abstract_prop prime(n)` | Stores the predicate interface only; it adds no mathematical facts. |
| Introduce a new object in a set | `have name Set` | `have x R` | Binds the name, stores its membership fact, and runs inference after proving the set is nonempty. |
| Introduce a new object equal to an expression | `have name Set = value` | `have x R = 1` | Binds the name and stores its type, membership, and defining equality. |
| Define a symbolic tuple by coordinates | `have tuple name for i <= n, ...` | `have tuple f for i <= n, f[i] = i` | Stores the tuple marker, dimension, and coordinate `forall` fact. |
| Define a symbolic Cartesian product by factors | `have cart name for i <= n, ...` | `have cart C for i <= n, proj(C, i) = R` | Stores set/cartesian markers, dimension, and projection `forall` fact. |
| Define an infinite sequence by entries | `have seq name seq(S) for i, ...` | `have seq s seq(N_pos) for i, s(i) = i` | Stores sequence membership and its function-body equality data. |
| Define a finite sequence by entries | `have finite_seq name finite_seq(S, n) for i <= n, ...` | `have finite_seq f finite_seq(N_pos, n) for i <= n, f(i) = i` | Stores finite-sequence membership, length constraints, and entry data. |
| Define a matrix by entries | `have matrix name matrix(S, r, c) for i <= r, j <= c, ...` | `have matrix M matrix(N_pos, r, c) for i <= r, j <= c, M(i, j) = j` | Stores matrix membership, dimensions, and entry data. |
| Introduce an object together with facts about it | `have name Set: facts` | `have x R:`<br>`x = 1` | Binds the name and stores the attached verified facts and inferred consequences. |
| Open a known existential and name its witnesses | `obtain names from exist ...` | `obtain a from exist x R st {x = 1}` | Binds witness names and stores their types and instantiated body facts. |
| Name a preimage of a known range member | `have by preimage name from membership` | `have by preimage x from y $in fn_range(f)` | Binds preimage names and stores domain and value-equality facts. |
| Define a function by one expression | `have fn f(params) ReturnSet = body` | `have fn f(x R) R = x + 1` | Stores the function, function type, defining equality, and callable body data. |
| Define a function by cases | `have fn f(params) ReturnSet by cases:` | `have fn sgn(x R) R by cases:`<br>`case x >= 0: 1`<br>`case x < 0: -1` | After coverage and return checks, stores the function and generated case `forall` facts. |
| Define a recursive function by induction | `have fn f(params) ReturnSet by induc measure from base:` | `have fn h(n N) N by induc n from 0:`<br>`case n = 0: 1`<br>`case n > 0: h(n - 1)` | After termination and return checks, stores the recursive function definition. |
| Define a function from unique existence | `have fn name by exist!:` | `have fn choose by exist!:`<br>`? forall x R:`<br>`exist! y R st {y = x}` | Stores the selected function, its type, defining property, and uniqueness fact. |
| Define a parameterized family | `template<params>:` | `template<S set>:`<br>`have A set = S` | Stores a reusable template body; its internal effects occur when an instance is materialized. |
| Introduce local names and facts without proving them | `trust have ...` | `trust have x R:`<br>`x = 1` | Stores unsafe names and assumptions, then runs inference; strict mode rejects it. |
| Attach a checked executable implementation to a function | `have algo for f(params):` | `have algo for max2(a, b):`<br>`case a >= b: a`<br>`b` | Stores executable cases for later `eval`; it does not replace the mathematical `have fn` definition. |
| Define a struct view, fields, and equivalent conditions | `struct Name:` | `struct Point:`<br>`x R`<br>`y R` | Stores the struct definition, field interfaces, and equivalent facts. |

### Proof, Theorem, Strategy, And Utility Statements (25)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| Prove a local goal and export its result | `claim:` | `claim:`<br>`? 1 = 1`<br>`1 = 1` | Runs the local proof, stores the proved target in the outer context, and runs inference. |
| Add an explicit unproved assumption | `trust fact` | `trust x = 1` | Stores the fact as unsafe proof debt and runs inference; strict mode rejects it. |
| Check a local exploratory block without exporting its facts | `sketch:` | `sketch:`<br>`1 = 1` | Checks nested statements in a child context; commits nothing to the outer context. |
| Define a named theorem for explicit calls | `thm name:` | `thm self_eq:`<br>`? forall x R:`<br>`x = x` | Stores the verified named theorem interface for `by thm`. |
| Define a named theorem that also participates in automatic matching | `lemma name:` | `lemma self_eq_auto:`<br>`? forall x R:`<br>`x = x` | Stores the named theorem and its reusable known `forall` fact. |
| Apply a named theorem | `by thm name(args)` | `by thm self_eq(1)` | After checking parameters and premises, stores the instantiated conclusions. |
| Verify a concrete predicate directly from its definition | `by def $P(args)` | `by def $is_unit_pair(1, 1)` | Verifies every instantiated definition clause, then stores the predicate fact. |
| Define and activate a reusable non-equational proof strategy | `strategy name:` | `strategy positive_nonzero:`<br>`? forall x R:`<br>`x > 0`<br>`=>:`<br>`x != 0` | Stores the verified strategy interface and activates it for matching goals. |
| Enable a previously defined strategy | `use strategy name` | `use strategy positive_nonzero` | Marks the strategy active for subsequent matching goals. |
| Disable a strategy | `stop strategy name` | `stop strategy positive_nonzero` | Removes that strategy from the active route for its target fact shape. |
| Declare a top-level project module | `module` in `[hierarchy]` | `module` under `[hierarchy]` | Configures the folder as a module with import capability. |
| Declare an exported child folder | `submodule` in `[hierarchy]` | `submodule` under `[hierarchy]` | Configures the folder as an exported child of its parent project. |
| Declare a non-standard package import | `Name = "path"` in `[import]` | `Algebra = "./Algebra"` | Registers an external module and its canonical namespace. |
| Declare an installed standard package | package name in `[import std]` | `basics` | Registers the installed standard module for import and lookup. |
| Export a project source file | `name = "path.lit"` in `[export]` | `local = "./local.lit"` | Registers the file, its canonical source name, and recursive run order. |
| Cite an earlier exported source | `source::name` | `chapter3::local` | No new binding by itself; resolves a name from an earlier registered source. |
| Order project dependencies | earlier entries in recursive `[export]` order | place dependencies before their users | Determines which exported contexts are available to later project sources. |
| Verify every exported project source | CLI `-r` | `litex -r <project>` | Runs the configured export graph; it does not persist a new source-level fact after the process exits. |
| Audit imported sources as well as exports | CLI `-strict -r` | `litex -strict -r <project>` | Runs the project with strict trust checks across imported and exported sources. |
| Perform no operation | `do_nothing` | `do_nothing` | No context effect. |
| Clear the current user environment | `clear` | `clear` | Removes current user bindings and facts while keeping registered imports available. |
| Evaluate an object expression | `eval expression` | `eval 1 + 2` | Computes the value, reports it, and stores the evaluation equality. |
| Evaluate a named executable definition | `eval name` | `have a R = 1 + 2`<br>`eval a` | Uses known executable data and stores the resulting equality. |
| Prove existence by supplying witnesses | `witness exist ... from values` | `witness exist x R st {x = 1} from 1` | Verifies the instantiated body, stores the existential fact, and runs inference. |
| Prove nonemptiness by supplying an element | `witness $is_nonempty_set(S) from value` | `witness $is_nonempty_set({1, 2}) from 1` | Verifies membership, stores nonemptiness, and runs inference. |

### `by ...` Proof-Control Statements (16)

| Ordinary mathematical idea | Litex form | Example | Effect on context |
|---|---|---|---|
| Prove a goal by exhaustive cases | `by cases disjunction:` | `by cases x = 0 or x != 0:`<br>`case x = 0:`<br>`do_nothing`<br>`case x != 0:`<br>`do_nothing` | Checks coverage and every branch, then stores the common conclusions. |
| Prove a goal by contradiction | `by contra negated_target:` | `by contra not $p(1):`<br>`$p(1)`<br>`impossible $q(1)` | Checks both sides of a contradiction, then stores the original target. |
| Unfold and verify a concrete predicate definition | `by def $P(args)` | `by def $P(a, b)` | Verifies all instantiated definition clauses, then stores `$P(a, b)`. |
| Prove a universal fact by enumerating a displayed finite set | `by enumerate finite_set forall! ...:` | `by enumerate finite_set forall! x {1, 2} => {x $in {1, 2}}:` | Checks every finite assignment, then stores the resulting universal fact. |
| Expand membership in an integer range | `by enumerate range: membership` | `by enumerate range: i $in range(0, 3)` | Stores the generated equality or disjunction describing the member. |
| Expose closed-range membership as cases | `by closed_range as cases: membership` | `by closed_range as cases: i $in closed_range(0, 3)` | Stores the generated equality or disjunction of endpoint/interior cases. |
| Prove by ordinary or strong induction | `by induc ...` or `by strong_induc ...` | `by induc n from 0:`<br>`? $P(n)` | Checks base and step obligations, then stores the resulting universal fact. |
| Prove a bounded universal fact by iteration | `by for forall! ...:` | `by for forall! i range(0, 3) => {i < 3}:` | Checks each finite assignment, then stores the universal fact. |
| Prove equality of sets by extensionality | `by extension A = B:` | `by extension A = B:` | Checks both subset directions, then stores the set equality. |
| Register a predicate as reflexive | `by reflexive_prop:` | `by reflexive_prop:`<br>`? forall x set:`<br>`$rel(x, x)` | Proves the required universal fact and registers reflexive matching behavior. |
| Register a predicate as symmetric | `by symmetric_prop:` | `by symmetric_prop:`<br>`? forall x, y set:`<br>`$rel(x, y)`<br>`=>:`<br>`$rel(y, x)` | Proves the permutation fact and registers symmetric matching behavior. |
| Register a predicate as transitive | `by transitive_prop:` | `by transitive_prop:`<br>`? forall x, y, z set:`<br>`$rel(x, y)`<br>`$rel(y, z)`<br>`=>:`<br>`$rel(x, z)` | Proves the required universal fact and registers transitive matching behavior. |
| Register a predicate as antisymmetric | `by antisymmetric_prop:` | `by antisymmetric_prop:`<br>`? forall x, y set:`<br>`$le(x, y)`<br>`$le(y, x)`<br>`=>:`<br>`x = y` | Proves the required universal fact and registers antisymmetric behavior. |
| Use the trusted preview Zorn route | `by zorn_lemma: set S, prop le` | `by zorn_lemma: set P, prop le` | After checking its obligations, stores the maximal-element existence conclusion; this route is trusted preview support. |
| Use the trusted preview choice route | `by axiom_of_choice: set F` | `by axiom_of_choice: set F` | After checking family and nonemptiness obligations, stores a choice-function existence conclusion. |
| Use the trusted preview regularity route | `by regularity_axiom(A)` | `by regularity_axiom(A)` | After checking nonemptiness, stores the regularity/foundation conclusion. |

## How Definitions Are Written

Choose a definition form by the mathematical thing being introduced.

| What is being defined | Use | Required shape | What Litex records |
|---|---|---|---|
| A named object or constant | `have` | Name, containing set or type, and optionally a defining value | The name, membership/type facts, and an equality when a value is supplied |
| A function given by one equation | `have fn ... = ...` | Name, parameters with domains, return set, and body | Function type and defining body |
| A piecewise function | `have fn ... by cases` | Function signature plus exhaustive, mutually exclusive cases | Function type and case-specific universal facts |
| A recursive function | `have fn ... by induc` | Function signature, induction measure, base, and decreasing recursive cases | Recursive function definition after termination checks |
| A canonical choice from unique existence | `have fn ... by exist!` | A verified existence-and-uniqueness interface | Selected function, its property, and uniqueness fact |
| A concrete property or relation | `prop` | Name, parameters, and defining equivalent facts | A definition that can be unfolded automatically or with `by def` |
| An intentionally uninterpreted property or relation | `abstract_prop` | Name and parameters only | A predicate symbol with no mathematical behavior |
| A parameterized family of definitions | `template` | Template parameters with domains and a checked body | A reusable body materialized by `\Template<args>` |
| A structure with fields and characterizing facts | `struct` | Name, optional parameters, fields, and equivalent facts | A struct view and field interfaces |
| A coordinate-defined tuple or Cartesian product | `have tuple`, `have cart` | Dimension and coordinate/projection equations | Shape, dimension, and coordinate facts |
| An entry-defined sequence or matrix | `have seq`, `have finite_seq`, `have matrix` | Value set, dimensions or bounds, and entry equations | Membership, dimensions, and entry function data |
| An executable implementation | `have algo for` | An existing `have fn` plus checked expressions or cases | Evaluation data for `eval`; not a second mathematical definition |

Three proof-status forms belong beside definitions in the language, but they
are not ordinary definitions:

| Form | Meaning |
|---|---|
| `thm` | A named result whose proof has been checked; later code cites it explicitly with `by thm`. |
| `axiom` | An explicitly assumed theorem-like interface. It belongs to the trusted boundary and is rejected in strict mode. |
| `trust` | Explicit local proof debt or an unsafe assumption. It is stored visibly and rejected in strict mode. |

The key distinction is mathematical definition versus executable
implementation:

```text
have fn    defines what the function is mathematically
have algo  gives an already-defined function a checked way to compute
```

## How Verification Works

### The Core Atomic-Fact Loop

Most proof obligations eventually become an atomic fact such as `x = y`,
`x $in A`, `x < y`, or `$P(x)`. Litex checks an atomic target in this
order:

1. **Well-definedness.** Check that every object in the target makes sense.
   Function arguments must satisfy their domains; division, indexing, matrix
   operations, intervals, struct fields, and other partial forms must satisfy
   their own conditions.
2. **Builtin mathematical patterns.** Match the target shape against the
   verifier's builtin routes for arithmetic, equality, order, membership,
   sets, functions, tuples, matrices, and related objects.
3. **Known atomic facts.** Search the current context for the same predicate
   and truth value. Arguments may match through equalities already known in the
   context; the source fact need not be textually identical.
4. **Known `forall` facts.** Match the target against a known universal
   conclusion, solve for a parameter substitution, instantiate its premises,
   and verify those premises through the same proof machinery.

Pattern matching is used in builtin routes, known-fact reuse, and known
`forall` instantiation. It is a common mechanism across the loop, not a
separate all-purpose tactic.

The public summary says **~500 builtin routes**. This is deliberately
approximate: the current verifier has roughly 477 related builtin-success
sites, and that implementation count changes as routes are split or combined.

### Context Growth

```text
target fact
   -> verify
   -> store the accepted fact
   -> infer routine consequences
   -> larger proof context
   -> verify the next statement
```

Storage and inference happen after verification. An inferred consequence can
help with the next statement, but it is not the proof route that justified the
original target.

### Additional Routes

These routes sit around the atomic loop. They either expose more obligations
or provide another checked interface; their subgoals return to the same
verification machinery.

| Route | Role |
|---|---|
| Concrete `prop` definition | Fold or unfold the predicate's instantiated defining facts. |
| `by def` | Force every instantiated clause of a concrete predicate definition to be checked. |
| Enabled `strategy` | Apply a registered checked non-equational proof interface to a matching target. |
| Registered predicate properties | Reuse proved reflexive, symmetric, transitive, or antisymmetric behavior. |
| `by thm` | Instantiate a named theorem, verify its parameter/domain obligations, and store its conclusions. |
| `by cases` | Split the goal into exhaustive branches and require the conclusion in every branch. |
| `by contra` | Add the negated target locally and require an explicit contradiction. |
| `by induc` / `by strong_induc` | Generate base and induction-step obligations. |
| `witness` | Instantiate an existential or nonempty target with explicit objects and verify the body. |

Builtin routes and builtin inference are part of Litex's trusted verifier
surface and still require review. `axiom`, `trust`, and the trusted preview
routes remain explicit in source or output rather than being presented as
ordinary checked definitions.

### Result Status

| Result | Meaning | Next action |
|---|---|---|
| `true` | The target was well-defined and a verification route closed it. | Continue; the accepted fact and inferred consequences are now available. |
| `unknown` | The target was well-defined, but the current context and enabled routes did not establish it. This does not mean false. | Add the smallest missing equality, premise, witness, case, or reusable lemma. |
| `error` | Parsing, statement shape, name resolution, or object well-definedness failed. | Repair the malformed or ill-defined expression before treating it as a proof goal. |

For executor-level structural checks and environment effects, continue with
[Statement Execution Cheat Sheet](cheatsheet.md). For detailed semantics and
larger examples, use the [Manual](Manual.md).
