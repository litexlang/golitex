# Litex FAQ

Created and maintained by Jiachen Shen.

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/FAQ.md

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

This page collects common questions about Litex's design, performance model,
and intended proof style. It is written as a living note: answers should stay
concrete, modest, and close to the current verifier behavior.

## Does everything in the public repository count as finished?

No. Litex is developed in public, so drafts, experiments, and incomplete
translations remain visible and available for reuse. Treat a feature or proof
as complete only when its current tests, dated status, explicit `trust`
boundary, and known limitations support that claim.

Litex source stays the same across natural languages. Batch Normal JSON carries
a language selection from `-lang` (default `en`); Chinese output localizes
field names and proof explanations, including `"语言": "zh"`. See [`docs/cli.md`](cli.md).

## Why recommend one spelling when another is supported?

Support describes the language contract; a recommendation helps readers write
consistent source. For new code, prefer `release thm name(args)` over the
supported bare `by thm` alias, an indented `forall` over an inline universal,
and English/ASCII source such as `forall`, `R`, and `$in` over documented
Unicode aliases. The alternatives remain accepted. Indentation exposes the
premise/conclusion boundary; canonical spellings match diagnostic output and
are easy to type and search.

`by thm name(args) => fact` has a distinct purpose: selecting one atomic
consequence. Keep it when that is the intended context effect. The
[learner guide](Litex_Learner_Cheatsheet.md#supported-syntax-and-recommended-writing)
shows both supported and recommended forms, and its
[common sticking points](Litex_Learner_Cheatsheet.md#common-places-to-get-stuck)
explain fact lists versus proof commands, definitions versus instances,
domains, scopes, and witnesses with small examples.

## How does equality reuse known equal objects?

Stored forall equalities are retrieved by nested object constructors,
function positions and parameter holes on both endpoints. When a fixed
argument such as `f(0)` has an existing equality with `g(0)`, matching can use
that complete-value path without requiring `f=g`. Fixed subtrees first use
Direct identity/equality/calculation, then supported constructor descent with
Direct-only leaves. Parameter carriers and theorem premises still need proof;
lookup keys are not proof evidence. See the
[checked tracer](../examples/proof_nodes/equal/by_known_forall/rigid_application_alias.lit).

After well-definedness, equality first checks exact IR or structural alpha
identity and already stored equality paths, then finite known tuple-property
reads, then permitted mathematical builtin rules. Stored paths retain their
generating FactIds and win before a rule can introduce new proof obligations,
including inside strategy search. The later class-search fallback can compare members of
the two endpoint classes using identity, permitted builtin rules, or constructor
matching, and records the left path, new proof, and right path. This also lets
known membership cross alpha-equivalent named function sets. The peer proof
cannot recursively expand more classes or enable a disabled builtin entry. Larger
classes still mean more candidate comparisons. The
[equality README](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md)
shows the complete call and result structure.

For example, `have p cart(R,R)` now lets `p = (p[1],p[2])` cite the
Cartesian membership. With `have p cart(R,R) = (a,b)`, `p[1] = a` cites
the stored equality. A tuple-valued function can likewise be projected after
application WD and one checked body substitution. Known shape supplies tuple
and index requirements without a user-written membership bridge. This route
retains source FactIds; it does not recursively unfold nested function bodies
or accept an out-of-range index. See the
[function tracer](../examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit). A template function
alias retains its checked signature through stored equality paths. A named
application result can supply its tuple value or a coordinate without first
asserting the complete tuple equality; see the
[template alias tracer](../examples/stmt_nodes/definition/template_alias_struct_tuple.lit).

An explicit chain such as `y = x + 1 = 3` checks its adjacent steps and also
stores the endpoint `y = 3`. Subsequent facts can reuse that stored equality.
For `have x R = 2` and `have y R = x + 1`, use this chain to expose the
definition and calculation; definition expansion keeps residual rewrite
disabled. See the [runnable example](../examples/proof_nodes/chain/named_definition_endpoint.lit).

## Can definition-time properties be used with builtin entry disabled?

Yes. After an atomic goal passes well-definedness, the shared `by_known`
entry first reads stored atomic facts using only identity/stored-path argument
matches. Only a miss opens the existing parameter-transforming search, then
`known_special_property`.
For a well-defined application, the latter can match its function's recorded
signature to establish codomain or `fn_range` membership. It only reads
the general Membership/Equality fact index, substitutes arguments, and cites
identity or stored equalities. It generates no proof subgoals and consumes
neither builtin entry nor strategy depth. Invalid applications still fail WD.

Fixed builtin premises also use the read-only form of this entry. Their
results retain the stored-fact or definition-property evidence. Candidate
enumeration and explicit FactId/history retrieval keep their own interfaces.
See the [verification pipeline](../src/execute/execute_fact_stmt/README.md).

## Why is Litex called Litex?

Litex = Lisp + LaTeX. 

Litex is inspired by Lisp not only in the idea “data
as code,” but also in its taste for a small uniform
core, symbolic manipulation, tree-shaped programs,
interactive feedback, and language-building through
small composable forms.

Litex is inspired by LaTeX's practical design for writing mathematics.

## Does Litex support multiple output languages?

The Litex source language is shared. Batch Normal JSON includes
English keys by default. With `-lang zh`, envelope and statement keys become
Chinese, and rule names and explanations are translated. Source syntax stays
the same; see [`docs/cli.md`](cli.md).

## How is Litex invented?

By iteratively implementing and refining the Litex language. The design process and implementation process happen side by side. The author took 6000 git commits (mostly before AI becomes sort of usable to help him to do kernel development) to finally know what he is implementing and designing. It's hard to imagine a better way to do something like this. When everything comes together, it's a beautiful thing.

## Is Litex a programming language?

No. Litex is a domain language for and just for mathematics reasoning. It is not a programming language. By sacrificing the programming language features, Litex can focus on the mathematics reasoning features. This is very different from Lean, Coq, and Isabelle. That's why it can be designed as close to ordinary mathematics as possible.

## Where does features of Litex come from?

The features of Litex come from the author's experience in writing mathematics. The author has been writing mathematics for a long time, and he has some understanding of the mathematics reasoning process. The author has also been writing code for a long time, and he has some understanding of the code reasoning process. He thinks formal language should be used by everyone, just like math is used by everyone.

Most of the features of Litex come from the author's experience in writing mathematics and code. The core verification process `match and substitute` is inspired by how people verify a fact: When he sees a fact not yet proven, he will try to match the fact with a known fact, and if the match is successful, he will substitute the arguments of the known fact into the fact to be proven. If it's ok to substitute, then the fact is proven.

`template` of Litex is inspired by the `template` of C++ (some math object can be defined on different sets)and `interface` of Go (The parameters of template must satisfy certain properties)

`struct` of Litex is inspired by the `struct` of C.

`claim`, `thm` of Litex is inspired by what `theorem` means in math books.

`strategy` and builtin rules of Litex is inspired by how people verify the well-definedness of a recursively defined object.

Syntax sugar of `xxx set` in `forall xxx set` meaning `$is_set(xxx)` is inspired by the discovery that when we talk about sets, we almost always are saying that `something is a set`. So the word `set` never appear independently in the language. It always shows up together with `<some_object> is a set`.

Anonymous function syntax like`fn(x R) R {(-x)}` is essential because they are used as parameters of functions like `sum` and `product` and `\integral`. It's inspired by JavaScript's `(x) => (-x)` syntax.

The correlation between `tuple`, `cart`, and `struct` is essential, because anything, including `struct`, must correlate to something in set theory. Nothing in Litex should be arbitrary and without concrete mathematical meaning. Once its parameters are fixed, `&Point` is one named subset of a Cartesian carrier. A definition such as `have p &Point = (0, 0)` therefore gives `p` the corresponding field names, including `p.x` for its first coordinate.

## What does "Litex is built on relationships between objects instead of meanings of them" mean?



The rational numbers `Q` can be constructed as equivalence classes of pairs
of integers, and the real numbers `R` can be constructed in several different
ways. Litex does not make one such construction the builtin definition of
either carrier. Similarly, a function `f fn(x R, y R) R` can be modeled by a
graph inside `cart(R, R, R)` or by a graph inside `cart(cart(R, R), R)`.
Litex exposes the function interface directly instead of forcing either graph
encoding on every user. A development may formalize a particular construction
when it matters, or mark an assumed compatibility result with `trust`. The
builtin interface focuses on usable relationships, such as `Z` being contained
in `Q`, and on the domain and codomain behavior of function application.

When we were learning Euclidean geometry in middle school, our teachers would say that these so-called points, lines, planes, and circles are not actually the real ones we draw on paper. They are imagined constructs that possess specific properties. What they fundamentally are is not important; what matters is that there are certain axioms governing these objects, which form the relationships among them. Although they can be defined by using more abstract math concepts (using cartesian coordinate for example), we don't consider that since we only want to focus on properties like parallel and intersection, which those axioms already can process. Similarly, real numbers, rational numbers, and the like can also be defined using more abstract mathematical concepts—users can construct these definitions themselves using Litex code. In fact, however, what is even more important is the relationships between them, and this is precisely what Litex emphasizes.

Read the content from Terrence Tao's Analysis One:

```

Remark 2.1.14. Note that our definition of the natural numbers is ax- iomatic rather than constructive. We have not told you what the natural numbers are (so we do not address such questions as what the numbers are made of, are they physical objects, what do they measure, etc.) - we have only listed some things you can do with them (in fact, the only operation we have defined on them right now is the increment one) and some of the properties that they have. This is how mathematics works - it treats its objects abstractly, caring only about what properties the objects have, not what the objects are or what they mean. If one wants to do mathematics, it does not matter whether a natural number means a certain arrangement of beads on an abacus, or a certain organization of bits in a computer’s memory, or some more abstract concept with no physical substance; as long as you can increment them, see if two of them are equal, and later on do other arithmetic operations such as add and multiply, they qualify as numbers for mathematical purposes (provided they obey the requisite axioms, of course). It is possible to construct the natural numbers from other mathematical objects - from sets, for instance - but there are multiple ways to construct a working model of the natural numbers, and it is pointless, at least from a mathematician’s standpoint, as to argue about which model is the “true” one - as long as it obeys all the axioms and does all the right things, that’s good enough to do maths.

```

As far as Litex is concerned, Litex contains and only contains standard math properties.

## Why does Litex have this particular menu of objects and statements?

Litex's grammar is intentionally finite and opinionated. The goal is not to
have every possible proof-engine concept become a new surface form. The goal is
to keep a small set of object and statement forms that make ordinary
mathematical writing comfortable while remaining checkable.

There are two main reasons a form becomes first-class.

First, some forms are basic mathematical or logical infrastructure. Equality,
membership, number literals, arithmetic, function application, `forall`,
`exist`, conjunction, cases, witnesses, definitions, and proof blocks are
trusted background, logical organization, or computational material that the
verifier needs to understand directly. If these were only encoded through a
more remote abstraction, nearly every proof would spend its budget on
bookkeeping before reaching the mathematical idea.

Second, some forms are user-interface choices. They are included because
mathematicians already write them, often with a close LaTeX analogue: set
displays, tuples, Cartesian products, intervals, sums, anonymous functions,
chained equalities or inequalities, `have`, `claim`, `witness`, `by cases`,
and similar proof moves. These forms are not all foundationally primitive in
the same sense. They are there because they make Litex code feel familiar and
reduce the distance between a paper proof and a checked script.

So `obj` and `statement` in Litex are a design boundary. Objects are the
mathematical expressions facts can talk about. Statements are the actions that
introduce objects, define vocabulary, assert facts, and organize proofs. A new
object or statement form has to earn its place: either the checker needs it as
direct mathematical background, or it makes the user-facing mathematical
surface substantially clearer.

This is one of Litex's unusual design choices. It optimizes for user comfort
and mathematical familiarity with as few first-class forms as possible, rather
than starting from a maximally general programming language or proof-term
calculus.

## Why can an `or` branch contain an `and` if `and` contains only atomic facts?

Because Litex uses a fixed precedence hierarchy for facts. An `and` is
deliberately flat and contains only atomic facts. The parser finishes one
atomic, relation-chain, or flat-`and` branch before the outer `or` collects
those branches. Internally, this is why an `AndFact` stores atomic facts while
an `OrFact` stores `AndChainAtomicFact` branches. The same fixed branch shapes
also make searching a known `or` against a goal `or` comparatively convenient.

For example, Litex reads

```text
$p(a) and $q(a) or $t(a)
```

as the two `or` branches `($p(a) and $q(a))` and `$t(a)`. Saying that `or` is
the higher grammar/AST layer and saying that `and` has tighter operator-binding
precedence describe the same parse from two viewpoints. This does not make the
fact grammar recursively nestable: `and` still contains only atomic facts, and
`or` only collects completed atomic, chain, or flat-conjunction branches.

The same four shapes form the bounded premise language for automatic builtin
rules. In particular, a rule may consume a known complete `or` fact without
claiming that any branch is separately known. For example, the premise
`a = 1 or a = 2 or a = 3` can prove `a $in {1, 2, 3}`. When the verifier instead
introduces an `or`, it must prove one selected branch. In both directions every
atomic leaf keeps the surrounding builtin permission and deep-search budget; the compound fact does
not reopen full proof search.

Universal conclusions follow the same bounded grammar. A `forall` conclusion
cannot contain another `forall`; bind all quantified parameters in the
outer header instead. For example, write `forall x R, y R: ...` rather than
placing `forall y R` inside the conclusion of `forall x R`. A universal fact
may still appear as an explicit premise before `=>:` because premises are
stored as assumed facts rather than conclusion branches. A direct `not forall`
conclusion is also rejected; name the quantified proposition first.

This means that some ordinary logical shapes have no direct anonymous Litex
syntax. In particular, a `forall` cannot be used directly as one branch of an
`or`, even though Lean can recursively compose that proposition shape. For a
closed subclaim, name the compound fact with a zero-parameter `prop`, then use
the resulting atomic call in the outer fact:

The current parser requires a nonempty `prop` parameter list. The closed,
zero-argument predicate below is retained as an intended interface, not
working syntax. Use a predicate with real mathematical parameters in current code.

> **Migration example:** Current `src/` checking stops at `parse_error: expected at least one parameter inside (...)`. This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
prop all_reals_reflexive():
    forall x R:
        x = x

by def $all_reals_reflexive()
$all_reals_reflexive() or 1 = 1 and 2 = 2
```

The definition defines `$all_reals_reflexive()` to be equivalent to its body;
it does not make the body true automatically. If the subclaim has free objects,
give the `prop` corresponding parameters. This naming step preserves Litex's
canonical fact representation while still exposing the intended mathematical
statement through an atomic interface.

## How does Litex parse a minus sign next to a power?

Power binds tighter than prefix minus, and prefix minus binds tighter than
multiplication, division, and binary addition or subtraction. Consequently,
the parser reads `-t^2` as `-(t^2)`, while `-t * u` groups as `(-t) * u`.
Powers remain right-associative, so `a^b^c` means `a^(b^c)`.

Litex authoring should nevertheless make the minus/power boundary explicit.
Write `-(t^2)` or `-1 * (t^2)` for the opposite of the square, `(-t)^2` for
the square of the negative value, and `t^(-1)` for a negative exponent. This
keeps the syntax tree visible to human readers and authoring agents instead of
making them remember or guess the parser rule.

## What are builtin objects and builtin rules?

Litex is easiest to understand through four related layers:

- an `object` is a mathematical expression, such as `x`, `x + 1`, `R`,
  `{1, 2}`, `abs(x)`, or `fn(n N+) R`;
- a `fact` is a proposition about objects, such as `x > y`, `x $in R`,
  `1 + 2 = 3`, or `x = y or x < y or x > y`;
- a `statement` is a line or block that acts on the mathematical context, such
  as `have`, `forall`, `claim`, `thm`, `witness`, `by cases`, or `trust`;
- a verification rule is a checker route for deciding whether a fact follows
  from the current context.

Objects, factual forms, and verification routes have builtin support. Ordinary
source-level facts are not injected into every run: a package fact is available
only after an explicit import and keeps its package namespace.

A **builtin object** is an object form or name that Litex understands directly.
Not every builtin word is an object: `not`, `and`, `or`, `forall`, and `exist`
are builtin logical or factual forms because they express the shape of facts
and proofs. Builtin object heads are expressions such as standard sets,
arithmetic operations, tuple and set forms, or `abs(x)`. Some of these are
mainly for user convenience. The absolute value object `abs(x)` is a good
example: users could define a similar function themselves from basic order and
arithmetic, but the standard spelling is built in because ordinary mathematics
uses it constantly.

```litex
have fn self_abs(x R) R by cases:
    case x = 0: 0
    case x < 0: (-x)
    case x > 0: x
```

The point is not that `abs` is impossible to express without a builtin name.
The point is that writing `abs(x)` lets the verifier connect the expression to
the usual absolute-value rules without every file rebuilding that interface.

A **source-level background fact** is an ordinary Litex fact, usually kept in
an explicitly imported project or source-local cite package. A **builtin
rule** instead lives in the verifier. For example, the verifier directly
recognizes the usual real-line trichotomy:

```litex
forall x, y R:
    x = y or x < y or x > y
```

Builtin rules can also produce the basic real comparison witnesses used by
ordinary object definitions:

```litex
have x R:
    x > 100
```

This applies only to a single comparison between a new real witness and a
well-defined real expression; it is not unrestricted witness search.

A **builtin statement** is a statement form that the executor understands as a
primitive context action. For example, `have` introduces objects, `forall`
checks universal facts, `claim` and `thm` prove reusable facts, `witness`
proves existential facts, and `by cases` organizes case proofs. These are not
ordinary mathematical objects. They are the proof-script actions that grow or
inspect the current context.

A **builtin verification rule** is different from a stored theorem. It is a
small verifier pattern that can close the current goal, often by looking at
equivalent forms or doing routine computation. For example, when the goal is
`x > y`, Litex can use common equivalent forms such as `y < x` or
`x - y > 0`:

Some of these routes are Rust-level verifier rules, while standard packages
can provide additional imported `forall` facts. The user-facing effect is
similar: the verifier can use common mathematical background without the
current file proving a local lemma first.

> **Migration example:** Current `src/` checking stops at `search_proof` (`forall x, y R:`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
forall x, y R:
    x - y > 0
    =>:
        x > y

forall x, y R:
    y < x
    =>:
        x > y

forall x, y R:
    x != y
    =>:
        y != x
```

The last proof uses the one-premise `not-equality symmetry` builtin. Its output
keeps the known proof of `x != y` as a child; the read-only lookup cannot
invent inequality when no orientation is known.

Builtin verification rules also cover calculation-style facts:

```litex
1 + 2 = 3
```

These rules matter because ordinary mathematical writing silently uses many
tiny equivalences and calculations. Without builtin rules, users would have to
write every bridge by hand: convert `x > y` to `y < x`, convert that to
`x - y > 0`, cite the arithmetic theorem for `1 + 2 = 3`, and so on. Litex
instead lets the user write the meaningful step while the verifier handles a
bounded amount of common background reasoning.

For example, Litex verifies `(a % 8) % 2 = a % 2` for `a Z` because the outer
modulus `2` divides the inner modulus `8`. It does not generalize this to
incompatible moduli such as `3` and `8`.

That bound is structural rather than a node budget. A direct builtin rule is
one layer deep: its premises may cite known non-`forall` atomic facts or use
deterministic computation, but cannot run another builtin rule. Separate
builtin strategies recurse only through a strictly smaller supported syntax
tree—for example nested arithmetic carriers, sums, products, finite-set
constructors, finite-product pointwise congruence, set membership, or tuple coordinates. Each strategy layer may
try one fresh direct rule on its immediate children. Neither route calls known
`forall` matching, concrete definitions, user strategies, or the full verifier.
Detailed output distinguishes `builtin rule` from `builtin strategy` and
returns nested child results to the root.

Finite intervals are a representative example. Already-known or computational
endpoint order uses a direct fast path. Otherwise nonemptiness of
`closed_range(a, b)` reduces structurally to `a <= b`, and nonemptiness of
`range(a, b)` reduces to `a < b`. A closed real interval `'[a, b]` uses weak
order, while a real interval with either endpoint open uses strict order. The
smaller order child receives one fresh direct-rule layer, so a local bound such
as `2 <= n` can justify an index carrier beginning at `1` without allowing
unbounded verifier recursion.

For finite products, the direct rules also recognize pointwise multiplication
and a pullback along an already-known bijection. They do not search for or
construct the bijection.

For finite sums, a guarded pointwise equality on a closed integer range can
justify equality of the corresponding sums. Integer-shift reindexing can use
the same kind of guarded fact after translating the bounds. Neither rule
invents a bijection or assumes equality outside the stated range.

`reduce` and `finite_set_reduce` are generic objects, but they are not isolated
from the older mathematical vocabulary. When the operation is pointwise
addition and the seed is `0`, they bridge to `sum` and `finite_set_sum`; the
multiplication/`1` pair bridges to the corresponding products. The operation
can be user-defined: a verified concrete prop whose unfolding supplies
`forall x, y T: op(x,y) = x + y` is enough. A pointwise forall
`forall x S: f(x) = g(x)` supplies congruence, while an already-known `$bijective` fact supplies finite-set
reindexing. The checker uses these facts but does not invent them.

Range reduction has a stricter reindexing rule because it remembers order.
Equal-length integer intervals may be translated without any operation law:
`reduce(a,b,f,op,s)` equals
`reduce(c,d,fn(k Z) T {f(a+(k-c))},op,s)` when `a <= b` and
`b-a = d-c`. In particular, choose `c = 0` to rebase the indices to
`0...(b-a)`. The first or last endpoint may also be peeled off while threading
the accumulator seed in left-fold order. A bare `$bijective` fact is not
enough to reverse or permute these indices; that order-insensitive route is
available through `finite_set_reduce` after associativity and commutativity
have been verified.

The generic disjoint-union law retains exactly one copy of the seed:
`F(union(A,B),s) = F(A,F(B,s))` after `intersect(A,B) = {}` is known. The
seemingly more familiar `op(F(A,s),F(B,s))` would count `s` twice and is false
unless additional identity assumptions are available. For seed `0` addition
or seed `1` multiplication, bridge to the existing finite sum/product object
and use its specialized laws.

Some common one-step implications are direct rules themselves. For example,
known facts `n $in N` and `n > 0` directly establish `n - 1 $in N`; the rule
does not need to derive an intermediate `1 <= n` through a second builtin call.
Known `n $in N+` also directly establishes `n - 1 $in N`. For a strictly
positive result carrier, add `n > 1` to prove `n - 1 $in N+`.
Likewise, known integers `a`, `b` and `a < b + 1` directly establish
`a <= b`; this is the discrete adjacency bridge behind the familiar
equivalence `a <= b <=> a < b + 1`.

Function qualifications come from stored facts rather than the syntax used to
introduce a name. Known `g $in fn(x R) R` permits a correctly typed call; a known
equality indexed on `g` to an anonymous function supplies its body. For example:

```litex
have fn f(x R) R = x + 1
let g = f
g = fn(t R) R {t + 1}
g(4) = 5
```

The explicit equality publishes the function body on `g`. The last line reads
that exact property before checking `4 + 1 = 5`; it does not follow an alias
chain. Membership alone has no such body information. Unknown
bodies, invalid arguments, and failed local proof steps cannot establish a
particular return value. Default struct field names still follow the view
selected by a definition.

Constructor and definition strategies remain local. They can check a dependent
tuple as a struct, project a callable field through one checked constructor,
or unfold one literal/checked/template set builder or one exact indexed named
builder for membership. They do not scan all local named definitions.

Inside a `struct` `<=>:` block, equivalent facts instead form an ordered local
filter context. After a fact is well-defined it is staged without definition
inference, so an earlier `value != 0` can make a later `1 / value`
well-defined. Reversing those two facts still fails. The same ordered check is
used at definition time and whenever the instantiated struct carrier is
checked; the temporary facts never leak into the surrounding environment.

Equality and other atomic facts share a search-level ceiling. Stored facts,
identity/alpha and stored equality paths, followed by closed exact calculation
and structural membership, form level 0 (`Direct`). Special-property premises
use level 0; builtin premises use level 1; strategy and definition/forall
premises use level 2. Rewrite is available once at the highest level and keeps
the residual goal's level. WD remains mandatory and inherits the current
ceiling. Independent strategy/deep recursion budgets have been removed.

The closed-calculation branch does not consult stored numeric representatives or unfold
functions. It evaluates closed numeric equality, real order and standard-set
membership, and records exact values under `by_closed_calculation`. For example,
`1/3 < 1/2` is available to a restricted premise. Given `a = 2`, the goal
`a+1=3` still needs a separate substitution route. WD is always checked before
truth search: `1/0=1/0` remains invalid. The finite enumeration example in the
[Direct tracer](../examples/proof_nodes/equal/direct_closed_calculation.lit)
works without first asserting the numeric memberships. This does not settle
all remaining composition/geo failures; see the [current receipt](../src/execute/execute_fact_stmt/builtin_entry_verification.md).

Deterministic carrier composition is also available at Direct. With `n in N`,
`((n+1)+1)+1 in N` follows by traversing the addition tree, without consuming
another search level per constructor. Likewise, `floor(x)+1 in Z` reads the
checked floor codomain and addition closure. Each leaf cites an existing type
or uses a closed calculation/fixed builtin signature; no SP or full search is
called. Missing leaf types remain a miss, and all object WD obligations remain
mandatory. See the [structural carrier tracer](../examples/proof_nodes/atomic/direct_structural_membership.lit).

Separately, a full equality goal reuses the same constructor matcher while
allowing each corresponding child equality to use the bounded builtin/equality
verifier. Function applications align
from the final argument group backwards, so `f(a, b) = g(1, 2)(a, b)` reduces
to the function-part equality `f = g(1, 2)` together with the corresponding
argument equalities. Known-fact lookup can transport another predicate through
the known-only congruence route, but it does not launch the fuller child-proof
route implicitly.

For integers, the checker also recognizes the two exact singleton intervals:
`n <= x < n + 1` closes `x = n`, and `n < x <= n + 1` closes
`x = n + 1`. An exact known pointwise universal packages `$fn_eq(f, g)` only
when the defined function carriers are alpha-equivalent.
Once that global function-equality fact is stored, inference stores `f = g` in
the ordinary equality class, so constructor congruence can also prove facts
such as `power_set(f) = power_set(g)`. A mere pointwise forall on a proper
subset of the domain does not trigger this global inference.

Function metadata has a narrower lookup contract than ordinary equality
proving. Signatures, bodies, return carriers and finite coordinates use
checked declarations and properties indexed on the exact object. They do not
search its equality class. For example:

```litex
have fn step(x R) R = x + 1
let alias = step
alias = fn(t R) R {t + 1}
alias(3) = 4
```

The third line proves and publishes the body on `alias`; the last line reads
that direct property. A signature membership publishes callability without
publishing a numeric body. Template instances are read from their declarations.
This avoids rebuilding the graph of all visible equalities for a metadata
query; ordinary equality proofs can still establish explicit endpoints.

A strict positive premise also proves a square root is nonzero:
`x > 0 => sqrt(x) != 0`. Merely knowing `x >= 0` does not trigger that rule.

When a rule needs a universal, existential, or compound premise, the proof uses
an explicit reserved builtin theorem call such as
`release thm set_builder_member(x, B)` or
`release thm tuple_equal_from_coordinates(L, R)`. These calls check their
requirements with the full verifier and commit no conclusion on failure.
The canonical rational interface is
`release thm rational_has_unique_reduced_fraction(q)`. For a known `q $in Q`, it
stores `exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}`. The name is bare and
reserved and accepts exactly one argument. This conclusion is available only
through the explicit theorem handler; writing the existential directly does
not trigger an implicit reduced-fraction rule, and no trusted `std/basics`
theorem is required.
Finite-set foundations also have explicit theorem interfaces. After checking
`A $subset B` with finite `B`, one may call
`release thm subset_of_finite_set_is_finite(A, B)`. A stored inclusion now also
publishes lower-set finiteness when the upper finite certificate is already
available at the restricted stored/structural stage. This forward consequence
lets later size expressions pass WD without enabling deeper search. Without
that certificate, the explicit theorem or existing bounded strategy is still
needed. The [inference tracer](../examples/infer/atomic/subset_finite_upper_bound.lit)
shows this boundary. For finite `s`,
`release thm finite_set_has_bijective_index(s)` stores a noncanonical existential
index in `finite_seq(s, finite_set_size(s))`, bijective from
`closed_range(1, finite_set_size(s))`. These are bare kernel names, not
`basics::` definitions, and an arbitrary finite sequence is not thereby
defined bijective.
For compatibility with older source files, bare `by thm name(args)` remains a
parser alias for `release thm name(args)`. It follows the same all-conclusions
execution path and is rendered canonically as `release thm`. For new code,
write `release thm name(args)` for a bare call. Use `by thm` with `=>` when
selecting one atomic consequence.

When only one atomic consequence should escape, use the preview form
`by thm name(args) => atomic_fact`. The target must match a directly returned
atomic conclusion of that theorem instance, including explicit conjunction or
adjacent-chain components. Structural identity and bound-variable renaming are
allowed; independent computation, ambient facts, rewriting, equality reversal,
and combining conclusions cannot replace the match. The proof cites that
returned conclusion. Only the selected fact is committed to the parent; its
normal inferred consequences may still be stored. The selected fact must be
well-defined in the parent, and a compound target or proof body is rejected.
To combine conclusions, use `release thm` and a separate proof step. The arrow
remains required for selection; only the separate bare legacy alias omits it.
Mathematical definitions similarly use explicit `by def A $subset B` and
`by def $injective(A, B, f)` statements. New code should use this inline
spelling; the older `by def:` plus one `? fact` goal remains accepted for
compatibility. At the top-level verification entry, a
bare positive concrete predicate can also be proved from its defining clauses
before known `forall` matching and user strategies. `by def` remains useful
when that proof route and its output should be explicit. Its execution entry
requires definition expansion even for an already known target. Only the
expanded obligations use ordinary proof search. A true arithmetic comparison
or SetBuilder membership therefore does not become a supported `by def` target;
write those facts directly.

This convenience is also part of the trust boundary. Builtin objects, builtin
facts, builtin statement behavior, and builtin verification rules all deserve
tests, examples, and audit-friendly output. They are not hidden magic; they are
the built-in mathematical interface that makes short Litex proofs possible.

## If there are ten thousand `forall` facts, will proving one proposition become slow?

It can become slow if all ten thousand universal facts are active automatic
matching candidates in the same context. Litex's proof model uses known facts,
builtin rules, substitution, and known `forall` facts to justify later facts.
That is useful because users can write the mathematical fact they want, but it
also means the active context should not be treated as an unbounded global
search space.

There are two main design answers.

First, use `thm` for named theorems that should be called explicitly. A
`thm` proves and stores a named theorem, but it does not add its `forall` body
as an ordinary automatic `forall` matching fact. To use it, the proof says
`release thm name(args...)`. That makes large, classic, expensive, or
parameter-sensitive results explicit proof dependencies instead of background
noise.

Second, organize broad mathematical background into source-local cite packages.
A theorem about groups should live beside the source that needs it; a theorem
about real analysis should live beside that analysis source. The owning module
imports the package in `litex.config` when that background is actually needed. This keeps the active
known-fact and known-`forall` space closer to the topic of the current proof.

## Can an imported package's public symbols be used without the module prefix?

No. Cross-module references always use canonical qualified names such as
`A::b` or `basics::theorem`. Module names and symbol names are separate, so
`A` may still be both a module head and a local object. Interactive terminal
imports are also qualified-only and are not valid inside Litex source.

Import aliases belong to the importing package's `litex.config`. Two packages
can each use `Common = "./dep"` for different directories; references resolve
through their own manifest and the normalized path. Two aliases for the same
directory share the same module. Alias duplication within one manifest is
still rejected. The global display label is separate from this local alias.

A practical rule of thumb is:

- use automatic `forall` matching for short, local, common facts whose intended
  instantiation is obvious from the goal shape;
- use `claim:` with a `? forall ...` goal, or direct `forall` facts, when you want a helper to behave
  like local reusable context;
- use `thm` plus `release thm` when every conclusion should be visible, or
  selected `by thm ... => fact` when only one atomic consequence should escape
  in the proof;
- put unfinished background in a source-local cite package and import only
  the facts needed for the current file.

This is not only a performance issue. It is also proof readability. If a fact
is mathematically important, the proof is often clearer when it names that fact
directly.

## What is a type in Litex?

In Litex, "type" is mostly a set-theoretic parameter annotation, not a type in
dependent type theory.

When a user writes `have x R`, `forall x R:`, or `exist x R st { ... }`, the
annotation `R` means that `x` is an object with the membership fact `x $in R`.
The same idea applies to `Z`, `N`, `{1, 2, 3}`, `cart(R, Z)`, `power_set(S)`,
and other ordinary set objects. The annotation gives Litex well-definedness
information and a fact that later proof steps can match.

Some annotations are parameter kinds rather than ordinary set domains. For
example, `have A set`, `have B nonempty_set`, and `have c finite_set` introduce
names and record facts such as `$is_set(A)`, `$is_nonempty_set(B)`, and
`$is_finite_set(c)`. These are not meant to say that `set` is one giant set
containing all sets. They are surface forms for introducing mathematical
objects with the corresponding set-theoretic properties.

The To-Lean target preserves this distinction as proof evidence: a quantified
`A set` receives an explicit `hA : Litex.IsSet A`, while an ordinary `x A`
receives membership in the exact set representative selected from `hA`.
`Litex.Set` is the Lean exact-carrier representation type, not a source-level
set of all sets, so neither `A $in Litex.Set` nor erasing `$is_set(A)` to
`True` is a faithful translation.

Function "types" are also set-theoretic function spaces. A definition such as
`fn(x S) T` means a function object whose inputs come from `S` and whose values
come from `T`. Each ordinary function parameter domain must be a fixed set
object: a later obj domain must not cite an earlier parameter of the same
`fn` signature (so `fn(x R, y S(x))` is rejected). The return set and
`: domain conditions` may cite the function parameters; an application
substitutes its actual arguments into those set expressions. These domains and
return sets are still ordinary set objects. Broader parameter kinds such as
`set`, `nonempty_set`, and `finite_set` belong in definition or theorem
headers (where `forall S set, x S` is sequential and allowed), not as ordinary
function input domains. This is why `fn(x set) R` is not the right way to say
"a function that accepts any set." Set-theoretic functions must have one
concrete domain object per parameter position, and Litex does not treat "the
collection of all sets" as one ordinary set object.

This has an important consequence: a Litex object does not have one unique
canonical type that determines all later notation. The same object may be known
to belong to several sets. Litex uses the currently verified membership,
function-space, and set-property facts to decide whether expressions are
well-defined and whether later facts can be proved.

## Why does Litex emphasize relationships instead of construction ancestry?

Many familiar mathematical objects can be constructed in more than one way.
Integers can be built from pairs of natural numbers, rationals from pairs of
integers, and reals from Cauchy sequences, Dedekind cuts, decimal expansions,
or other equivalent constructions. Litex does not make ordinary users inherit
all of that construction history every time they write `Z`, `Q`, or `R`.

Instead, Litex is relationship-first. The kernel and source-local packages can
expose common objects and the relationships that make them useful: membership,
arithmetic, order, density, floor bounds, completeness, function spaces, set
operations, and so on. For many day-to-day proofs, the exact construction of
`R` from `Q` is not the point; what matters is that `Q` embeds into `R`,
rationals are dense in reals, Cauchy real sequences converge, and bounded
nonempty real sets have least upper bounds.

This is a deliberate design trade-off. Litex's builtin `R` is a mathematical
surface with verifier-visible properties, not a proof term saying "this object
was constructed by this exact chain of quotients and completions." A source
that needs rational density or real completeness should state that background
in a visible source-local cite package, with every `trust` boundary recorded,
rather than loading a global numeric library.

The practical rule is:

- use builtin objects such as `Z`, `Q`, and `R` directly when the proof only
  needs their ordinary relationships;
- put broad semantic background, such as density of `Q` in `R` or completeness
  of `R`, in a source-local cite package and make the trust boundary visible;
- keep chapter-specific or domain-specific theorems local until they are worth
  extracting into a reusable package;
- formalize a construction explicitly only when the construction itself is the
  mathematical subject.

So Litex is not anti-foundational. It simply chooses a lighter user-facing
route for ordinary mathematics: expose the relationships people actually use,
then make any trusted background facts explicit enough to audit.

## Does Litex define `R` from `Q`?

No. In current Litex, `Q` and `R` are builtin carrier objects. Litex records
mathematical relationships between them, but the kernel does not say that an
element of `R` is literally made from an equivalence class of objects from
`Q`.

The Analysis I translation makes this distinction concrete. Tao's source
defines real numbers using equivalence classes of rational Cauchy sequences.
The Litex chapter instead keeps the builtin `R` and introduces the relation
`$has_formal_limit_in_Q(a, x)`, meaning that a rational Cauchy sequence `a`
represents the builtin real `x`. The theorem
`cauchy_sequence_representative_in_Q_exists` says that every builtin real has
such a representative. It is a representation or compatibility theorem, not
a definition of `R`. Its proof is currently an explicit `trust` boundary in
the textbook.

The Cauchy-sequence construction is only one possible presentation of the real
numbers. Other standard approaches include:

- Dedekind cuts of `Q`;
- nested rational intervals;
- infinite decimal expansions, after identifying expressions such as
  `0.999...` and `1.000...`;
- a completion of `Q` characterized by a universal property;
- an axiomatic complete Archimedean ordered field containing `Q`.

To connect the builtin `R` completely with the rational-Cauchy presentation,
one would want a checked interface stating that:

1. every rational Cauchy sequence represents a unique real;
2. every real has a rational Cauchy representative;
3. two rational Cauchy sequences are equivalent exactly when they represent
   the same real;
4. addition, multiplication, and order on representatives agree with the
   corresponding operations on `R`.

With that interface, one may say that the builtin `R` is isomorphic to the
Cauchy completion of `Q` with the relevant ordered-field structure. One still
should not say that the two are definitionally the same object. The same
distinction appears one chapter earlier: integer fractions can represent
builtin rationals without making builtin `Q` definitionally equal to a
quotient of pairs of integers.

Litex can formalize a particular construction when that construction is the
mathematical subject. Its default builtin interface simply does not force all
later users to inherit one privileged construction history.

## Are `sin`, `cos`, `tan`, and `cot` numerical functions?

They are native symbolic real objects in the current beta. Arguments
are real angles in radians. The verifier knows a small central interface and
derives parity, difference and double-angle formulas, selected `pi` values,
periodicity, cofunction formulas, and range bounds through one canonical
normalizer.

`sin` and `cos` are total on `R`. A use of `tan(x)` requires
`cos(x) != 0`, while `cot(x)` requires `sin(x) != 0`; an undefined expression
fails well-definedness before equality checking. The preview remains symbolic:
`eval` and Python extraction reject native trigonometric expressions explicitly.
The current parser also accepts real `arcsin`, `arccos`, `arctan`, and
`arccot`, with domain and principal-range rules described in the
[manual](Manual.md#native-real-trigonometry-beta-preview). Exact rational
coefficients of `pi` can establish principal-range comparisons without decimal
approximations. Quarter-angle inverse examples use the forward value and an
explicit right-inverse equality chain; `arccot(-1)=3*pi/4` follows the `(0,pi)`
branch. This is not a complex-trigonometry or numerical-evaluation interface. Lean compilation is
not connected to the current Cargo build; see the [CLI boundary](cli.md#lean-compiler-boundary).

## Does the native `C` scalar system turn every number into a complex value?

No. In the current beta, `C` is the largest default scalar carrier and
the standard sets satisfy `N ⊆ Z ⊆ Q ⊆ R ⊆ C`. The verifier still preserves
the narrow conclusion it can establish. Integer arithmetic remains integer
arithmetic, and real arithmetic remains real arithmetic; an expression falls
back to `C` only when no narrower supported carrier applies.

`C*` denotes the nonzero complex carrier `C \ {0}`. Thus `R* $subset C*`,
`C* $subset C`, and a definition such as `have z C*` supplies both `z $in C`
and `z != 0`. The reverse inclusion `C $subset C*` is false, and `0 $in C*`
is rejected.

This is also why complex equality does not add a complex order. The relations
`<`, `<=`, `>`, and `>=`, sign reasoning, real intervals, `abs`, `sqrt`, and
`log` still require real operands. `C_abs` is the separate complex modulus,
with a nonnegative real result.

The native complex layer remains symbolic in this release. Verification now
also performs bounded exact polynomial/rational normalization with
`i * i = (-1)`, so identities such as
`2 * i + 1 = i * i + 2 + 2 * i` and
`(1 + i) * (1 - i) = 2` verify directly. Division still needs its ordinary
nonzero well-definedness proof. `eval` and Python extraction do not acquire a
complex runtime representation.

Earlier Lean artifacts describe a separate complex-normalization backend;
they do not establish compiler coverage for the current `src/` pipeline.
Names such as `C`, `i`, `re`, `img`, and `C_abs` are reserved native forms;
sources using them as ordinary identifiers must choose other names. See the
[complex scalar reference](Manual.md#complex-scalars-beta-preview).

## Why not just import a big library and cite the theorem?

For many mature proof-assistant projects, importing a large library and citing
the strongest available theorem is the most efficient path. That is a real
advantage of systems with large libraries.

Litex is aimed at a different workflow, especially for textbooks and education.
If the goal is to formalize a calculus or analysis book, the proof script
should ideally show the derivation the book is teaching: definitions, local
lemmas, intermediate facts, and the way later results use earlier ones. If the
main work becomes "find a theorem in a mathematical dictionary and cite it",
the final result may verify, but the code no longer records the learning path.
It records where the result already exists.

Litex therefore tries to make the basic mathematical ground cheap enough that
users can write the book's proof directly. Builtin objects and small background
interfaces let the file get started without a huge import. Larger packages
still matter, but they should provide visible background or reusable interfaces,
not erase the central proof of the current chapter.

This is not a claim that imports are bad. It is a claim about where the
mathematical labor should live. For textbook-first formalization, the proof
script should be the derivation, not only a pointer into a theorem database.
In systems such as Lean or Isabelle, the large-library route is often excellent
formal engineering. Litex is exploring whether a lighter base can make the
book's own proof cheap enough to write and check directly.

## Why can an elementary-looking result still need a cite interface or explicit trust?

Ordinary mathematical prose omits a great deal of supporting infrastructure.
That does not make a result impossible to formalize, nor does it make an
unfinished Litex proof a language failure. It means the file must say which
interface the prose took for granted. Mature libraries often already contain
many such interfaces; a source-local development may not yet have the one its
current theorem needs.

For example:

- A nonempty finite subset of `R` having a maximum can require a finite-set
  induction or enumeration interface, a nonempty witness, and the fact that
  inserting one real preserves a chosen maximum.
- Native `gcd(a, b)` is available for non-all-zero integer pairs. A textbook
  that wants to explain its construction may still define a transparently
  named source function such as `gcd_by_finite_divisors`, prove its
  specification, and bridge it to native `gcd`; see
  [`gcd_from_finite_divisors.lit`](../examples/_internal/regression/gcd_from_finite_divisors.lit).
- Native `$coprime(a, b)` follows the elementary `Nat.Coprime` surface and is
  available for all natural pairs without importing `std/basics`; it is false
  at `(0,0)`. Integer and general-ring coprimality remain distinct interfaces.
- The bound `|S union T| <= |S| + |T|` can require a cardinality interface:
  a decomposition into disjoint pieces, or an injection/bijection argument
  that makes overlap visible.

Do not mark an entire result `trust` merely because it feels obvious. Preserve
the source-facing theorem, make the smallest natural Litex attempt, and record
the exact missing bridge plus the verifier feedback. Keep a one-off bridge as
the smallest local proof debt. When the same background fact genuinely recurs,
give it a named source-local cite interface. Consider a shared `std` interface
only after its meaning is stable and several independent uses show that it is
really common background. The rest of the source proof should remain checked
wherever possible.

## What are the boundaries of Litex's type system?

Litex deliberately does not try to be a full dependent type theory in the Lean,
Coq, or Agda sense. Its surface is closer to set-theoretic ordinary
mathematics: objects belong to sets, structures are subsets of Cartesian
products with named views, predicates express properties, and proofs grow a
verified context of facts.

Function parameter domains and return sets are fixed relative to the current
signature. They may use an already-bound enclosing carrier, as in
`forall q set` followed by `fn(c1, c2 q) q`, but may not use parameters of
that same function. Thus `fn(S power_set(R), x S) R` and
`fn(S power_set(R)) fn(x S) R` are rejected during parsing. Domain conditions
and function bodies can depend on the parameters, as in
`fn(x R: x > 0) R {x + 1}`. A more precise result property is expressed as a
separate fact, not an argument-indexed return set.

The parser delays function parameter registration while parsing their carriers
and removes that temporary visibility while parsing the complete return
object. WD enforces the same boundary independently. Ordinary `forall` and
`exist` binders retain sequential dependencies; `template` supports families
such as structures, sequence spaces, and quotient constructions indexed by an
arbitrary carrier or by hypotheses. Litex still does not expose
universe-polymorphic type families, proof-indexed computational types, or proof
terms as ordinary computational data.

For a concrete quotient-group construction, see the quotient-group section in
the Manual.

## What is a `struct` in Litex?

A `struct` is not a class or a record object with hidden fields. It is a named
view of a subset of a Cartesian product. The field names label the positions in
that product.

A structure must declare at least two fields. There is no one-field “identity
view” of a sole carrier (parse error:
`struct definition expects at least two fields`).

For example:

> **Migration example:** Current `src/` checking stops at `release_thm` (`release thm …`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
struct FirstQuadrant:
    x R
    y R
    <=>:
        x > 0
        y > 0

release thm struct_member((1, 2), &FirstQuadrant)
have p &FirstQuadrant = (1, 2)
p.x = 1
p.y = 2
```

Read this as a named set-builder over `cart(R, R)`:

```text
&FirstQuadrant = { p in cart(R, R) | p(1) > 0 and p(2) > 0 }
```

Here the field name `x` labels index `1`, and `y` labels index `2`. Because
`p` was defined directly in `&FirstQuadrant`, `p.x` is its first component
and `p.y` is its second component. This direct `p &FirstQuadrant` binding is
the only automatic property-release case: it opens one struct layer and stores
Cartesian membership, ordinary field/coordinate bridges, field carriers, and laws.

For any other definition-owned struct expression, write
`release struct def expression`. The statement first verifies that exact expression
belongs to its already-defined struct carrier, then releases exactly one
layer. There is no `as &Struct` syntax and no recursive opening. For example,
if `make_outer(t)` returns `&Outer` and `Outer.inner` is defined as `&Inner`,
then `release struct def make_outer(t).inner` opens `Inner`, not `Outer` and not any
struct below `Inner`.

For a multi-field value `e`, opening stores exact Cartesian membership and
equations such as `e.x = e(1)`, together with field carriers and laws. It stores
no tuple shape or dimension fact. These tuple/struct
bridge facts are not stored anywhere else, except that the struct-membership
verifier may use the tuple representation internally while checking membership.

For a parameterized struct, `&Name<a>` is the instantiated struct set. For a
non-parameterized struct, `&Name` is the struct set. Both are ordinary sets and
are valid in every binder or function-signature position that expects a set.

The same tuple may belong to several struct sets, but that does not make field
selection ambiguous: named fields belong to the definition of a symbol or
function return. Giving a fresh binding the carrier `p &FirstQuadrant` fixes
that ownership for `p`. There is no surface form for changing it at one use.

The same definition-owned rule supports consecutive field chains. If
`outer &Outer` and `Outer.inner` is defined directly as `&Inner`, then
`outer.inner.value` is valid. The intermediate field owner comes from the
field definition, not from proof search. A named set definition or a later
fact saying that `outer.inner` belongs to `&Inner` does not add fields.

This validity is only well-definedness. Looking up `outer.inner.value` checks
that the defined field path exists; it does not store field membership,
field/index equalities, or instantiated struct laws. Definitions now publish
universal laws over their parameters and an instance, flattening consequent
universals while keeping conditions and existential witnesses in scope. Those
laws can be used by ordinary known-forall matching when their carrier and
premises verify, including for a nested instance. Use `release struct def
outer.inner` to materialize its representation and property facts. A function's
explicit struct return carrier makes `f(t).field` a legal path without itself
opening the result.

Postfixes compose when definitions provide the carriers. A final field may be
callable, so `space.scalars.mul(a, b)` is supported when `scalars` is a
struct-valued field and `mul` is callable. Likewise, after
`have fn make_inner(...) &Inner = ...`, `make_inner(...).value` is valid.

This is not a unique nominal type, and Litex does not infer fields from all
known memberships. A later fact `p $in &FirstQuadrant` supplies only that
membership proposition; it does not eagerly store positional consequences,
laws, or `p.x`. Nor can it be opened with `release struct def p`, because `p` has no
definition-owned `FirstQuadrant` view. If a `p &Point` also belongs to
`&ComplexPair`, `p.x` remains the `Point` field fixed by its definition. To use
the other names, introduce a new object explicitly, for example
`have p2 &ComplexPair = (p.x, p.y)`, then write `p2.real` and `p2.img`.

## Why would a vector space own its scalar system?

It makes the ordinary single-space interface smaller and more faithful to the
mathematics. A `VectorSpace<s,V>` exposes `space.zero`, `space.smul(a,v)`, and
`space.scalars.mul(a,b)` from one selected structure. The same pattern lets an
inner-product space own both its scalar geometry and its vector-space
operations.

This does not silently make arbitrary spaces compatible. A relation that joins
two spaces—such as `is_linear_map(Vspace,Wspace,T)`—records
`Vspace.scalars = Wspace.scalars` once. Bilinear, tensor, and other
multi-space relations use the same boundary. Scalar-only constructions, such
as polynomial arithmetic, still receive an explicit `ScalarSystem` because no
vector-space owner exists there.

## Why can an anonymous function be written as `fn(x R) R {(-x)}`?

This is intentional shorthand, not a typo. The fully explicit anonymous
function form is `fn(x R) R { (-x) }`: the parameter `x` ranges over `R`, the
return set is `R`, and the body is `(-x)`.

When all parameters have the same domain as the return set, Litex also accepts
the compact form `fn(x R) R {(-x)}`. Similarly, `fn(x, y) R {x + y}` means that both
inputs range over `R` and the return set is `R`; it is the compact version of
`fn(x R, y R) R { x + y }`.

The compact form is useful in short mathematical expressions, such as passing
`fn(x R) R {x}` to a sum or using `fn(x R) R {(-x)}` as a group inverse operation. In
explanatory documentation or when the domain and return set are easy to
confuse, the explicit form is usually clearer. Both forms denote ordinary
anonymous function objects and can be compared by Litex's function-equality
rules.

## Why does Litex have `template`?

`template` is the mechanism for definitions that are uniform in a parameter
such as a set, a structure, or a carrier satisfying some condition, when that
parameter cannot be modeled as the input of one ordinary set-theoretic function.

A useful way to read a template is: first pretend that the angle-bracket
parameters have already been introduced and satisfy the header conditions.
Then run the statements inside the template body as ordinary definition
statements in that temporary context. If those statements check, Litex stores
the result as a family. When you later write an instance such as `\name<R>`,
Litex substitutes the concrete argument for the parameter and gives you the
corresponding defined object or function.

For example:

```litex
template<s set>:
    have carrier_copy set = s

\carrier_copy<R> = R
\carrier_copy<Z> = Z
```

The reading is: first fix an arbitrary set `s`; in that temporary context,
`carrier_copy` is definable as `s`; because this works for every `s set`, the
family can later be called as `\carrier_copy<R>`, `\carrier_copy<Z>`, and so on.

A checked template also publishes the facts supplied by its ordinary body
definition, with the angle-bracket parameters universally quantified and
header conditions retained as premises. For example:

```litex
template<S nonempty_set>:
    have member S
\member<R> $in R
```

The template stores `forall S nonempty_set: \member<S> $in S`, so ordinary
known-universal search supplies the instantiated membership. The same rule
applies to object equations and selected-witness properties, function
signatures and guarded equations, unique-existence selection, and replacement
facts. It publishes the definition stores, not the temporary scope's assumptions
or proof intermediate steps. See the [acceptance example](../examples/stmt_nodes/definition/template_definition_facts.lit).

The simplest reason is the one above: a Litex function input must range over a
particular domain set. But `set` is not itself a particular domain set. It is a
surface parameter kind meaning "introduce a parameter and check that it is a
set." So a family defined for every set should carry that set in the definition
header, not hide it as a fake function argument.

A template instance keeps its parameters visible in angle brackets. If a family
is defined as `template<s set>:` with body `have name ...`, then the instance at
`R` is written like `\name<R>`, and the instance at `Z` is written like
`\name<Z>`. The chosen set travels with the name. This is useful because every
use shows which carrier or parameter the object belongs to, and different
instances cannot be confused.

This pattern appears throughout ordinary mathematics:

- `seq(S)` is conceptually a family indexed by the value set `S`; a sequence
  over `S` is essentially a function from positive integers into `S`, not one
  universal function type over all possible value sets.
- A group structure is a family over a carrier set. `&Group<R>` and
  `&Group<Z>` are different struct carrier sets because the carrier is part of the
  mathematical data.
- A quotient construction is naturally a family over a concrete group together
  with the relevant normality or equivalence assumptions. The quotient is not
  one global function from "all groups" to sets; it is a parameterized
  construction whose parameters should remain visible.

This is the point of `template`: it gives Litex a direct way to express
mathematical families while staying set-theoretic. Ordinary functions are for
maps whose domain is a known set. Templates are for families indexed by
mathematical parameters that should stay attached to each instance.

For example, `seq` is a built-in object form in Litex, but if we wanted to
define the same idea ourselves, we would define a family of function spaces:

```litex
template<S set>:
    have my_seq set = fn(n N+) S

\my_seq<R> = fn(n N+) R

```

This verifies the instantiated set equality. Automatic membership transport
into that template instance is still a gap; the following currently soft-fails:

```text
template<S set>:
    have my_seq set = fn(n N+) S
have a fn(n N+) R
a $in \my_seq<R>
```

The important point is that `S` is not an ordinary function input. It is a
parameter of the family. After instantiation, `\my_seq<R>` is the ordinary set
of real-valued sequences, namely functions from `N+` to `R`. Similarly,
`\my_seq<Z>` would be the set of integer-valued sequences. The angle-bracket
argument keeps the value set visible at every use.

The built-in `seq(S)` can still have special syntax or verifier support. The
template version shows the underlying set-theoretic shape: a sequence type is a
parameterized family of function spaces.

## If AI can write Lean proofs, what is Litex for?

AI can make theorem-prover code much cheaper to generate. It can often find
lemma names, write tactic calls, and discharge routine side conditions. That
is valuable, but generation cost and understanding cost are different. A
machine-generated proof can be accepted by a kernel while still requiring a
mathematician to reconstruct the simple mathematical idea from a large amount
of system-facing code.

Litex tests whether the durable artifact can stay closer to that mathematical
idea. AI may fill routine details, while the checked source records the facts,
witnesses, cases, definitions, and calculation chains that a reader needs to
understand and modify the argument. When Litex omits a routine step from the
surface, its verifier output should still expose the rule, known fact,
definition, theorem, or explicit assumption that justified the step.

This is not a claim that Lean proofs must be long or unreadable. Lean has
powerful automation and can support concise, well-designed interfaces. Litex
is testing a different default interface: can checked mathematics remain
readable after AI has made proof generation abundant? The epsilon-product
example in [Representative Lean–Litex Example
Comparisons](Representative_Lean_Litex_Example_Comparisons.md#ai-lowers-generation-cost-not-automatically-understanding-cost)
is the concrete test: the durable proof should preserve the short estimate
`abs(x * y) = abs(x) * abs(y) < epsilon * epsilon <= epsilon` while keeping
its side conditions auditable.

## What is fundamentally different about Litex?

Litex's core difference is its matching-and-substitution verification
interface.

The user writes mathematical facts: equalities, memberships, implications,
existential witnesses, `forall` statements, function facts, set facts, and
prop facts. The verifier then asks whether the new fact follows from the
current verified context by builtin rules, known facts, known `forall` facts,
definitions, matching, and substitution.

So the central interaction is not "choose a tactic that transforms the proof
state." It is closer to:

1. write the next mathematical fact;
2. let Litex match it against the verified context and trusted mathematical
   background;
3. if it succeeds, store the fact and continue growing the context;
4. if it fails, inspect whether the missing step is a missing fact, missing
   theorem call, missing library support, or a real gap in the argument.

This is why Litex proofs often look like ordinary mathematical prose or
calculation chains. The proof script exposes the facts that should be true, and
the checker performs routine matching and replacement steps that a human reader
would usually do silently.

For example, once `b - a > 0` or `0 < b - a` has been verified, the
positive-difference builtin can prove `a < b` for real `a` and `b`. It reads the
saved bound and cites that premise; it does not recursively discover the bound.
Replacing the premise with `b - a >= 0` does not justify strict order. The
[runnable example](../examples/proof_nodes/atomic/by_builtin_rule/greater_from_positive_difference.lit)
also covers the corresponding `>` goals.

Saved negative differences now give the complementary real order. Weak targets
accept a strictly stronger saved bound; a weak bound never proves a strict
comparison. The fixed negative forms `0-u`, `-u`, `(-1)*u`, and `u*(-1)` use
these same bounded saved-premise bridges. For example:

```litex
forall a, b R:
    a-b<0
    =>:
        a<b

forall u R:
    -u<0
    =>:
        u>0
```

The selected premise retains its actual orientation, strictness and citation in
Detailed output. These leaves do not recursively search for a difference bound.
See the [signed difference tracer](../examples/proof_nodes/atomic/by_builtin_rule/signed_difference_order.lit)
and [negative sign tracer](../examples/proof_nodes/atomic/by_builtin_rule/negated_sign_order.lit).

Some routine consequences are saved when a verified fact enters the context.
For example, saving `n >= 0` after `n $in Z` publishes `n $in N` in that same
scope. More generally, a saved `b <= n` or `n >= b` needs both an integer
certificate for `n` and an available nonnegative certificate for `b`. This
lets a later call to a function with domain `N` cite its argument's carrier,
including inside an induction goal's WD check. A nonnegative real value alone
does not justify `N`, and a weak bound does not justify `N+`. See the
[lower-bound infer tracer](../examples/infer/atomic/weak_integer_lower_bound_in_n.lit).

For real-valued functions, routine carrier checks can also compose across
field expressions. The target `f(x)^2 / 4 <= f(x)^2 / 4` first needs the
fraction to be real, before the claim body runs. The constructor-closure
builtin checks the function-return leaves and integer exponent with its
existing limited premise permissions. Division still needs a valid nonzero
denominator; a complex-only return does not gain a real carrier. The
[real constructor tracer](../examples/proof_nodes/atomic/by_builtin_rule/real_arithmetic_constructor_closure.lit)
retains this goal-WD example and the focused tests cover rejected boundaries.
The same separation applies to real-valued Cartesian functions inside `abs`:
argument domains are checked by the enclosing WD, while arithmetic closure
consumes the return signatures. The [Cartesian function tracer](../examples/wd/real_cart_function_arithmetic.lit)
checks a real difference and a quotient with its nonzero guard.

This does not mean Litex proves arbitrary goals by magic. It means Litex places
ordinary mathematical structure inside the verifier and visible local
background packages, then gives the user a fact-oriented interface to that
structure. The trade-off is explicit: Litex has a larger trusted implementation
than a small-kernel proof assistant, so builtin rules, infer rules, `trust`, and
imported facts need clear boundaries, tests, and audit-friendly output.

Litex should therefore be described as complementary to Lean, Coq, and Isabelle,
not a replacement for them. Those systems expose deeper foundations and much
larger mature libraries. Litex tests a narrower hypothesis: many ordinary
mathematical arguments may become cheaper to check if the main proof interface
is verified context growth through matching and substitution.

## Why does Litex think of proof as context growth?

Litex's proof interface is fact-oriented. A proof is usually written as a
sequence of mathematical facts. When a fact is verified, Litex stores it in the
current context, and later facts may use it by matching, substitution, builtin
rules, or known `forall` instantiation.

For example:

```litex
have x R = 2
x + 1 = 3
```

The second line is not a tactic script. It is the mathematical fact the user
wants. Litex checks that `x` is known to be `2`, reduces the equality to an
ordinary numeric calculation, and then stores the new fact. This is the core
reader experience: write the next useful fact, let the checker explain why it
follows, then continue from the stronger context.

Bare `have x R` is witness selection from a nonempty carrier; it differs from
the explicit definition `have x R = 2`. The current runtime retains verification
and storage evidence for these steps. An independent Lean replay would need to
preserve that distinction. The earlier compiler experiment is not built by
the current `src/`; no current Lean coverage follows from this example.

When the exact existential is already a known fact, the verifier records that
direct `FactId` citation before considering specialized builtin existential
routes. This retains the source of the accepted fact; it does not widen
ordinary existential proof search.

## Does zero-premise direct evaluation replace every symbol by an equal object?

No. Direct evaluation checks the atomic fact as written. It does not unfold
every argument through `have x T = value` definitions and then retry the
evaluation on a rewritten target.

For example, `2 $in Z` is zero-premise direct evaluation: it closes the fact
without generating a child fact that must also be proved. After
`have one Z = 1` and `have integer_set set = Z`, the fact
`one + 1 $in integer_set` does not become direct evaluation merely because all of
its arguments have equal closed representatives. Known-fact matching may
still transport an already proved fact through checked equalities, but it does
not manufacture that source fact by running direct evaluation on rewritten
arguments.

For equality, the zero-premise phase also includes terminating structural
congruence. From known `x = y`, for example, matching products such as
`(x + 1) * (x + 2)` and `(y + 1) * (y + 2)` may be compared
constructor-by-constructor. This does not make arbitrary symbolic equalities
automatic: without the known leaf `x = y`, that product equality remains
unknown. Premise-producing mathematical equality rules are tried only after
these zero-premise routes fail.

## Why does Litex distinguish Success, Failed, and SessionError?

These three outcomes separate situations that are easy to confuse.

**Success** means Litex found a proof route (or completed a definition) from
builtin rules, known facts, known `forall` facts, definitions, or other
accepted context, and merged the temporary environment into the parent.

**Failed** (soft miss) means the statement did not succeed. The temporary
environment is discarded and the session continues. Common causes:

- search miss: the statement is meaningful, but current evidence is not enough;
- well-definedness miss: an object or fact is not legal yet;
- other soft statement failures in the same transactional envelope.

A soft miss is not a proof that the proposition is false. It may be false, or
it may only need a smaller intermediate step. Batch JSON keeps soft misses
inside `statement_results` with `"success": false` and a `why_failed` payload.

**SessionError** means a hard failure. The session must stop. Batch JSON
exposes this as top-level `"session_error"`.

An internal invariant conflict is reported explicitly as
`internal_bug: Litex internal bug: <specific reason>`. This is an implementation
bug in Litex, not an ordinary unproved statement. It stops the session; Litex
does not present the affected session as safe to continue or claim an atomic
rollback of an internal commit error.

This makes the feedback loop more useful. A search soft miss usually suggests
"add the missing mathematical fact." A well-definedness soft miss suggests
"fix the expression or its domain information before discussing truth." A
SessionError suggests "stop and repair the session invariant."

Some atomic equality failures include a narrower detail in the evidence tree.
If a known equality stops at a function-valued prefix such as
`trace(q) = base(q)` while the goal asks about `trace(q)(row)`, Litex reports
the unmatched outer application and that nearest prefix. This is guidance to
project or rewrite the prefix before applying the remaining argument; it does
not perform new congruence or accept the failed goal.

## Does a tuple call supply its coordinate carrier?

Literal and named tuples use ordinary function calls. The selected coordinate's
carrier is checked from its actual value or Cartesian member source:

```litex
forall x,y N:
    (x,y)(1)=x
    (x,y)(1) $in C
```

The direct carrier route `(x,y)(1) $in C` is also supported for this literal
value. Invalid inputs such as `(x,y)(3)` fail WD. Cartesian set equalities do
not recover a construction dimension or factor list; element membership
supplies the complete function domain and coordinate carriers.

## Which assumptions are available when checking an induction target?

For `by induc n from base`, target WD uses `n $in Z` and `n >= base`.
It does not use the induction hypothesis. Base and step bodies then run in
separate local scopes through the ordinary proof-body checker:

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
    n $in N
    have a N = 0
```

The bound `n >= 0` makes the target callable. The checked `n $in N` step
also supplies the natural carrier for its successor application. Changing the base
to `-1` rejects the target's WD. The same rules apply to `by strong_induc`;
its stronger hypothesis is supplied only after WD, in the successor scope.
Recursive function definitions additionally require every nested case list
to cover its parent guard and have disjoint siblings before publication.

## Why does Litex check well-definedness before truth?

Litex treats mathematical expressions as meaningful only when their objects,
domains, and side conditions are justified. This happens before the checker
tries to prove or disprove the fact.

For example, a function application must have an argument in the function's
domain, and a division must have a nonzero denominator. If those facts are not
available, Litex should report a problem with the expression, not merely say
that the desired equality soft-fails.

A function name introduced by `let` need not carry its signature directly.
After `let g = f`, well-definedness follows that exact transparent definition
from `g` to `f`, reuses `f`'s checked signature, and checks the actual arguments
against `f`'s domain. Atomic verification uses the same deterministic,
one-direction reduction and records proof evidence for it. This is not circular
truth checking or equality-class search: Litex follows only the stored
definition of the inspected `let` symbol, and it does not launch general
equality or `forall` search from well-definedness.

This design matters because many mathematical mistakes are not false theorems
but ill-formed statements: applying a function outside its domain, using a
projection from the wrong Cartesian product, or writing an expression with a
missing side condition. Litex tries to make that distinction explicit.

For a checked definition `have x S = value`, carrier compatibility belongs to
the statement's `verify_process` phase and runs before `x` is stored. When a
standard numeric source carrier can be established, the error reports both
the required `S` and that source carrier. Thus a `Z`-valued remainder reports
`required N` and `known Z`; later proof-body inequalities cannot retroactively
make that failed definition an `N` binding.

## Can a predicate premise make a later expression well-defined?

Yes, when it is a positive concrete predicate whose checked definition has the
needed consequence. Inside a `forall` premise list or an `exist` body, Litex
checks facts from left to right in a temporary scope. Each checked fact
is then assumed there and may expose sound definition consequences before the
next fact is checked.

For example, if `$nonzero_on(E, g)` is defined by `forall x E: g(x) != 0`, a
later anonymous-function body may safely contain `1 / g(x)`. The definition
supplies exactly the denominator obligation. Without that earlier premise,
the same expression is rejected as ill-defined.

This does not run arbitrary proof search while deciding whether syntax is
meaningful. It unfolds concrete positive definitions through the ordinary
guarded inference path; recursive definitions are cycle-protected,
`abstract_prop` supplies no clauses, and all temporary consequences disappear
when the quantified check ends.

## Why can't an existential or set-builder body contain `forall`?

Those bodies intentionally use a small property grammar: atomic facts, flat
conjunctions, chains, and disjunctions. The main engineering reason is index
keys: with only those four shapes, an `exist` lookup key stays easy to design,
so searching a known `exist` is a simple shape bucket plus exact or unify match.
An anonymous universal would add another binder scope inside a body that is also
reused for witnesses, matching, set-builder membership, substitution, and
inference. Keeping that extra scope out keeps both the key and every consumer
unambiguous.

Name the quantified condition instead:

```litex
prop is_reduced_fraction(p Z, q N+):
    forall z N+:
        p % z = 0
        q % z = 0
        =>:
            z = 1

have a Q
trust exist p Z, q N+ st {a = p / q, $is_reduced_fraction(p, q)}
```

`forall` remains a normal fact and remains valid inside the `prop` definition.
Only its anonymous use as an entry of an existential or set-builder body is
rejected.

## Why does Litex have both `claim` and `thm`?

`claim` and `thm` both prove facts, but they have different proof-interface
roles.

A `claim` is good for short, local, reusable context. After it is proved, its
fact is available to later lines in the ordinary context. This is useful for
helper facts that should behave like part of the current mathematical
environment.

A `thm` is good for important named results whose use should be visible. A
theorem is stored under a name and used explicitly with `release thm name(args...)`.
This keeps large, classic, parameter-sensitive, or source-package results
from silently becoming background search noise.

The distinction is partly about performance, but mostly about readability.
When a result is mathematically important, naming the theorem at the use site
often makes the proof easier to audit.

## Is proof debt a proof?

No. `trust` is explicit assumption injection, not a proof-producing command. It
is Litex's closest analogue to Lean's `by sorry`: it deliberately lets the
author cross the ordinary proof boundary. For example, both of these are
intentional uses of `trust`, not verifier bugs:

```litex
prop positive_real(x R):
    x > 0

trust 0 = 1
trust $positive_real({})
```

The second line is accepted even though `{}` was not previously known to
belong to `R`. A concrete `prop` parameter carrier is a proof-time condition
when the definition is used normally; it is not a formation check that limits
what the author may inject with `trust`. After the trusted proposition is
stored, ordinary definition inference may also record its defined parameter
fact, here `{} $in R`, and other consequences of the definition. Those are
consequences of the unsafe assumption, not independently checked discoveries.

`trust` is therefore intentionally very powerful. It still requires parsable
Litex, a known predicate with the correct arity, and argument objects that the
runtime can represent; it is not a way to submit arbitrary malformed syntax.
But it may assume a false equality, place an object outside a proposition's
previously established carrier, and make later statements succeed through the
resulting trusted context. Tightening concrete proposition calls to reject
such a trusted argument would weaken the intended escape hatch, so this
behavior should not be classified as a well-definedness bug.

In documentation and audits, read `trust P` as "assume P from this point onward."
If a later `verification`
trace cites a fact that came from `trust`, that trace explains why the later line
follows from the injected assumption; it does not show that the injected
assumption was proved by Litex.

Likewise, success on a `trust` line only means the assumption was accepted into
the context. It is not a certificate that the injected fact was proved.

This is useful for three narrow purposes:

- introducing background assumptions in a small example;
- marking exact proof debt while translating or experimenting;
- temporarily stating a theorem or library fact that should later become a
  checked `claim`, `thm`, builtin rule, or source-local cite result.

The cost is explicit. If a false statement is introduced with `trust`, later
results can inherit that assumption. Serious Litex developments should keep
remaining `trust` facts visible and treat them as assumptions or proof debt, not
as completed proof. Litex reports this trust boundary, and strict mode rejects
executed user `trust`, `trust have`, and `axiom`, including nested proofs and
imported dependencies. Pure `abstract_prop` signatures and named foundation
releases remain allowed; neither supplies arbitrary user-assumed facts.

## Why does Litex infer extra facts after accepting a line?

Some mathematical facts carry routine consequences. Litex stores those
consequences so the user does not have to restate every projection, membership,
domain fact, or set-builder condition by hand.

For example, after Litex knows a function object and a valid input, it can use
the function's domain and return-set information. After it records certain set
or Cartesian-product facts, it can infer basic membership and projection
facts. Struct membership is intentionally different: a generic
`e $in &Struct` stores no tuple, field, or law consequences. Those facts are
released only by a direct `e &Struct` symbol binding or by an explicit,
membership-checked `release struct def e`.

This is one reason Litex proofs can stay close to ordinary mathematical prose.

For example, `have x R*` followed by `have square R = x^2` records
`square $in R+`. The relevant fact is that a nonzero real square is positive;
the checker does not need to establish that x itself is positive. The power
inference first reuses that existing checked rule. Zero and `i^2` cannot use it.

The user states the meaningful structural fact once, and the checker records
the small consequences that a human reader would normally keep in mind.

For example, `closed_range(0, n) $subset N` follows directly when `n $in N`,
and `{k closed_range(0, n): P(k)}` is finite because it only filters a finite
base. If that filtered set is also proved nonempty, its finite minimum can be
used with the inherited natural-number carrier.

## Why does `obtain` name witnesses explicitly, and can its source be a prop?

An existential fact says that some object exists. A later proof often needs to
choose a name for such an object and use its properties. `obtain ... from
exist` is the Litex form of that ordinary mathematical move.

For example:

```litex
witness exist u R st {u > 0, u < 1} from 1 / 2:
    1 / 2 > 0
    1 / 2 < 1
obtain w from exist v R st {v > 0, v < 1}
w > 0
```

The first block proves an existential fact. The `obtain` line introduces
the witness name `w` for a matching existential statement. After that, the
witness properties are available in the context.

If a named theorem's only direct conclusion is positive `exist` or `exist!`,
use `release thm` (to store the existential) then `obtain` from that exist,
or keep the existential and name witnesses in a `claim` as needed:

> **Migration example:** Current `src/` checking stops at `release_thm` (`release thm …`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
have q Q
release thm rational_has_unique_reduced_fraction(q)
obtain p, d from exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}
```

(`obtain … from thm …` is removed; prefer the two-step form.)

Multiple conclusions, a nonexistential or negated existential
conclusion, and a mismatched number of names are rejected.

A concrete prop can serve as a named wrapper around that existential:

```litex
prop has_copy(a R):
    exist x R st {x = a}

$has_copy(2)
obtain copy from $has_copy(2)
copy = 2
```

The same wrapper can also be the target of `witness`:

```litex
prop divides(p Z, u Z):
    exist k Z st {p = u * k}

witness $divides(6, 2) from 3:
    6 = 2 * 3
```

Here the primary proved fact is `$divides(6, 2)`, not a parser-expanded
existential. At execution time Litex checks that the active definition has
exactly one positive ordinary `exist` clause, instantiates it, and reuses the
ordinary witness checker. Normal definition inference then makes the matching
existential fact available. For unique existence, write the explicit
`witness exist! ...` proof, including its uniqueness obligation, and introduce
the named predicate separately with `by def`.

This is deliberately narrow. Litex first verifies the source prop, then
rechecks its retained definition and substitutes the call arguments. The
definition must contain exactly one clause and that clause must be positive
ordinary `exist`. An `exist!` definition, abstract prop, negated source,
`not exist`, or definition with an extra clause is not accepted by this named
witness form.

The existential statement is a fact; a name introduced by `obtain` denotes
a selected witness together with its checked type and body facts. These are
runtime contracts. Earlier Lean experiments describe how such evidence might
be replayed with `Exists.choose` and `choose_spec`; that backend is not part
of the current build, so this section makes no current Lean replay claim.

## How do function ranges and preimages work?

`fn_range(f)` is the set of values reached by a function `f`. If Litex knows
that a value is in this range, then ordinary mathematics allows us to choose a
preimage. `have by fn_preimage` turns that move into an explicit proof step.

For example:

> **Migration example:** Current `src/` checking stops at `session_error`. This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
sketch:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    have by fn_preimage: x from f(1) $in fn_range(f)

    x $in R
    x > 0
    f(1) = f(x)
```

For multi-argument functions, one preimage name is provided for each function
parameter. This feature is small but important: it makes "since this value is
in the range, take a point mapping to it" a checkable, named move rather than
an implicit jump.

## What is `strategy` for?

`strategy` is for proof patterns where the hard part is not the outer
predicate name, but the internal structure of the object being checked.
Ordinary `forall` matching retrieves a stored conclusion by shape and performs
structural parameter substitution. Supported matching constructors can descend
through nested terms; fixed subterms use existing Direct equality evidence.
It does not search unrelated subexpressions or additional foralls to invent a
substitution. Such proof discovery would be expensive and hard to audit.

This matters for predicates that also serve as practical well-definedness
interfaces. Suppose `f`, `g`, `h`, and `t` are known to have a property such as
being differentiable or integrable, and the library knows that this property is
closed under pointwise addition, subtraction, and multiplication. For a nested
anonymous function such as:

```text
fn(x R) R {f(x) + (g(x) - h(x)) * t(x)}
```

without a strategy, the user may have to introduce the intermediate pieces by
hand: first `g - h`, then `(g - h) * t`, then the final sum with `f`. The proof
is mathematically routine, but the object is syntactically deep.

A `strategy` packages that structural argument as one checked, named universal
proof. The potentially deep reasoning lives in the definition body; after the
definition succeeds, matching non-equality atomics may apply it through the
dedicated known-strategy search route (same match / instantiation mechanics as
known forall, but cited by strategy name). Strategies are not injected into
ordinary known-forall matching.

The shape is:

```text
strategy name:
    ? forall parameters:
        assumptions
        =>:
            $target_predicate(...)
```

After the strategy is defined, Litex can use it when it sees a matching
predicate goal. Its visibility follows the normal environment and
lexical-scope rules. In serious files, a strategy should be backed by a real
checked proof or by clearly marked proof debt, just like any other reusable
universal fact.

## Why can definition folding stay fast in a large context?

For a concrete proposition, ordinary folding and explicit `by def` know the
exact clauses they must prove. Litex therefore checks directly stored argument
carriers and exact cached clauses first. It opens broader proof search only when
that bounded route does not establish a requirement. This is not a shortcut
around the definition: a missing universal or existential clause still makes
the fold fail.

The same bounded-design principle applies to the builtin greatest-member rule.
It proves only the standard maximum-existence shape for a finite nonempty
subset of `N`; dropping finiteness or nonemptiness leaves the goal unknown.


### Why did an inline forall or an old builtin theorem call fail?

`forall x R: x > 0 => x > 0` now parses the premise separately from the arrow.
A `by induc n` inside a theorem selects the existing goal binder `n`; it does
not redeclare it. Nested declarations with the same name are still rejected.
The 25 legacy named builtin theorem calls now have native `release thm`
contracts. Failures identify the theorem, stage and failed premise in JSON.
For example, `subset_of_finite_set_is_finite({2}, {1})` fails at `{2} $subset {1}`.

### How does calculation treat the imaginary unit and empty indices?

Calculation uses the reserved literal `i² = -1`, so `i*i = -1` and
`(1+i)*(1-i) = 2` are checkable without extra rewrite. Symbolic denominator
cancellation still needs nonzero premises. Indexed union, intersection and
Cartesian product require a nonempty index at WD. Naming an empty family
function does not enable an empty-index identity.


### Do enumeration, nested proof methods, and eval check the same boundaries?

Finite enumeration checks each conditional instance, skipping only a proved
false atomic premise and otherwise proving the conclusions under local
premises. Quantified names remain available to nested proof steps. The domain
must be a displayed finite list set or a concrete integer range; `cart(...)`
enumeration is not supported. `by` proof bodies run nested statements through
the same checked, transactional entry as claim/witness bodies, and publish only
the enclosing target. A nested template cannot bypass `-strict` with
`trust have`. `eval` checks source-expression well-definedness before rewriting
or executing an algorithm; a successful computation publishes the checked
`source = result` equality in the current scope. A failed computation or check
publishes no equality.

The runnable [finite-set proof tracer](../examples/stmt_nodes/by/finite_set_conditional_proof_steps.lit)
and [eval domain tracer](../examples/stmt_nodes/command/eval_source_domain.lit)
show these boundaries. False conclusions under true premises and out-of-domain
calls are executable rejection controls in the statement suite.

### Can a proved constant unique-existence source be renamed?

Yes. After proving `forall t R: exist! y R st {y = 0}`,
`have fn f by exist!` may ask for the same statement with `x` and `z`.
The verifier replays the whole proved proposition and checks WD again; it
records its source FactId and bound-name renamings. An unused `t` receives no
arbitrary value. Carriers, premises, uniqueness and free definition owners
must still match. A local `value` cannot replace `Other::facts::value`.

The [constant-source tracer](../examples/stmt_nodes/definition/forall_source_replay.lit)
contains the complete checked proof. Tests also reject an unproved source,
an ordinary `exist` source and a source whose premise was dropped.
The [nested-function source tracer](../examples/proof_nodes/forall/known_exist_nested_function_alpha.lit)
also checks renamed bound variables inside an existential function carrier.
Domains, return carriers, guards and free identities must remain the same.
The [nested unique-source tracer](../examples/proof_nodes/forall/known_source_nested_unique.lit)
also repeats a proved forall with nested universal preconditions and
`exist!` witnesses over a dependent closed range. This is structural
source reuse; it still checks WD at the current permissions and rejects
changing uniqueness, either map condition or a complete input domain.

### Can decimal aliases, complex reciprocals and finite aggregates be checked directly?

Yes. Decimal literals are normalized exactly, so `2.400 = 2.4` succeeds and
`2.400 != 2.4` is rejected. The dedicated builtin proves `i != 0` in either
orientation; guarded complex calculation then checks `1 / i = -i`.
`1 / i = -1` and division by `i - i` are rejected.

The numeric/aggregate correction raised the module-cache compatibility revision
to ABI 3; subsequent interface corrections raised it to ABI 4. Older imported
products rebuild once, because cached theorem interfaces omit their proof body
and must not preserve an earlier incorrect acceptance. The layout stays the
same; standalone numeric decoding also normalizes old spellings.

Finite `sum` and `product` instantiate each index, check the function domain,
and fold exact values. Named functions, nested aggregates, exact fractions and
displayed finite sets use the same calculation path. One evaluation shares a
1024-term allowance across all nested aggregates; integer endpoint arithmetic
is checked. A general finite set needs a known enumeration for numeric eval.
Symbolic constant, linearity, pointwise, partition and shift identities use
their own checked premises rather than enumerate an unknown endpoint. Source
and target interval legality may need explicit hypotheses.

`eval` displays the result and publishes the checked `source = result` equality
in the current scope. Algorithm calls cite their defining equations; a failed
computation or check publishes no result. Later assertions can use its FactId.
Detailed output retains substitutions, each term, running totals and the store
result. See the [eval publication tracer](../examples/stmt_nodes/command/eval_store_result.lit),
[numeric tracer](../examples/proof_nodes/equal/by_builtin_rule/numeric_normalization.lit),
[complex tracer](../examples/proof_nodes/equal/by_builtin_rule/imaginary_division.lit),
[aggregate calculation tracer](../examples/proof_nodes/equal/by_builtin_rule/aggregate_calculation.lit)
and [symbolic identities](../examples/proof_nodes/equal/by_builtin_rule/aggregate_identities.lit).


### Can negative powers, fraction comparisons and periodic trig values be checked directly?

Yes. `2^(-3)=1/8`, `1/3<1/2` and `min(1/3,1/2)=1/3` use exact
calculation. The nonzero-base and denominator requirements remain checked;
zero to a negative power or division by zero rejects. The rational fallback
uses bounded checked integers and refuses overflow rather than approximate.

```litex
have k Z
tan(pi + 2 * k * pi) = 0
sin(pi / 6 + 2 * k * pi) = 1 / 2
C_abs(3 - 4 * i) = 5
C_abs(-4 * i + 3) = 5
```

The period rule checks integer membership; `have k R` alone is insufficient.
Tangent poles and cotangent poles remain undefined. Numeric complex modulus
accepts both summand orders and signs, computes exact coordinates and selects
the nonnegative root. `eval C_abs(1+i)` displays `sqrt(2)` and stores
`C_abs(1+i)=sqrt(2)`. Detailed output records the period's integer evidence or the modulus's
coordinates and squared value. See the [period tracer](../examples/proof_nodes/equal/by_builtin_rule/periodic_trig_exact_values.lit)
and [modulus tracer](../examples/proof_nodes/equal/by_builtin_rule/numeric_complex_modulus.lit).

### Can tangent and cotangent quotient identities verify directly?

These two fixed identities verify with the partial-operation conditions:

```litex
forall x R:
    sin(x)!=0
    cos(x)!=0
    =>:
        tan(x)*cot(x)=1

forall x R:
    cos(x)!=0
    =>:
        1+tan(x)^2=1/cos(x)^2
```

Reversing the equality or the product/sum order is supported; a square may
also be written as repeated multiplication. Removing a nonzero condition,
using a pole or substituting a different angle still rejects. The fixed laws
do not provide a general trigonometric expansion procedure. See the
[product tracer](../examples/proof_nodes/equal/by_builtin_rule/tan_cot_product.lit)
and [square tracer](../examples/proof_nodes/equal/by_builtin_rule/tan_square_reciprocal_cosine.lit).

### Can equivalent written principal bounds be used directly?

The fixed inverse, sine-order and nonzero interval consumers recognize four
literal lower-endpoint forms: `(-pi)/2`, `-(pi/2)`, `0-pi/2` and
`(-1)*(pi/2)`. Both comparison directions are supported:

```litex
forall y R:
    -(pi/2)<=y
    y<=pi/2
    =>:
        arcsin(sin(y))=y
```

The actual condition and its citation remain in the proof. Open intervals
remain open for tangent and cosine nonzero; broader or missing bounds still
reject. See the [acceptance example](../examples/proof_nodes/equal/by_builtin_rule/arcsin_principal_bound_spellings.lit).

### How does a negative multiplier affect inequalities?

A negative common factor reverses strict order. A nonpositive factor, including
zero, reverses weak order. The factor may occur on either side of each product:

```litex
forall a,b,c R:
    0>c
    a>b
    =>:
        c*a<b*c

forall a,b,c R:
    c<=0
    a<=b
    =>:
        a*c>=c*b
```

Both the actual sign proof and reversed argument comparison remain in the
result. Weak/zero premises cannot justify a strict conclusion; missing sign or
argument-order facts still reject. The rules inherit their caller's premise
permissions and do not open definitions or rewrite inside that restricted stage.
The [strict](../examples/proof_nodes/atomic/by_builtin_rule/negative_common_factor_order.lit)
and [weak](../examples/proof_nodes/atomic/by_builtin_rule/nonpositive_common_factor_weak_order.lit)
tracers record the supported archived-overlay gate; current shared startup
compilation remains a separate pending gate.

### Do first-quadrant bounds suffice for tangent and cotangent WD?

Yes. The actual strict bounds certify nonzero sine and cosine before the
partial operators are checked. The fixed positivity rules use the same
written bounds:

```litex
forall x R:
    0<x
    x<pi/2
    =>:
        0<tan(x)

forall x R:
    x>0
    pi/2>x
    =>:
        cot(x)>0
```

Each rule retains both actual bound citations. Closed or missing bounds,
wrong signs and poles still reject. See the
[quadrant tracer](../examples/proof_nodes/atomic/by_builtin_rule/trig_first_quadrant.lit)
and [quotient WD consumer](../examples/proof_nodes/equal/by_builtin_rule/trig_first_quadrant_quotient_wd.lit).

### Why should stored whole numeric values precede their arguments?

When both `a=0` and `cos(a)=1` are available, replacing the argument first can
hide the whole cosine equality. Numeric substitution matches the original
whole term first, then visits its children and checks a rebuilt parent. This
keeps the result independent of the numeric table's row order:

```litex
claim:
    ? forall a,b R:
        a=0
        b=pi
        =>:
            cos(b)<cos(a)
    cos(a)=cos(0)=1
    cos(b)=cos(pi)=-1
    cos(b)<cos(a)
```

The selected equalities are cited, and the rewritten comparison is verified
with the existing rewrite permission consumed. The
[tracer](../examples/proof_nodes/atomic/by_builtin_rewrite/closed_numeric_subterm_priority.lit)
and focused tests also cover equality and `eval` consumers.

### Can rational exponents compute exact rational values?

Yes, for closed positive rational bases when the exact roots exist within
checked `i128` arithmetic:

```litex
8^(1/3)=2
16^(3/4)=8
(1/27)^(-1/3)=3
eval (4/9)^(1/2)
```

These use the central closed calculation and the same exact evaluator used by
`eval`. The reduced exponent `p/q` requires exact `q`-th roots of the reduced
base's numerator and denominator, followed by an integer power. Irrational
results are not rounded: `let u=2^(1/3)` is well-defined, but `eval 2^(1/3)`
declines. This exact evaluator still requires a positive base for noninteger
exponents; the separate WD domain also admits zero with a positive real exponent.
See the [rational-power tracer](../examples/proof_nodes/equal/by_builtin_rule/closed_rational_power_calculation.lit).

### Can a symbolic positive real base have a real exponent?

Yes. Power WD now accepts a positive real base and any real exponent, or a
nonnegative real base and a positive real exponent:

```litex
forall a R+, t R:
    a^t $in R
forall x R:
    exp(x) = e^x
```

Natural powers keep `0^0=1`. Zero to a negative power, negative bases with
noninteger exponents and general complex exponents are rejected. A symbolic
expression being well-defined does not make it exactly calculable or prove
all its identities. See the [power WD tracer](../examples/wd/pow_real_domains.lit).

### Are fraction rounding, numeric radicals, complex parts and rational logs calculations or rules?

Closed expressions use the pure calculation leaf. For example:

```litex
floor(-7 / 3) = -3
sqrt(12) + sqrt(27) = 5 * sqrt(3)
img((1 + 2 * i) / (3 - i)) = 7 / 10
log(8, 4) = 2 / 3
eval log(1 / 3, 27)
```

The same exact arithmetic supplies `eval` results and their published equalities.
Symbolic laws keep their existing premise-bearing builtin rule or strategy.
All input domains are checked before computing. Square roots keep the
nonnegative principal value, and numeric logarithms use exact prime-exponent
ratios. Unsupported radical inversion, factorization exhaustion and arithmetic
overflow decline calculation. No decimal approximation proves an equality.
The four [closed calculation tracers](../examples/test_objs/experience/problem_notes/closed_exact_elementary_calculation_2026-10-03.md)
and their paired executable negatives record these boundaries.

### Why can a strict positive lower bound make a logarithm goal well-defined?

Storing `1 < x` now publishes `0 < x`: the strict source and the closed
proof `0 <= 1` justify that forward consequence. More generally, `b < x`
can use an available `0 <= b` proof at the same restricted inference stage.
The [strict-bound tracer](../examples/infer/atomic/strict_lower_bound_positive.lit)
keeps the original logarithm premise. This does not permit negative or unknown
bounds to imply positivity, and does not widen WD search permissions.

A stored R-returning function can supply `f(a) $in C` at the known-property stage after its application domain has been checked. This is numeric carrier inclusion. The checker requires every candidate stored return signature to fit the target. Function-space membership additionally requires the complete input domain: a function defined on `union(S,{a})` cannot be published as a member of `fn(x S) R`. Construct `have fn restricted(x S) R = f(x)` and use that value for the smaller domain. Freshness remains a premise of finite-product insertion. Native template/field signatures retain their checked producers.


### Which real trigonometric interval facts can be checked directly?

The checker has fixed sign and monotonicity rules for the usual intervals.
The following standalone snippet keeps the tangent denominators explicitly
well-defined and uses the original angle bounds:

```litex
forall x R:
    0<x
    x<pi/2
    =>:
        0<sin(x)
        0<cos(x)

forall a,b R:
    -pi/2<a
    b<pi/2
    a<b
    cos(a)!=0
    cos(b)!=0
    =>:
        tan(a)<tan(b)
```

Cosine reverses order on `[0,pi]`; tangent preserves order on
`(-pi/2,pi/2)`; cotangent reverses order on `(0,pi)`; sine preserves weak as
well as strict order on `[-pi/2,pi/2]`. Fixed endpoint spellings and reversed
conditions cite the actual written facts. The chosen lower bound, upper bound
and argument-order result remain visible in Detailed output. These are bounded
interval checks, and partial-operation WD is checked first. A weak argument
bound does not justify a strict image inequality, and poles remain invalid.
See the [interval examples](../examples/proof_nodes/atomic/by_builtin_rule/trig_interval_monotonicity.lit).
