# Litex Learner Cheatsheet

> A first-contact guide for learning the Litex way of writing mathematics.
> Follow this page from top to bottom once, then keep it beside your editor.
> For the complete language contract, read the [Manual](Manual.md). For
> runnable source files, browse the [examples directory](../examples/README.md).

<!-- Learner spine: object → fact → statement → verifier output → context growth → proof routes → repair → reusable mathematical world. -->

## The one idea to remember

Litex is read from top to bottom. You write the mathematical objects and facts
that should hold. The verifier checks each statement in the current context,
reports the route or the first stopping point, and makes accepted information
available to later statements.

The practical loop is:

```text
identify objects
    → state the next fact
    → choose the statement form
    → run Litex
    → read the output
    → continue from committed context or repair the local stop
```

Keep these four words separate:

| Word | Meaning | Examples |
|---|---|---|
| **Object** | A mathematical value or expression | <code>x</code>, <code>R</code>, <code>{1, 2}</code>, <code>x + 1</code>, <code>fn(t R) R</code> |
| **Fact** | A proposition about objects | <code>x = 2</code>, <code>x $in R</code>, <code>$prime(n)</code> |
| **Statement** | A line or block that introduces, defines, or checks facts | <code>have</code>, a bare fact, <code>prop</code>, <code>claim</code>, <code>thm</code> |
| **Output** | The verifier's evidence, context effects, or stopping point | proof route, stored fact, soft miss (`success: false`), session error |

The most useful authoring question is not “which tactic should I use?” It is:

> What fact should be true next, given the objects and facts already in the
> context?

## 1. First run: check one fact

Install Litex or use the online playground. The smallest useful local run is:

```bash
litex -e '1 + 1 = 2'
```

The command returns Normal JSON. A successful run has a small envelope like this
(fields inside <code>statement_results</code> are shown only as a readable
excerpt):

```json
{
  "kind": "run",
  "success": true,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "1 + 1 = 2",
      "proof_method": { "type": "builtin_rule", "rule_name": "Calculation", "message": "Both sides evaluate to the same number" },
      "stores": ["1 + 1 = 2"],
      "infers": []
    }
  ]
}
```

Read the result in this order:

1. Did the whole run succeed (<code>success</code>) and did each statement succeed
   (<code>success</code>)?
2. Why was it accepted (<code>proof_method</code>)?
3. What was actually added to the context (<code>stores</code>, <code>infers</code>)?
4. If it stopped, what is <code>why_failed.phase</code> and <code>why_failed.goal</code>?
   Soft misses stay inside <code>statement_results</code>; only
   <code>session_error</code> is a hard stop.

The output is part of the working method, not an after-the-fact log. It tells
you what the next legal/useful statement can build on.

## 2. A fact grows the context

The simplest useful file is a sequence of statements:

```litex
have x R = 2

x + 1 = 3
x^2 = 4
```

Read the first line as one statement with two effects: it introduces the object
<code>x</code>, records its carrier <code>x $in R</code>, and records the value fact
<code>x = 2</code>. The next two lines are ordinary fact statements. They are
checked from the current context and become available after they succeed.

Names may depend on earlier names. Write an equality chain to expose the
definition and the calculation:

```litex
have x R = 2
have y R = x + 1

y = x + 1 = 3
y^2 = 9
x + y = 5
```

After both adjacent equalities pass, the chain also stores `y = 3`.
The next two facts can use that endpoint without a separate `y = 3` statement.

This is Litex's default bottom-up direction: establish a useful fact, keep it,
and use the stronger context to establish the next fact. You may still write a
local proof block when a result needs several steps; the surrounding source
remains a readable sequence of mathematical facts.

## 3. Choosing the right object statement

Use the smallest statement that gives later code the interface it needs.

| Later code needs | Write | What it contributes |
|---|---|---|
| An arbitrary object in a nonempty set | <code>have x S</code> | A name and the fact <code>x $in S</code> |
| A named object with a known value | <code>have x S = value</code> | A typed object, its carrier, and <code>x = value</code> |
| A transparent local abbreviation | <code>let name = value</code> | A name that reduces to an already well-defined value |
| A callable value | <code>have fn f(x S) T = body</code> | A function and its domain/return contract |
| A concrete reusable property | <code>prop P(x S): ...</code> | A definition usable through <code>by def $P(...)</code> |
| A short local derivation | <code>claim:</code> with <code>? goal</code> | One fact proved in a local proof context |
| A reusable mathematical result | <code>thm name: ...</code> | A named theorem and a stored universal fact |
| An explicit assumption | <code>trust fact</code> | Trust debt, not a completed proof |

Examples:

```litex
have x R
x $in R

have a R = 1
a $in R
a = 1

have fn shift(t R) R = t + 1
shift(2) = 3
```

Use <code>let</code> when the name is only a local abbreviation:

> **Migration example:** Current `src/` checking stops at `search_proof` (`successor(2) = 3`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
have fn shift(t R) R = t + 1
let successor = shift

successor(2) = 3
fn_range(successor) = fn_range(shift)
```

Do not use a predicate to encode a value that later code must call. If later
code writes <code>f(x)</code>, introduce a <code>have fn</code> interface. If later
code must assert <code>$P(x)</code>, introduce a <code>prop</code>.

## 4. Writing fact shapes

Start with the mathematical shape, then use the corresponding Litex spelling.

| Mathematical shape | Common spelling |
|---|---|
| Equality or membership | <code>a = b</code>, <code>a $in A</code> |
| Named predicate | <code>$P(a)</code> |
| Equality/order chain | <code>a &lt;= b = c &lt; d</code> |
| Conjunction | <code>atomic and atomic</code> |
| Disjunction | <code>branch or branch</code> |
| Existence | <code>exist x S st {facts}</code> |
| Unique existence | <code>exist! x S st {facts}</code> |
| Universal fact | <code>forall x S:</code> with indented assumptions and <code>=&gt;:</code> conclusions |
| Negated quantifier | <code>not exist ...</code>, <code>not forall ...</code> |

<code>and</code> is a flat conjunction of facts. <code>or</code> joins completed
branches. These are not a general recursively nested Boolean language. Keep
quantified parameters in one <code>forall</code> header:

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

Do not put a second <code>forall</code> inside the conclusion when it can be
declared in the header as <code>forall x, y R</code>.

Parenthesize negative powers so the intended syntax tree is visible. The
following block is notation guidance, not a complete fact to run by itself:

<!-- litex:skip-test -->
```litex
have t R = 2

-(t^2) = -4     # opposite of the square
(-t)^2 = 4      # square of the negative value
2^(-1)           # a negative exponent
```

The canonical forms are <code>-(t^2)</code>, <code>(-t)^2</code>, and
<code>t^(-1)</code>. Do not rely on a reader remembering parser precedence.

## 5. Definitions create vocabulary

### Functions

Function definitions state the domain, return set, and expression:

Parameter domains and the return set use the enclosing scope and cannot refer
to that function's own parameters. Domain conditions and the body can:
<code>fn(x R: x > 0) R {x + 1}</code> is valid, while
<code>fn(x R) {x}</code> and <code>fn(S power_set(R), x S) R</code> are rejected
during parsing. Put a more precise output membership property in a separate
fact. Ordinary quantified parameter dependencies remain available.

```litex
have fn square_plus_one(t R) R = t^2 + 1

square_plus_one(3) = 10
square_plus_one(0) = 1

forall x R:
    square_plus_one(x) = x^2 + 1
```

### Concrete properties

Explicit <code>by def</code> must unfold a supported concrete or builtin
predicate definition; its clauses may use ordinary verification. A true raw
comparison or SetBuilder membership is checked by writing the fact directly.

A <code>prop</code> gives a mathematical property a name. Use <code>by def</code>
when you want to fold the definition at a concrete argument:

```litex
prop is_unit_distance_from_two(t R):
    abs(t - 2) = 1

by def $is_unit_distance_from_two(3)
```

<code>prop</code> defines the shape of <code>$P(...)</code>; it does not introduce a
value or a callable function. <code>abstract_prop</code> is an external interface:
it supplies no defining facts and therefore needs assumptions or theorems before
an instance can be used.

### Sets and membership

Litex has one mathematical object universe. Number sets, functions, tuples,
and user-defined sets are objects; membership is a fact about an object:

```litex
0 $in N
1 $in R
1 $in {1, 2, 3}
{1, 2} $subset {1, 2, 3}
```

The standard sets are <code>N</code>, <code>Z</code>, <code>Q</code>, <code>R</code>,
and <code>C</code>, with common subsets such as <code>N+</code>, <code>R-</code>,
and <code>C*</code>. A set builder is bounded by an existing set:

> **Migration example:** Current `src/` checking stops at `release_thm` (`release thm …`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
release thm set_builder_member(1, {x R: x > 0})
```

The carrier is part of the proof obligation. Before using a compound object,
make sure its domain, index bounds, and denominator conditions are known.

## 6. Small proofs: write the route only when needed

Try the target directly. Use a proof action when the target's shape needs one
explicit construction or control structure.

| Goal shape | First route | Mental model |
|---|---|---|
| Direct arithmetic, equality, membership, or known consequence | State the fact | Let the verifier match the current context |
| Concrete positive definition | <code>by def $P(args)</code> | Fold a named definition |
| A named ordinary theorem fact | <code>release thm name</code> | Cite its stored fact |
| A universal theorem | <code>release thm name(args)</code> | Instantiate its parameters |
| One theorem consequence | <code>by thm name(args) =&gt; fact</code> | Select only the needed result |
| Existential target | <code>witness ... from ...</code> | Supply the witness and prove its body |
| Known existential | <code>obtain ... from ...</code> | Open its witness in a local context |
| Exhaustive alternatives | <code>by cases</code> | Prove every available branch |
| Contradiction-shaped goal | <code>by contra</code> | Assume the opposite and finish with <code>impossible</code> |
| Bounded finite/universal goal | <code>by for</code> or <code>by enumerate ...</code> | Iterate a displayed finite set or concrete integer range; <code>cart(...)</code> is unsupported |
| Inductive invariant | <code>by induc</code> or <code>by strong_induc</code> | Give base and step cases |
| Set equality | <code>by extension</code> | Prove both membership directions |

`by contra` accepts existing classified opposites for atomic facts,
`exist` / `not exist` / `exist!`, `and` / `or` / chains, and `forall`,
`not forall` or forall-iff with quantifier-free bodies and premises.
Its `impossible` tail accepts those same Fact families, including multiline
forall/iff facts; both the complete fact and its classified opposite must
verify in the local scope.

Conditional enumeration uses its premises in each local assignment. Nested
proof methods and binder names are allowed in proof bodies; helpers stay local.
`eval expr` checks the expression's mathematical domains before computing.
A successful exact evaluation stores `expr = result` in the current scope;
Normal JSON lists this equality in `stores`. For example:

```litex
algo flag(x R) N by cases:
    case x = 0: 0
    case x != 0: 1
eval sum(0, 3, flag)
sum(0, 3, flag) = 3
```

Each executed algorithm equation is checked before publication. An invalid
expression or exhausted computation budget stores no result equality.
Strict mode rejects `trust have` inside templates as well as ordinary trust.

Templates publish their body definition facts under their parameters and
conditions. Instance properties can be used directly:

```litex
template<S nonempty_set>:
    have member S
\member<R> $in R
```

This uses the stored `forall S nonempty_set: \member<S> $in S`. A conditional
header or function case keeps its premises; selection does not assert uniqueness.

### Local claims

Use <code>claim</code> when a few local facts make one result clear:

```litex
claim:
    ? forall x R:
        x = 2
        =>:
            (x + 1)^2 = 9
    x + 1 = 3
    (x + 1)^2 = 9
```

The <code>?</code> line is the target. The indented lines below it are the local
proof spine. Once the claim succeeds, the target fact is available outside the
block.

### Witnesses and obtain

An existential proof gives its witness explicitly:

```litex
witness exist x R st {x^2 = 4} from 2:
    2^2 = 4

obtain root from exist x R st {x^2 = 4}
root $in R
root^2 = 4
```

The source existential must already be known before <code>obtain</code> can open it.

### Theorem reuse

Name a result when it has a real second consumer:

```litex
thm add_zero_right:
    ? forall x R:
        x + 0 = x
    x + 0 = x

release thm add_zero_right(2)
2 + 0 = 2
```

Root-<code>forall</code> theorem calls require parentheses. A named ordinary
theorem fact uses its bare name. Do not repeat an identical theorem result as an
extra echo.

### A short induction example

Induction is explicit when the invariant is not a direct builtin fact:

The target's WD may use the integer lower bound. Local proof actions such as
`have`, `let`, and `by def` are checked separately in the base and step scopes:

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
    n $in N
    have a N = 0
```

The base has no induction hypothesis; its local objects do not escape.

> **Migration example:** Current `src/` checking stops at `internal_bug: name n is already bound in an enclosing parse scope`. This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
claim:
    ? forall n N:
        2 ^ n >= n + 1
    by induc n from 0:
        ? 2 ^ n >= n + 1
        2^0 = 1 >= 0 + 1

        forall m Z:
            m >= 0
            2^m >= m + 1
            =>:
                2^m * 2^1 >= (m+1) * 2
                2 ^ (m + 1) = 2 ^ m * 2^1 >= (m+1) * 2 = (m + 1) + (m + 1) >= m + 1 + 1
```

Keep induction in a claim or theorem. A bare universal fact is for stating a
conclusion; proof-control commands belong in a proof block.

## 7. One complete mathematical thread

This small divisibility development shows how a definition, witnesses, a
reusable theorem, and ordinary fact reuse fit together:

```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divisibility_is_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)

witness $divides_by(3, 12) from 4:
    12 = 3 * 4
witness $divides_by(12, 60) from 5:
    60 = 12 * 5
by thm divisibility_is_transitive(3, 12, 60) => $divides_by(3, 60)
```

The source writes the mathematical facts: divisibility is an existential,
transitivity multiplies its witnesses, and the concrete instances have
witnesses <code>4</code> and <code>5</code>. The verifier checks each local
connection and stores the accepted facts. The theorem call is an explicit
citation because the author wants to select that reusable interface.

## 8. Read output as a repair interface

When a statement stops, classify the earliest phase before changing the
mathematics.

| Output/phase | Meaning | Next move |
|---|---|---|
| Parse / CLI hard error | The source or command is not accepted | Fix indentation, delimiters, binders, or the command line |
| Name/type problem | An identifier, arity, callable interface, or carrier is wrong | Check spelling, imports, argument count, and exact domain |
| Well-definedness soft miss | An object is not legal yet | Prove membership, bounds, nonzero divisors, or a typed construction |
| Search soft miss | The fact is meaningful but current evidence is insufficient | Add the smallest equality, membership fact, theorem call, or witness |
| Later use fails | The earlier statement stored a different interface than expected | Inspect <code>stores</code>/<code>infers</code>; distinguish an object, fact, predicate, and function |
| <code>trust</code> or <code>axiom</code> appears | The route includes an explicit assumption | Mark the assumption; strict mode rejects executed <code>trust</code>, <code>trust have</code>, and user <code>axiom</code> |

A soft miss is not a proof that the proposition is false:

<!-- litex:skip-test -->
```litex
have x R
x = 0
```

The context only says that <code>x</code> is real. It does not say which real
number <code>x</code> is, so <code>x = 0</code> normally soft-fails with
<code>why_failed.phase: search_proof</code>.

For a run containing a soft-failed statement, top-level <code>success</code> is
<code>false</code>, but the failed statement remains in
<code>statement_results</code> with <code>success: false</code>. Read
<code>why_failed</code> rather than treating the envelope alone as the
mathematical explanation.

### Three high-value repair patterns

**Carrier first.** If an application is not well-defined, establish the exact
argument carrier before unfolding it:

```litex
have fn p_affine(x R) R = 2 * x - 5

forall y R:
    (y + 5) / 2 $in R
    p_affine((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 = y
```

**Inside out.** If one compound equality soft-fails, expose the smallest
changed subterm, then lift it through the outer expression:

```litex
have fn f_add3(x R) R = x + 3
have fn g_times2(y R) R = 2 * y
have fn composite(x R) R = g_times2(f_add3(x))

claim:
    ? forall x R:
        composite(x) = 2 * x + 6
    f_add3(x) = x + 3
    g_times2(f_add3(x)) = 2 * f_add3(x)
    composite(x) = g_times2(f_add3(x)) = 2 * f_add3(x) = 2 * (x + 3) = 2 * x + 6
```

**Phase first.** If the parser rejects the proof surface, repair the statement
shape before changing the mathematical argument. A current proof surface is:

```litex
claim:
    ? forall x R:
        x = 2
        =>:
            (x + 1)^2 = 9
    x + 1 = 3
    (x + 1)^2 = 9
```

Do not keep a bridge fact merely because it makes the proof look safer. Delete
one class of echoes at a time and restore only the first bridge whose removal
causes the real consumer to fail.

## 9. Sets, functions, and structures

### Functions and images

```litex
have fn shift(x R) R = x + 1

shift(2) $in fn_range(shift)
by def fn_range(shift) $subset R
```

When later code must call a value, keep its function interface visible. A
set-shaped value that happens to have an implementation is not automatically a
callable function.

### Finite domains and cases

Finite enumeration is bounded, not arbitrary quantifier automation:

```litex
have x Z
trust x $in range(1, 3)
expand: x $in range(1, 3)
# stores: x = 1 or x = 2
```

Use <code>by cases</code> when an exhaustive disjunction is already available:

```litex
by cases:
    ? 1 = 1
    case 1 = 1
    case 1 != 1:
        impossible 1 = 1
```

### Structures

A <code>struct</code> creates a reusable carrier and field vocabulary:

> **Migration example:** Current `src/` checking stops at `release_thm` (`release thm …`). This retained block is not a verified result.

<!-- litex:skip-test -->
```litex
struct Point:
    x R
    y R

release thm struct_member((1, 2), &Point)
have p &Point = (1, 2)
p.x = p[1]
p.x = 1
p.y = 2
```

Direct symbols introduced in a struct carrier can open one definition-owned
layer automatically. A later generic membership fact does not select field
names; use <code>release struct def</code> or the explicit struct theorem when that
interface is needed.

### A reusable domain interface

Structures and templates let a project build a small mathematical world:

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one
```

The structure is a vocabulary and a law interface. It is not a claim that every
later theorem is automatic; later facts still need to match the declared fields
and laws.

## 10. Run, inspect, and promote

### Useful commands

```bash
# One expression
litex -e '1 + 1 = 2'

# One file; project mode when its direct parent has litex.config
litex -f path/to/file.lit

# Full configured project, including its exports
litex -r path/to/project

# Reject explicit trust during a complete audit
litex -strict -r path/to/project

# After a successful file run, keep the Runtime and continue in the REPL
litex -session -f path/to/file.lit
```

Batch commands (`-e` / `-f` / `-r`) return one Normal JSON document. The REPL
prints short status lines. For automation, inspect top-level <code>success</code>,
each statement's <code>success</code>, and <code>session_error</code>; do not
infer success from nested evidence text alone.

### A practical authoring checklist

Before each new line or block, ask:

- Which objects does this statement use or introduce?
- What exact fact should hold between them?
- Is this a bare fact, an object definition, a predicate, a local claim, or a
  reusable theorem?
- Can the target be stated directly before I choose a proof action?
- After running it, what did the output prove, store, infer, or reject?
- If it stopped, is the earliest problem parse, name/type, well-definedness, or
  verification?
- Am I adding a real mathematical bridge, or only copying the endpoint as an
  echo?

### Trust and scope

Litex is an experimental language in beta. A successful check is relative to
the checker, its builtin and inference rules, imported facts, and any explicit
trusted inputs. <code>trust</code>, <code>trust have</code>, and <code>axiom</code>
are visible assumptions. Strict mode rejects executed <code>trust</code>,
<code>trust have</code>, and user <code>axiom</code>, including nested proofs
and dependencies. Pure <code>abstract_prop</code> signatures and named
foundation releases remain allowed. Strict imports re-execute source exports
instead of replaying cached environments. The current Cargo build has no Lean compiler entrypoint; see
the [CLI boundary](cli.md#lean-compiler-boundary).

### Where to go next

- Read the [Manual](Manual.md) for exact syntax, well-definedness, proof
  boundaries, output contracts, inference, modules, and compiler coverage.
- Prefer the phase acceptance tree under [examples/](../examples/)
  (`proof_nodes/`, `stmt_nodes/`, `wd/`, `module_manager/`, …).

For new code, write `release thm name(args)` whenever the call has no `=>`
selection. Bare `by thm name(args)` remains accepted for source compatibility;
the recommended spelling is `release thm`.

The learner's central habit is simple: write the next mathematical fact, read
the verifier's evidence, and let only accepted context drive the next line.


### Native named builtins and complex calculation

```litex
forall x R: x > 0 => x > 0
release thm set_builder_member(1, {x R: x > 0})
release thm subset_of_finite_set_is_finite({1}, {1, 2})
i * i = -1
(1 + i) * (1 - i) = 2
```

`release thm` checks premises before storing conclusions. `by thm NAME(args)
=> FACT` selects one atomic consequence; compound and chain targets are
rejected. Existential conclusions use `release thm`. Indexed operators require
a nonempty index, including named families.
