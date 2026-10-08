# Parse surface

What this module accepts: token blocks → AST (`Stmt` / `Fact` / `Obj`).

This is a **parse** reference, not a verifier guide.

- Layers: `parse.rs` (dispatch) → `statements/*` → `fact*.rs` → `object/*` → `param.rs`
- Keywords: `keywords.rs` (no legacy `syntax::keywords` import)
- Exec wiring may lag parse: see `examples/stmt_nodes/README.md`
- Human tutorial: `docs/Manual.md` / `docs/Litex_Learner_Cheatsheet.md`

`Runtime::parse` is a parse-only batch API: success retains the batch's new
bindings; any parse error restores the entire prior scope stack. It does not
execute statements, and ID allocation remains monotonic even on failure.
The source runner instead owns a transaction spanning one top-level block's
parse and `exec_stmt`, then proceeds to the next block. See
[`run/README.md`](../run/README.md#source-string-transaction-order) for why
parse bindings need rollback independently of the execution environment.

Acceptance for cited tracers:

```bash
target/release/litex -f <file.lit>
```

---

## Lexical notes (tokenize)

| Feature | Form |
|---|---|
| Line comment | `# ...` |
| Inline aside | `"..."` on one line (stripped; not in AST) |
| Block comment | line that is exactly `"""` opens/closes |
| Indentation | defines blocks |
| Line continuation | trailing `\\` joins the next physical line |

Unicode aliases (e.g. `∀`→`forall`, `∈`→`$in`, `∪`/`∩`/`×` as infix) are accepted at tokenize/parse time; see Manual “Unicode mathematical input aliases”.

---

## Statement dispatch

First header token chooses the family. Anything else is a **bare fact** statement.

AST nesting: object introductions are
`Stmt::Definition(DefinitionStmt::DefineObj(…))`;
`prop` / `thm` / `have fn` / `struct` / … are flat
`DefinitionStmt` siblings. `release` / `by` / `register` stay top-level.

| First token | AST family | What it does |
|---|---|---|
| *(other)* | `Fact` | Assert one fact; search + store |
| `trust` | `Trust` | Skip truth search; WD still required |
| `let` | `Definition.DefineObj.LetObj` | Untyped equality binding |
| `have` | `Definition.DefineObj` or flat `HaveFn*` / `have by` | Introduce objs / define fns |
| `obtain` | `Definition.DefineObj.Obtain*` | Name exist witnesses |
| `prop` / `abstract_prop` | `Definition.DefProp` / `DefAbstractProp` | Predicate interface |
| `struct` | `Definition.DefStruct` | Product carrier |
| `template` | `Definition.DefTemplate` | Parameterized definition |
| `thm` / `axiom` / `strategy` | `Definition.DefThm` / `Axiom` / `DefStrategy` | Named goal interfaces |
| `release` | `Release` | Unpack thm / struct def / obj def |
| `by` | `By` | Named proof method |
| `register` | `Register` | Register prop rewrite laws (no proof body) |
| `witness` | `Witness` | Exhibit witnesses for exist / nonempty |
| `claim` / `sketch` | `ProofBlock` | Nested local proof scope |
| `eval` | `Command.Eval` | Evaluate an object for display |

Rejected at dispatch (intentional):

| Input | Why |
|---|---|
| top-level `?` | goals live inside claim/thm/by/… |
| `import` | declare deps in `litex.config` |
| `setting` | not supported |
| bare `strong_induc` | only after `by` |
| `have algo for fn …` | removed; use top-level `algo name(…) ret by cases:` / `by induc …:` |
| `have tuple\|cart\|seq\|finite_seq\|matrix` | removed; use `have fn` |

---

## Statements — definitions and introductions

### Bare fact

```text
1 + 1 = 2
```

Tracer: `examples/stmt_nodes/fact/execute_fact.lit`

### `let`

```text
let a = 1
```

Tracer: `…/definition/let_obj.lit`

### `have` (object)

```text
have x R
have x R = 1
have x, y R = 0, 1
have x R:
    x > 0
```

Tracers: `have_obj_equal.lit`, `have_obj_in_nonempty_set.lit`, `have_obj_by_exist_facts.lit`

### `have fn`

```text
have fn id(x R) R = x

have fn nonzero_flag(x R) R by cases:
    case x = 0: 0
    case x != 0: 1

have fn countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: countdown(n - 1)

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}
```

Fn header params must be **object-typed** (`x R`), not `set` / `nonempty_set` / `finite_set`.  
`by exist!` has no signature paren list; the body is exactly one shaped `? forall …: exist! …`.

Function parameter domains and the complete return object are parsed without
the signature's own parameter bindings. The parser collects the names first,
parses all domain carriers in the enclosing scope, registers the bindings only
for `: conditions`, closes that scope for the return object, then reopens the
same binding IDs for the body. This applies to function sets, anonymous values,
`have fn` and `algo`. The derived signature of `have fn ... by exist!` is checked
for the same carrier restriction after parsing its ordinary quantified source.
Ordinary `forall` / `exist` parameter lists retain sequential binding.

`fn(S power_set(R)) fn(x S) R` and `fn(S power_set(R), x S) R`
are parse errors. `fn(x R: x > 0) R {x + 1}` remains valid.
Disjoint binders, as in `fn(x R) fn(x R) R`, have independent IDs.
Tracer: `examples/wd/fixed_function_signature_scopes.lit`.

Tracers: `have_fn_equal.lit`, `have_fn_equal_case_by_case.lit`, `have_fn_by_induc.lit`, `have_fn_by_exist.lit`

### `algo` (preview)

```text
algo nonzero_flag(x R) R by cases:
    case x = 0: 0
    case x != 0: 1

algo countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: countdown(n - 1)
```

Defines the mathematical function with the same strength as `have fn … by
cases` / `by induc`, and stores an executable presentation. Preview `eval`
consumes stored algos for plain-Identifier calls (see `command/eval.lit`).

Tracer: `def_algo.lit`

### `have by`

```text
have by replacement_axiom: Img from prop image_rel, set {1, 2}

have by fn_preimage: source from shift(2) $in fn_range(shift)
```

Tracers: `have_by_replacement_axiom.lit`, `have_by_fn_preimage.lit`

Wrong: `have by preimage` → use `fn_preimage`.

### `obtain`

```text
obtain a from exist x R st {x = 0}
obtain a from exist! x R st {x = 0}
obtain a from $P(…)
```

No indented body. Tracers: `obtain_obj_from_*.lit`

### `prop` / `abstract_prop`

```text
prop above_zero(x R):
    x > 0

abstract_prop F(x, y)
```

`prop` body facts become iff-facts. `abstract_prop` takes bare names only (no types, no body).

Tracer: `def_prop.lit`, `def_abstract_prop.lit`

### `struct`

```text
struct Point:
    x R
    y R
    <=>:
        x = x

struct Pair<A set>:
    left A
    right A
```

Params use `<…>`, not `(…)`. Tracer: `def_struct.lit`

### `template`

```text
template<S set>:
    have carrier_copy set = S

\carrier_copy<R> = R
```

Exactly one body statement among: `have` / `trust have` / `obtain` / `have by replacement_axiom` / `have fn …`.

Tracer: `def_template.lit` (+ obtain / replacement variants)

### `thm` / `axiom` / `strategy`

```text
thm t:
    ? 1 = 1
    # optional proof stmts

axiom a:
    ? forall x R:
        x = x

strategy s:
    ? forall x R:
        x = x
    # proof
```

`axiom` / `strategy` goals are a single `? forall …`. Tracers: `def_thm.lit`,
`axiom.lit`, `def_strategy.lit` (strategy then applies via known_strategy).

### `claim` / `sketch`

```text
claim:
    ? 1 = 1

sketch:
    1 = 1
```

Tracers: `examples/stmt_nodes/proof_block/claim.lit`,
`sketch.lit`.

### `trust`

```text
trust 1 = 1

trust:
    1 = 1
    2 = 2

trust have x R

trust have x R:
    x > 0
```

Tracers: `unsafe/trust_stmt.lit`, `unsafe/trust_have_stmt.lit`

### `witness`

```text
witness exist x R st {x = 0} from 0
witness exist! x R st {x = 0} from 0
witness $is_nonempty_set(S) from e
witness $P(…) from a, b
witness exist u R st {0 < u, u < 1} from 1 / 2:
    0 < 1 / 2
    1 / 2 < 1
```

Optional trailing `:` + indented proof body (full Stmt). Flat header means empty proof.
Tracers: `witness/*.lit`

### `eval`

```text
eval 1 + 1
eval (1 + 2)^2
```

Rewrite via `known_closed_numeric_equal`, then recursively evaluate
(closed-numeric simplify; Identifier FnObj → stored algo). Does not store a
proof fact. Recursive-algo examples deferred.
Tracer: `examples/stmt_nodes/command/eval.lit`

### `release` / `expand`

```text
release thm Name
release thm Name(args…)
release struct def <obj>
release obj def name
release zorn_lemma: set S, prop P, prop U, prop M:
release axiom_of_choice: set F:
release regularity_axiom(S)
expand: e $in range(…)
expand: e $in closed_range(…)
expand: e $in a...b
```

Bare `by thm Name` / `by thm Name(…)` **without** `=>` also parses as release-thm.

Old `by enumerate range` / `by closed_range as cases` / `by zorn_lemma` /
`by axiom_of_choice` / `by regularity_axiom` parse-error with a migrate hint.

Tracers: `definition/release_*.lit`, `release_and_expand/*.lit`

---

## Statements — `by` proof directives

| Form | Sketch | Tracer |
|---|---|---|
| cases | `by cases:` + `? fact` + `case cond:` [proof] [`impossible atomic`] | `by/by_cases.lit` |
| contra | `by contra:` + `? fact` + proof + `impossible atomic` | `by/by_contra.lit` |
| def | `by def <atomic>` or `by def:` + `? <atomic>` (positive only) | `by/by_def.lit` |
| thm | `by thm Call => <atomic>` | `by/by_thm.lit` |
| induc | `by induc n from base:` + goals; optional `? from n = base:` / `? induc:` | `by/by_induc.lit` |
| strong_induc | `by strong_induc n from base:` + `? strong_induc:` | `by/by_strong_induc.lit` |
| extension | `by extension A = B` or `by extension:` + `? A = B` | `by/by_extension.lit` |
| fn_extension | same for function equality | `by/by_fn_extension.lit` |
| enumerate finite_set | `by enumerate finite_set:` + `? forall …` | `by/by_enumerate_finite_set.lit` |
| for | `by for:` + `? forall …` | `by/by_for.lit` |

Finite-set induc forms `by induc S:` / `by induc S in A:` are **removed**.
Range expand / choice / Zorn / regularity live under `release` / `expand` above.
---

## Statements — `register` prop properties

Not proof methods: verify a shaped forall, then tag the prop for rewrite / infer.

| Form | Sketch | Tracer |
|---|---|---|
| reflexive | `register reflexive:` + one shaped `? forall …` (no proof body) | `register/register_reflexive.lit` |
| symmetric | `register symmetric:` + shaped forall (no proof body) | `register/register_symmetric.lit` |
| transitive | `register transitive:` + shaped forall (no proof body) | `register/register_transitive.lit` |

---

## Facts

Top-level:

```text
fact ::= forall | exist | exist! | not … | qf
```

### Atomic / QF

| Shape | Example |
|---|---|
| compare | `1 = 1`, `x > 0`, `a != b` |
| chain (positive) | `1 < 2 < 3` |
| infix `$` | `x $in R`, `A $subset B`, `A $superset B`, `A $proper_subset B` |
| prefix `$` | `$above_zero(1)`, `$is_set(S)`, `$is_finite_set(S)`, `$proper_subset(A,B)` |
| `and` / `or` | `x > 0 and x < 1` / `… or …` |
| `not` atomic | `not x > 0`, `not $P(a)` |

Builtin `$` atoms with dedicated AST:  
`=` `!=` `<` `>` `<=` `>=` `$in` `$subset` `$superset` `$is_set` `$is_nonempty_set` `$is_finite_set`
(and their `not …` forms). Other `$names` → normal atomic (e.g. `$proper_subset`); binary normal atomics may also be written infix (`A $proper_subset B`).

Qualified props: `$Mod::name`, `$Mod:::name`, `$a::b::c` (prefix only, not infix).

### Exist

```text
exist x R st {x = 0}
exist! y B st {$F(x, y)}
exist x, y R st {x = y, x > 0}
```

Body entries are QF (atomic / and / chain / or / leading `not` on arms). Empty `{}` is rejected.

`not exist …` is allowed; **`not exist!` is not**.

Complete facts reject unconsumed header tokens, including nested existential
facts in `forall`, `prop`, and `trust` bodies. For example,
`exist y R st {y = x} and 0 = 1` is rejected, not shortened to its existential
prefix. Prefix parsing is reserved for an enclosing syntax such as
`witness exist ... from ...`.

Tracer: `examples/wd/fact/exist.lit`

### Forall

Then-only (preferred when no domain facts):

```text
forall x R:
    x = x
```

With domain + then:

```text
forall x R:
    x != 0
    =>:
        1 / x = 1 / x
```

With iff:

```text
forall x R:
    x > 0
    =>:
        $above_zero(x)
    <=>:
        $above_zero(x)
```

Inline:

```text
forall x R => x = x
forall x R: x != 0 => 1 / x = 1 / x
```

`not forall` mirrors block forall with QF conclusions (**no** `<=>:`).

Preferred authoring (no empty dom): write then-only `forall x R:` rather than `forall x R:` + bare `=>:`.

Tracer: `examples/wd/fact/forall.lit`

---

## Objects / expressions

Precedence low → high:

```text
->   ∪   ∩   ×   + -   * / %   ...   unary-   ^   postfix . ( ) [ ]
```

### Primaries

| Family | Examples |
|---|---|
| names | `a`, `Mod::name`, `Mod:::name`, `a::b::c` |
| numbers | `2`, `2.5` |
| literals | `i`, `e`, `pi` |
| standard sets | `N` `Z` `Q` `R` `C` `N+` `Z+` `Q+` `R+` `Z-` `Q-` `R-` `Z*` `Q*` `R*` `C*` |
| group / tuple | `(e)`, `(a, b)`, `()`, `tuple(a, b)` |
| list set / builder | `{1, 2}`, `{}`, `{x R: x > 0}` |
| ranges | `a...b`, `closed_range(a, b)`, `range(a, b)` |
| cart | `A × B`, `cart()`, `cart(A)`, `cart(A, B, ...)` |
| unicode / keyword sets | `A ∪ B`, `A ∩ B`; `union` `intersect` `set_minus` `family_union` `family_intersect` `power_set` `index_union` `index_intersect` `index_cart` |
| arith | `+ - * / % ^`, unary `-` (= AST `Neg`), `abs` `floor` `ceil` `sign` `min` `max` |
| int | `gcd` `lcm` `quot` |
| trig / explog | `sin cos tan cot arcsin arccos arctan arccot` ; `sqrt exp ln` ; `log(base, x)` |
| finite | `finite_set_size` `finite_set_max` `finite_set_min` `finite_set_product` |
| seq spaces | `seq(S)`, `finite_seq(S, n)` |
| fn space | `fn(x A) B`, `fn(x A: x > 0) B`, `A -> B` (sugar, right-assoc) |
| anonymous fn | `fn(x R) R {x + 1}` |
| apply / field / bang | `f(a)`, `f(a)(b)`, `obj(i)`, `obj.field`, postfix `n!` (= `factorial(n)`) |
| struct view | `&Point`, `&Pair<R>`, `&Lib::facts::Pair`, `&Lib:::Tagged<R>` |
| template instance | `\Name<args>` (angles required) |
| interval literals | `'[a,b]` `'(a,b)` `'[a,b)` `'(a,b]` ; rays `'(,a]` `'[a,)` … |
| fn_range | `fn_range(f)` |
| preimages | `preimage(f, y)`, `preimage_set(f, Y)` (exactly two operands) |
| factorial | `factorial(n)` and postfix `n!` |

### Keyword primaries that are **not** parse-wired yet

Keywords exist in `keywords.rs` but have no primary arm today (do not document as working surface):  
`re` / `img` / `C_abs`, `sum` / `product` / `reduce` / `finite_set_sum` / `finite_set_product` / `finite_set_reduce` (aggregate family wired).

### Typical object rejects

| Wrong | Right |
|---|---|
| `[1, 2]` list literal | tuple `(1,2)` and ordinary call `obj(i)`; singleton `tuple(1)`; sets `{…}` |
| `&Point{obj}` / `&Name(…)` | `&Point` / `&Name<args>` |
| `struct Name(…)` params | `struct Name<…>:` |

Authoring tip for `-` / `^`: prefer `-(t^2)`, `(-t)^2`, `t^(-1)` over ambiguous `-t^2` / `t^-1`.

---

## Params / binders

| Form | Where | Example |
|---|---|---|
| typed group | forall / exist / have / prop / … | `x R`, `x, y R` |
| type | obj / `set` / `nonempty_set` / `finite_set` | `S set` |
| until `:` / `=>` | forall | |
| until `st` | exist | |
| until `=` / `:` / EOF | have / trust have | |
| `(…)` | prop / fn header | `prop P(x R)` |
| `<…>` | struct params / template | `struct G<S set>:` ; `template<S set>:` |
| `<… : qf, …>` | template with extra facts | |
| bare names | `abstract_prop` only | `abstract_prop F(x, y)` |

`have fn` / `fn(…)` headers: object carriers only.

---

## Typical fact / statement rejects

| Wrong | Right / note |
|---|---|
| `import Foo` | use `litex.config` |
| top-level `? 1 = 1` | put `?` inside claim/thm/by/… |
| `have by preimage: …` | `have by fn_preimage: …` |
| `have fn f(…) Ret:` cases | `have fn f(…) Ret by cases:` |
| `not exist! …` | unsupported |
| `$in` as leading prefix | write `x $in S` |
| `$in` / `$subset` / `$superset` inside compare chains | use separate atomics |
| nested `forall` in then / exist-or-and positions | lift or reshape |
| `by def` on a negative atomic | positive atomics only |
| `obtain` with indented body | flat header only |
| `$fn_eq` / `$fn_eq_in` | removed |

---

## File map

```text
parse.rs           statement dispatch
statements/        Stmt families
fact.rs            Fact + forall/exist/qf
fact_prop.rs       $prop / infix prop names
object/            Obj expression + primary
param.rs           typed parameter lists
keywords.rs        spellings
```

Iron rules (also in `mod.rs`):

1. Plain atoms get `IdentifierId` (see `../identifier_identity.md`): no shadowing; no same-name nested binders.
2. ParseScope maps plain name → id only.
3. Do not store facts or read `ExecEnv` here.
4. Errors: `RuntimeParseError` + path from `TokenBlock`; AST stamps `SourceLine` via live `CodeSource`.

Object-primary builtin spellings cannot be declared as user names, including
parameters, fields and witnesses. The shared binder wrapper rejects them before
allocating an identifier; literal builtin uses and nearby fresh names remain
valid. Struct views use the same full module/export owner resolver as templates.
The configured acceptance fixture is
[`qualified_struct_views`](../../examples/module_manager/qualified_struct_views/README.md);
reserved-binding acceptance is
[`reserved_object_bindings.lit`](../../examples/wd/reserved_object_bindings.lit).

Tuple/cart shape predicates, dimensions, construction projections and postfix object brackets now reject explicitly during parsing. Keyword spellings stay reserved for retirement diagnostics. Ordinary named/returned function calls retain their parameter groups; quoted interval brackets and general indexed-family constructors remain available. The corresponding AST payload deletion and general object head are separately proposed in the tuple/cart plan.
