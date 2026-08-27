# Legacy Compiler Capability Parity

This ledger tracks source-level capabilities that existed in the archived
universal-object Litex-to-Lean compiler and their status in the active native-
carrier compiler. Parity means that the same verified Litex behavior has a
reviewed representation in the ABI defined by `Litex/Core.lean`, an exact
verifier-evidence adapter, a generated `.lit`/`.lean` pair, and a real Lean
kernel gate. It never means copying the retired `Litex.Object` representation.

The initial inventory was compared with
`../tmp/compile_to_lean_legacy/STATUS.md` and the executable sources under
`../tmp/compile_to_lean_legacy/` on 2026-08-18. The archive is evidence of old
coverage, not a design authority.

Status meanings:

- `migrated`: the active numbered examples and focused tests cover the route;
- `partial`: a representative subset is active, but an old supported shape is
  still missing;
- `pending`: the old source capability has no active native-carrier adapter;
- `decision`: source behavior is known, but its new trust or ABI semantics
  require an explicit decision before implementation. There are currently no
  rows in this state: the outstanding semantic choices have been approved;
- `not legacy parity`: the old compiler also left the capability unsupported.

Current snapshot (2026-08-19): **25 migrated, 8 partial, 10 pending,
0 decision, and 3 not-legacy-parity** rows. Thus 18 actual archived
capabilities still need implementation work. They fall into five remaining batches:

1. remaining named-function carriers and operators (1 row);
2. wider atomic-statement and object-definition shapes (2 rows);
3. WD-backed set and collection constructors (8 rows);
4. remaining numeric objects and refined carriers (4 rows); and
5. set, reflection, and typed rule adapters (3 rows).

## Semantic and proof spine

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Native carriers plus independent Litex membership | migrated | Examples 1, 4, and 5; generated output forbids `Litex.Object` and set encodings based on `Set.univ`. |
| Heterogeneous equality and membership transport | migrated | Examples 1 and 6 use `Litex.Same` and exact equality-path `FactId`s. |
| Real order wrappers and typed catalog rules | migrated | Example 2; the exact Rust rule variant and ordered subgoals are validated before `Litex.Lt.toLe`. |
| Generic two-ended order normalization | verifier-only | The verifier records stable `OrderTransitivity` evidence, but this non-catalog rule now fails closed in ToLean until it receives a separately reviewed mapping. |
| Source order, persistent/local scope, and exact `FactId` replay | migrated | Examples 6, 8, and 9. |
| Verifier-owned WD object/fact graph | partial | Current arithmetic and function tracers consume it; old constructor families below still lack emitters. |
| Known forall instantiation and alpha-equivalent citation | migrated | Example 6 and focused compiler tests. |
| Conjunction, disjunction, cases, and contradiction | migrated | Examples 7 and 9 cover conjunction/disjunction, structured conjunction assumptions, direct contradiction, classical double-negation introduction for a negated order goal, nested case/contra scopes, and branch-local function-application WD. A checked reduction of two identical applications is normalized to the exact reflexivity adapter instead of being rejected as a non-alpha reduction. |

## Statements and definitions

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Top-level and scoped atomic facts | partial | Equality, standard membership, selected order and strategy facts compile; most atomic predicates still lack adapters. |
| Named theorem, claim, example, and sketch scopes | migrated | Examples 1, 2, 8, and 9. |
| Explicit-value object definitions | partial | Example 11 covers numeric values and one exact membership; rich object values depend on the object rows below. |
| Checked choice from a nonempty set | migrated | Example 14 uses the exact carrier and retained nonemptiness proof. |
| Concrete proposition definitions and `by def` | migrated | Example 13 and the concrete-predicate part of example 14. |
| Bodyless concrete propositions | not legacy parity | The old strict emitter also rejected this shape. |
| Abstract propositions | migrated | Example 25 emits one source-scoped, independently universe-polymorphic Lean predicate `axiom` with the exact declared arity. The interface proves no application; the untrusted `$unproved(1)` boundary is rejected by Litex. |
| Explicit source `trust` | migrated | Example 25 requires the distinct `Trusted` IR marker, emits one visible `axiom` for the exact trusted source FactId, and emits later citation and inferred facts only as theorems. Focused audits prove the file has exactly the two source-requested axioms, an ordinary checked file has none, and `Core.lean` remains axiom-free. Litex `-strict` deliberately rejects the explicit unsafe source tracer. |
| Positive existential introduction/elimination | migrated | Example 10 covers the archived emitter's complete supported shape: one positive witness, one singleton parameter group, one body fact, and checked elimination by choice/projection. The archived implementation explicitly rejected multiple witnesses and did not implement uniqueness or negative existential emission, so those are not parity debt. |
| Transactional incomplete-report output | migrated | `compile_source_with_report` returns `Complete` only after whole-file emission succeeds. A verified IR emission gap returns one `Incomplete` report and a diagnostic-only Lean artifact with no partial theorem or axiom; verifier/IR failures remain hard errors. Existing file-output preservation stays covered by the CLI regression. |

## Functions

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Unary function set and checked application | migrated | Example 4 uses exact function and argument membership evidence. |
| Unary named functions with domain clauses | partial | Example 12 supports real-valued `+`, `-`, `*`, and `/` bodies; Example 23 extends the same construction route to one multi-parameter source layer. Other carriers and operators remain open. |
| Multiple parameters in one application layer | migrated | Example 23 uses `FnTelescope.parameter` nodes for every retained parameter, an optional ordered `requirement` node, and one `done` codomain. Both quantified and named `f(a,b)` consume the whole layer; generated named values use `@f` so Lean cannot silently insert an implicit carrier and curry the source layer. |
| Multiple source application layers | migrated | Example 23 follows the exact verifier `FunctionPrefix` DAG for `g(a)(b)`, binds every intermediate exact function carrier once, and separately consumes each layer's argument/domain evidence; the focused Rust regression also covers three layers. |
| Dependent parameter requirements and return sets | migrated | Example 24 renders parameter and return sets in the progressively extended `FnTelescope` context. A later set consumes the earlier argument plus its exact membership proof, and application returns the argument-indexed subtype carrier. |
| Compound anonymous functions | migrated | Example 24 selects the exact parser occurrence, owned binder scope, parameter-membership premise, body-membership closure, and direct-application `FunctionHead` WD child. The generated `R -> R` value replays a typed `x + 1 $in R` proof and is accepted by Lean; a body not verified in its declared return carrier remains rejected. |
| Function extensionality | not legacy parity | Neither compiler established an extensional equality interface. |

## Objects and sets

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Numerals and `+`, `-`, `*`, `/` expressions | partial | Native complex expressions, named real-function bodies, real/complex closure for all four operators, and integer `+`/`-`/`*` closure compile; other occurrence contexts remain incomplete. |
| Native constants and base memberships | migrated | Example 19 lowers `i`, `e`, and `pi` to native Mathlib terms, proves `i $in C` and `e, pi $in R`, and reaches `C` from the exact real-membership FactIds. Refined `R+` remains tracked separately. |
| Power, remainder, floor/ceil, elementary and transcendental functions | pending | Structural IR exists for many operators; native terms, membership closure, and proof adapters are missing. |
| Predicate-defined set builders | partial | Example 14 supports whole-side equality and one concrete predicate; nested binder expressions remain rejected. |
| Finite list-set literals | pending | The approved carrier direction is an indexed finite coproduct retaining ordered distinctness evidence; its Core definition, WD adapter, and generated tracer are not implemented. |
| Union, intersection, set difference, big union/intersection, power set | pending | Exact carriers, semantic laws, and universe behavior must be defined before builtin adapters. |
| Integer ranges | pending | Half-open and closed range IR is retained but has no native-carrier emitter. |
| General Cartesian products | pending | Depends on the generalized function ABI and exact family carriers. |
| Tuple and sequence literals/carriers/indexing | pending | Structural IR exists; exact carriers and checked projection/index recipes are missing. |
| Indexed and finite-set sum/product/reduce | pending | Depends on generalized functions, range/finite-set carriers, and owner-scoped WD replay. |
| Replacement | not legacy parity | The old design marked it decided but did not emit it. |

## Builtin and registered rules

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Reflexivity, rational normalization, standard numeral membership | migrated | Examples 3 and 5. |
| Not-equality symmetry and exact equality paths | migrated | Example 6. |
| Additive nonnegative and one-strict sign strategies | migrated | Example 15 covers real-addition closure, left/right strict routes, and typed rule evidence. |
| Multiplicative/divisive sign strategies | migrated | Example 15 replays typed `MulNonnegative`, `MulPositive`, `DivNonnegative`, and `DivPositive` certificates through canonical zero-ended order and proved Mathlib adapters. |
| Standard-set hierarchy | migrated | Example 16 validates every proper projection through `N → Z → Q → R → C` and composes four proved adjacent native-carrier bridges. |
| Refined numeric membership | partial | Examples 20–22 give exact `N+`, `R+`, `Z*`, `Q*`, `R*`, and `C*` carriers. The star family compiles construction from base membership plus source `!= 0`, base/supercarrier projection, `Z* → Q* → R* → C*` widening, and membership-to-`!= 0` elimination by retaining the semantic nonzero certificate in a complex-source subtype. Generic `R + positivity → R+`, `Q+`, negative carriers, closed `!=` reflection, and star arithmetic remain fail-closed. |
| Base numeric arithmetic membership families | partial | Examples 15, 17, and 18 cover real/complex/rational `+`/`-`/`*`/`/`, integer `+`/`-`/`*`, and natural `+`/`*`. Integer remainder/quotient/power/absolute value, rational power/absolute value/quotient, natural subtraction/power, and real power remain pending. |
| Set-relation and set-operator rules | pending | Depend on exact native set constructors and their proved laws. |
| Reflection rules such as prime and coprime | pending | Verifier evidence exists; no active native-carrier compiler theorem family is accepted yet. |
| Remaining verifier-only typed rules | pending | Every non-catalog rule needs a separately reviewed Rust mapping and a real-Lean tracer; no generic theorem search is allowed. |

## Required migration order

1. Generalize named-function construction beyond the current real arithmetic
   body family while retaining the exact source telescope and return closure.
2. Add the approved exact source-axiom adapters for `abstract_prop` and
   explicit `trust`, then restore wider statement shapes and transactional
   incomplete-report output without allowing implicit axioms.
3. Use the function ABI to migrate ranges, Cartesian products, tuples,
   sequences, and aggregate objects.
4. Define exact list/set-constructor carriers and only then port their builtin
   theorem families.
5. Port the remaining numeric operators, refined carriers, reflection, and
   registered rules in coherent theorem families.

## Completion evidence

Parity is complete only when every row that is actually legacy parity is
`migrated`, every approved semantic decision has matching implementation and
tests, and no undocumented old-only source route remains. The final audit must
use the current versions of these gates:

```sh
target/release/litex -compact -strict -runner -f lean/examples/<tracer>.lit
cargo test --release --test stmt_result_to_lean_compiler_tracers
cd lean && ./stmt_result_to_lean_compiler.sh check examples
cd lean && lake build
```

Generated outputs must contain no retired universal-object ABI, no `sorry` or
`admit`, no compiler-invented axiom, and no source-set encoding based on
`Set.univ`.
