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
  require an explicit decision before implementation;
- `not legacy parity`: the old compiler also left the capability unsupported.

## Semantic and proof spine

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Native carriers plus independent Litex membership | migrated | Examples 1, 4, and 5; generated output forbids `Litex.Object` and set encodings based on `Set.univ`. |
| Heterogeneous equality and membership transport | migrated | Examples 1 and 6 use `Litex.Same` and exact equality-path `FactId`s. |
| Real order wrappers and registered order rules | migrated | Example 2; exact rule ID and fingerprint are validated before `Litex.Lt.toLe`. |
| Real-representative coherence | decision | `Core.lean` declares `RealCoherence` but intentionally installs no instance. Multiplicative/divisive sign laws compare independently selected zero representatives and cannot be emitted until this boundary is approved or constructively proved. |
| Source order, persistent/local scope, and exact `FactId` replay | migrated | Examples 6, 8, and 9. |
| Verifier-owned WD object/fact graph | partial | Current arithmetic and function tracers consume it; old constructor families below still lack emitters. |
| Known forall instantiation and alpha-equivalent citation | migrated | Example 6 and focused compiler tests. |
| Conjunction, disjunction, cases, and contradiction | partial | Examples 7 and 9 cover the reviewed shapes; wider branch and negation shapes remain fail-closed. |

## Statements and definitions

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Top-level and scoped atomic facts | partial | Equality, standard membership, selected order and strategy facts compile; most atomic predicates still lack adapters. |
| Named theorem, claim, example, and sketch scopes | migrated | Examples 1, 2, 8, and 9. |
| Explicit-value object definitions | partial | Example 11 covers numeric values and one exact membership; rich object values depend on the object rows below. |
| Checked choice from a nonempty set | migrated | Example 14 uses the exact carrier and retained nonemptiness proof. |
| Concrete proposition definitions and `by def` | migrated | Example 13 and the concrete-predicate part of example 14. |
| Bodyless concrete propositions | not legacy parity | The old strict emitter also rejected this shape. |
| Abstract propositions | decision | The old compiler emitted an uninterpreted declaration. The active compiler currently preserves its zero-project-axiom boundary and fails closed. |
| Explicit source `trust` | decision | The old compiler emitted an axiom scoped to the source trust. A new exact and visible trust ABI has not been approved. |
| Positive existential introduction/elimination | partial | Example 10 covers one witness and one body fact; multiple witnesses, uniqueness, and negative existentials remain pending. |
| Transactional incomplete-report output | pending | The active strict emitter fails closed but has not restored the old incomplete-report mode. |

## Functions

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Unary function set and checked application | migrated | Example 4 uses exact function and argument membership evidence. |
| Unary named functions with domain clauses | partial | Example 12 supports real-valued `+`, `-`, `*`, and `/` bodies. |
| Multiple parameters in one application layer | pending | Requires a native-carrier argument telescope; source `f(a,b)` must not become curried application. |
| Multiple source application layers | pending | Source `g(a)(b)` must retain two applicability/result-membership certificates. |
| Dependent parameter requirements and return sets | pending | The old `FnSpec` cannot be copied; a new typed wrapper contract is required. |
| Compound anonymous functions | pending | Identity is the only current anonymous native-carrier value; body WD and result membership need an owner-scoped adapter. |
| Function extensionality | not legacy parity | Neither compiler established an extensional equality interface. |

## Objects and sets

| Capability | Status | Active evidence or remaining boundary |
| --- | --- | --- |
| Numerals and `+`, `-`, `*`, `/` expressions | partial | Native complex expressions, named real-function bodies, real/complex closure for all four operators, and integer `+`/`-`/`*` closure compile; other occurrence contexts remain incomplete. |
| Power, remainder, floor/ceil, elementary and transcendental functions | pending | Structural IR exists for many operators; native terms, membership closure, and proof adapters are missing. |
| Predicate-defined set builders | partial | Example 14 supports whole-side equality and one concrete predicate; nested binder expressions remain rejected. |
| Finite list-set literals | pending | The old compiler emitted proof-free list sets with ordered distinctness evidence; an exact heterogeneous carrier is undecided. |
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
| Additive nonnegative and one-strict sign strategies | migrated | Example 15 covers real-addition closure, left/right strict routes, direct evidence, and registered rule certificates. |
| Multiplicative/divisive sign strategies | decision | IR now retains direct and recursive `Mul*`/`Div*` evidence, but Example 15 keeps `MulNonnegative` fail-closed because the native proof needs the uninhabited `RealCoherence` certificate. |
| Standard-set hierarchy | migrated | Example 16 validates every proper projection through `N → Z → Q → R → C` and composes four proved adjacent native-carrier bridges. |
| Refined numeric membership | pending | Verified `N+ → N` remains an executable compiler negative; refined exact carriers must preserve their sign/nonzero predicates. |
| Integer/complex/real arithmetic membership families | partial | Examples 15 and 17 cover real and complex `+`/`-`/`*`/`/`, plus integer `+`/`-`/`*`; integer remainder/quotient/power/absolute value, rational/natural families, and real power remain pending. |
| Set-relation and set-operator rules | pending | Depend on exact native set constructors and their proved laws. |
| Reflection rules such as prime and coprime | pending | Verifier evidence exists; no active native-carrier compiler theorem family is accepted yet. |
| Remaining registered local rules | pending | Every rule needs its stable ID/fingerprint adapter and a real-Lean tracer; no generic theorem search is allowed. |

## Required migration order

1. Keep the real `+`/`-`/`*`/`/` closure and additive-strategy tracer green;
   decide whether `RealCoherence` is proved, required explicitly, or avoided
   by a revised order wrapper before porting multiplication/division signs.
2. Approve and implement the native-carrier function telescope: multiple
   parameters, exact application layers, dependent requirements, then compound
   anonymous bodies.
3. Use that function ABI to migrate ranges, Cartesian products, tuples,
   sequences, and aggregate objects.
4. Define exact list/set-constructor carriers and only then port their builtin
   theorem families.
5. Port the remaining numeric operators, refined carriers, reflection, and
   registered rules in coherent theorem families.
6. Decide the explicit `trust`/abstract-proposition boundary and restore
   transactional incomplete-report mode without weakening strict compilation.

## Completion evidence

Parity is complete only when every row that is actually legacy parity is
`migrated`, every `decision` row has an explicit approved outcome and matching
tests, and no undocumented old-only source route remains. The final audit must
use the current versions of these gates:

```sh
target/release/litex -compact -strict -runner -f lean/examples/<tracer>.lit
cargo test --release --test litex_to_lean_compiler_tracers
cd lean && ./compiler.sh check examples
cd lean && lake build
```

Generated outputs must contain no retired universal-object ABI, no `sorry` or
`admit`, no compiler-invented axiom, and no source-set encoding based on
`Set.univ`.
