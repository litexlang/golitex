# Phase 1: common native mathematical operations

Date: 2026-10-18. Status: first scalar/set increment implemented and verified; remaining relationships stay on the roadmap.

## Current implementation scope

The user approved the Obj additions, then explicitly deferred function composition and restriction. The delivered increment adds the ten scalar/set objects below, using the proposed independent `HyperbolicOperator` family. No existing AST payload fields or Env/Runtime state contracts changed.

Later on 2026-10-18, the user removed native restriction from scope and requested composition design, including `f ∘ g`. The [current composition proposal](litex-function-composition.md) supersedes the earlier unary-only P5 design: `compose(f,g)` means `f(g(...))`, with unary outer function and fixed positive-arity inner function, including guards. The first composition delivery is implemented with 17 focused tests and 10 strict CLI files passing (see its validation record for the pre-existing static-check failure); restriction uses existing anonymous functions and is no longer a native-operation milestone.

Implemented: native parsing, reserved names, display/IR, recursive substitution and congruence, typed WD evidence, result carriers, LaTeX, defining equations and the focused law groups documented in [Native elementary operations](../docs/native-elementary-operators.md). Conjugation and hyperbolic anchors use exact arithmetic. Symmetric difference supports XOR membership/nonmembership and exact rational-list enumeration. Lean replay fails closed.

Remaining from the complete proposal: conjugate fixed-point/zero reflection; hyperbolic general sign, range and monotonicity laws; tanh addition; symmetric-difference subset/disjointness/finite-cardinality laws; the later preimage and mapping-property laws from P5 composition. These are not claimed implemented by adding the objects. The former P6 native restriction milestone is removed by the user's later decision.

The full inventory below is retained as the roadmap. The original approval language records the planning-stage boundary; the later user approval covers the ten objects in this increment.

Parent roadmap: [Litex support for common LaTeX mathematics](litex-latex-math-support.md).

## Public naming update — 2026-10-18

At the user's request, the public spelling is now `set_diff(A,B)`. It still denotes symmetric difference and renders as `A\triangle B`; ordinary difference remains `set_minus(A,B)`. The original `sym_diff` spelling is removed from the reserved vocabulary. The existing `SymmetricDifference` object and mathematical proof families are unchanged.

Rename verification passed: the release all-target Rust run completed with **1975 tests passed**, the Markdown gate passed **948 blocks**, and all four native examples (**76 top-level statements**, including 14 symmetric-difference statements) passed strict CLI verification. Direct controls confirmed that the new name appears in output, false results and wrong arity are rejected, `set_diff` is reserved, `sym_diff` is no longer reserved or recognized as a builtin, and LaTeX still contains `\triangle`.

The full build also exposed two existing boxed-pattern type errors in the concurrently added `cached_formula_head` tests; adding `.as_ref()` / `.as_mut()` fixed those compile errors without changing their assertions. The final full run passed. Commands used the same isolated release target recorded below; rename CLI evidence is in the task-local `tmp/2026-10-18/set-diff-rename/` directory.

The following initial implementation receipt predates this rename and used the original spelling. Formulas elsewhere in this plan have been updated to the current name.

## Initial implementation acceptance receipt — 2026-10-18

The full Rust run used source snapshot `9f36dac70`; the durable symmetric-difference example additionally includes the subsequently checked finite-enumeration assertion. Later concurrent edits outside this feature are not covered by this receipt.

- `cargo test --release --all-targets --no-fail-fast --target-dir tmp/2026-10-18/latex-phase-1/target`: exit 0; **1971 tests passed** across ten registered targets, including all seven new native-operation test groups.
- `cargo build --release --target-dir tmp/2026-10-18/latex-phase-1/target`: exit 0. The strict native examples, LaTeX outputs and eight CLI negative controls were checked again with this final binary and passed.
- Four [durable examples](../docs/native-elementary-operators.md#native-elementary-operations), **76 top-level statements**, passed `-lang en -strict -f`. Each returned exit 0, `kind: run`, `run_result: success`, `session_terminated: false`, and `termination: null`.
- The four examples also passed `-latex -f`; output preserves native notation and correctly reports `verified: false`.
- `python3 tests/tooling/run_docs_markdown_files.py --litex tmp/2026-10-18/latex-phase-1/target/release/litex`: exit 0; **940 Markdown blocks passed**.
- Executable negative controls reject false identities, missing guards and invalid domains, including `cosh(0)=0`, `conj(i)=i`, `coth(i)=coth(i)`, `0*coth(0)=0`, and `2 $in set_diff({1,2},{2,3})`. A rejected statement preserves previously accepted context.
- The focused tests check reserved names/arity, substitution, congruence, carriers, typed rule evidence, search permission ceilings, all ten LaTeX operators, and explicit unsupported Lean replay.

The implementation audit caught and repaired two domain hazards before final acceptance: `coth`/`csch` retain real-membership evidence alongside nonzero evidence; native equation matchers compare the actual checked structure, so synthetic undefined operands cannot disappear through cancellation. For example, `cosh(0)=0` remains rejected even though a candidate identity might mention `coth(0)*sinh(0)`.

The first full test run found two stale expectations in concurrently changing integer-quotient/Lean tests. The latest source corrected those expectations; the final full run above passed both. Local textbook projects and publication/release gates were outside this task. The release build used an isolated target directory because the shared default target was in concurrent use; these results do not assert that the installed executable was updated.

## 1. Scope and mathematical starting point

Category 1 now contains eleven native public operations (ten delivered, composition proposed):

```text
conj
sec, csc
sinh, cosh, tanh, coth, sech, csch
set_diff
compose
```

Binomial coefficients belong to category 3 in the agreed classification. They are not part of this phase; the earlier abandoned five-scalar proposal is not its scope. Inverse hyperbolic functions, complex analytic extensions and general nth roots retain their own later domain/branch decisions.

The scalar and set operations are defined from existing mathematics. Function composition additionally requires exact callable-domain handling. It follows the scalar/set increment because returning a new function is more involved than returning a scalar or set. The original inventory also proposed `restrict`; the user subsequently chose existing anonymous functions instead.

The sections below preserve the original **proposal**, including relationships and function objects deferred beyond this increment. The current scope and acceptance receipt above identify what is implemented. A `text` block containing source-like formulas is a rule specification, not by itself a claim that the current executable accepts it.

## 2. Primary before/after tracer

Current expression for the complex conjugate of `z`:

```text
re(z) - i * img(z)
```

Proposed public interface and direct relationships:

```text
conj(i) = -i
forall z C:
    conj(conj(z)) = z
    z * conj(z) = C_abs(z)^2
```

Nearest controls: reject `conj({1})` as outside the scalar domain and reject the false equality `conj(i) = i`. Both equality orientations should work where the existing equality interface supports symmetry. Do not turn all expressions matching `re(z)-i*img(z)` into a new named operation during parsing.

Planned persistent tracer: `examples/proof_nodes/equal/by_builtin_rule/complex_conjugation.lit`. It will preserve the former expression as comments, keep the new assertions active, and record its strict release command. Each later family receives its own focused acceptance artifact.

## 3. Proposed Obj representation

Keep the operations as semantic objects through parsing, verification and presentation. The existing [Obj families](../src/ast/obj.rs) already follow this pattern for `sin`, `re`, `img`, set operations and function-space operations.

| Surface | Proposed enum owner/variant | Proposed payload and exact fields |
| --- | --- | --- |
| `conj(z)` | `ComplexOperator::Conjugate` | `Conjugate { arg: Box<Obj> }` |
| `sec(x)` | `TrigOperator::Sec` | `Sec { arg: Box<Obj> }` |
| `csc(x)` | `TrigOperator::Csc` | `Csc { arg: Box<Obj> }` |
| `sinh(x)` | `HyperbolicOperator::Sinh` | `Sinh { arg: Box<Obj> }` |
| `cosh(x)` | `HyperbolicOperator::Cosh` | `Cosh { arg: Box<Obj> }` |
| `tanh(x)` | `HyperbolicOperator::Tanh` | `Tanh { arg: Box<Obj> }` |
| `coth(x)` | `HyperbolicOperator::Coth` | `Coth { arg: Box<Obj> }` |
| `sech(x)` | `HyperbolicOperator::Sech` | `Sech { arg: Box<Obj> }` |
| `csch(x)` | `HyperbolicOperator::Csch` | `Csch { arg: Box<Obj> }` |
| `set_diff(A,B)` | `SetOperator::SymmetricDifference` | `SymmetricDifference { left: Box<Obj>, right: Box<Obj> }` |
| `compose(f,g)` / `f ∘ g` | `FunctionSpace::Composition` | `Composition { outer: Box<Obj>, inner: Box<Obj> }`; see the [current design](litex-function-composition.md) |

### AST Struct Change Proposal

The preferred hyperbolic organization adds `Obj::HyperbolicOperator(HyperbolicOperator)` and a family enum with six variants. This keeps circular trigonometric laws and hyperbolic laws in distinct mathematical families. The alternative is six more variants in `TrigOperator`; it avoids one top-level family but mixes the two groups. Both preserve dedicated leaf identities. Record the chosen organization before implementation.

Together with that family choice, the current table covers additions to existing dedicated enums and eleven leaf payloads. The ten scalar/set payloads were subsequently approved and delivered; the Composition payload remains a proposal. It does not alter existing payload fields, `Identifier`, `Stmt` or `Fact`. Concrete AST authorization is required before the remaining source edits. No Restriction payload is proposed any longer.

The parser constructs the nodes; WD, instantiation/substitution, comparison/IR, proof search, calculation and output consume them. Each payload has the ordinary recursive expression lifetime. Function operands carry values, not copied declarations or permanently cached inferred signatures. A checked signature and its supporting FactIds belong to the WD/proof result, not to the Obj payload.

No new Env/Runtime fields, state owner, symbol registry, transaction policy or search-level policy is proposed. If implementation reveals a real need for one, return to that separate contract decision.

### Why not only parser expansion?

Expanding `conj(z)` immediately to `re(z)-i*img(z)` could provide the value without a new AST node, but would lose the operator identity used by natural diagnostics, direct relationship matching and `\overline{z}` output. Recognizing expanded formulas afterward is ambiguous. Dedicated objects fit existing native operation ownership; expansion remains an explicit, checked definition route.

The new public names become reserved object spellings. Before each increment, scan declarations, parameter bindings and module exports for collisions, and add rejection tests for newly reserved bindings. Do not silently redirect an existing declared identifier to a builtin.

## 4. Domains, results and defining equations

| Operation | Required domain | Result and defining relation |
| --- | --- | --- |
| `conj(z)` | `z in C` | In `C`; `conj(z) = re(z) - i*img(z)` |
| `sec(x)` | `x in R`, `cos(x) != 0` | In `R*`; `sec(x) = 1/cos(x)` |
| `csc(x)` | `x in R`, `sin(x) != 0` | In `R*`; `csc(x) = 1/sin(x)` |
| `sinh(x)` | `x in R` | In `R`; `(exp(x)-exp(-x))/2` |
| `cosh(x)` | `x in R` | In `R+`; `(exp(x)+exp(-x))/2` |
| `tanh(x)` | `x in R` | In `R`; `sinh(x)/cosh(x)`, with `-1 < tanh(x) < 1` |
| `coth(x)` | `x in R`, `x != 0` | In `R*`; `cosh(x)/sinh(x)` |
| `sech(x)` | `x in R` | In `R+`; `1/cosh(x)`, with `sech(x) <= 1` |
| `csch(x)` | `x in R`, `x != 0` | In `R*`; `1/sinh(x)` |
| `set_diff(A,B)` | The same set-operand contract as existing union/difference | A set; `union(set_minus(A,B),set_minus(B,A))` |
| `compose(f,g)` / `f ∘ g` | Checked unary outer `f` and fixed positive-arity inner `g`; every admissible input of `g` yields a legal call to `f` | Function with the exact input domain/guards of `g`; application is `f(g(args))` |

Do not invent a stricter set-operand model than existing `union`/`set_minus`: Litex uses its existing pure-set foundation. For composition's outer function, “unary” includes one tuple-valued input. Inner functions may have multiple separate arguments; no implicit tuple spreading, currying or parameter-dependent return carriers are introduced.

Hyperbolic division must be supported by the relevant evidence: `cosh(x)>0` for all real `x`, and `sinh(x)!=0` when `x!=0`. WD cannot prove these by calling back into the same unverified quotient. Establish the nonzero/sign relations on the primitive hyperbolic functions first.

### Exact function-domain contract

Existing [call WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/core.rs) collects signature candidates with their source FactIds; [complete-domain evidence](../src/execute/execute_fact_stmt/function_domain.rs) retains the actual callable source. Current [signature parsing and binder checks](../src/parse/object/primary.rs) require parameter carriers and the return set to be independent of the signature's own binders, although guards and bodies may use them. Older FnSet comments suggesting dependent return carriers do not override these checks.

The [composition design](litex-function-composition.md) now owns the exact contract, including unary outer/multi-argument inner functions, checked signature selection, retained local scopes, strict complete-domain preservation and callable consumers. Under the inner binders and guards, check `g(args)` and then `f(g(args))`; do not shrink the inner domain when an outer guard cannot be established. No new Env/Runtime state contract is proposed.

Restrictions use existing anonymous functions, for example `fn(x {1,2}) R {f(x)}`. The body must satisfy `f`'s actual input conditions; writing a wrapper does not waive them.

## 5. Definition routes versus BT relationships

Here “BT rules” means the mathematical builtin relationships the user requested. Keep the existing proof owners separate:

- **Defining-equation rules:** expose `conj(z)=re(z)-i*img(z)`, the hyperbolic defining equations and the symmetric-difference expansion as explicit native defining-equation leaves. Current native equations such as `ExpAsEulerPower` already use a BT leaf in `by_native_fixed_base.rs`; preserve that pattern rather than creating a parallel definition registry. Definition equations and derived identities remain separate mathematical groups even when both use BT evidence.
- **Function application route:** the composition evaluation equation consumes the parent call's checked domain and signatures through the existing function application/object-definition responsibility. Ordinary declared function unfolding and anonymous-function restriction retain their current proof classification.
- **Equality BT rules:** recognize the fixed mathematical laws below. A direct law must not require expanding every occurrence into coordinates/exponentials.
- **Atomic BT/structural membership:** establish result carriers, sign/nonzero facts, order bounds, membership and subset facts with their actual requirements.
- **Bounded strategy:** use only where a constructor genuinely decomposes into checked children, such as membership in a symmetric difference. Keep the measure and child permissions explicit.
- **Inference:** add only normal typing consequences needed for later use. Do not eagerly publish every identity on object creation.

Every rule specifies its matched objects, premises, exact conclusion and typed evidence. Structural matching is not permission to search equality aliases without retaining their proofs. Reuse existing equality symmetry/congruence; do not write two independent mathematical rules merely for swapped equality endpoints.

Never add unrestricted bidirectional rewriting between native objects and their defining formulas. A request for a definition may unfold once; a BT matcher may recognize either equality orientation without recursively alternating representations.

## 6. Relationship inventory and implementation increments

All equations below require the declared carriers and **both sides to be WD**. Extra guards are written next to the relevant laws.

### P1 — Complex conjugation

Dependencies: existing complex scalar arithmetic, `re`, `img`, `C_abs` and exact complex calculation.

Required relationship groups:

| Group | Laws to support |
| --- | --- |
| Constants/real embedding | `conj(0)=0`, `conj(1)=1`, `conj(i)=-i`; `conj(x)=x` for real `x` |
| Coordinates/involution | `re(conj(z))=re(z)`, `img(conj(z))=-img(z)`, `conj(conj(z))=z` |
| Arithmetic | `conj(-z)=-conj(z)`; preserve addition, subtraction and multiplication |
| Division/powers | `conj(z/w)=conj(z)/conj(w)` when `w!=0`; `conj(z^n)=conj(z)^n` for `n in N` |
| Modulus/realness | `C_abs(conj(z))=C_abs(z)`; `z*conj(z)=C_abs(z)^2`; fixed-point/zero relationships with realness and `z=0` |

Implement fixed-point and zero statements as explicitly directed implications/atomic checks with retained premises. Do not infer that an arbitrary complex value is real.

Acceptance: exact numeric case, symbolic involution, symbolic product/modulus law, composition under another native operator, false `conj(i)=i`, set input rejection, and quotient without a nonzero denominator. Preserve exact arithmetic; no floating-point proof of equality.

### P2 — Secant and cosecant

Dependencies: sine/cosine, their zero/nonzero facts, existing `tan`/`cot` domains.

| Group | Laws to support |
| --- | --- |
| Reciprocal | `sec(x)*cos(x)=1`; `csc(x)*sin(x)=1` |
| Existing trig connections | `tan(x)=sin(x)*sec(x)`; `cot(x)=cos(x)*csc(x)` |
| Pythagorean | `sec(x)^2=1+tan(x)^2`; `csc(x)^2=1+cot(x)^2` |
| Parity/period | `sec(-x)=sec(x)`; `csc(-x)=-csc(x)`; period `2*pi` for both |
| Cross/phase relations | `sec(x+pi)=-sec(x)`; `csc(x+pi)=-csc(x)`; `csc(pi/2-x)=sec(x)` |
| Exact anchors | `sec(0)=1`, `sec(pi)=-1`, `csc(pi/2)=1` |

Acceptance must reject `sec(pi/2)`, `csc(0)`, an unguarded arbitrary-real `sec(x)` claim and the false parity `csc(-pi/2)=csc(pi/2)`. Cancellation must not mask an undefined operand.

### P3a — Primitive hyperbolic functions

Add `sinh` and `cosh` together; they share the exponential definitions and essential identity.

```text
sinh(0) = 0                       cosh(0) = 1
sinh(-x) = -sinh(x)                cosh(-x) = cosh(x)
cosh(x)^2 - sinh(x)^2 = 1
exp(x) = cosh(x) + sinh(x)
exp(-x) = cosh(x) - sinh(x)
sinh(x+y) = sinh(x)*cosh(y) + cosh(x)*sinh(y)
cosh(x+y) = cosh(x)*cosh(y) + sinh(x)*sinh(y)
sinh(2*x) = 2*sinh(x)*cosh(x)
cosh(2*x) = cosh(x)^2 + sinh(x)^2
```

Atomic relationships: `cosh(x)>=1`, `cosh(x)>0`; `sinh(x)=0` iff `x=0`; positive/negative `x` gives the corresponding sign of `sinh(x)`; strict monotonicity of `sinh`, and monotonicity of `cosh` on the nonnegative half-line. Guard sign-dependent claims; `cosh` is not strictly increasing on all reals.

Acceptance: zero values, addition/identity with arbitrary real binders, exact `exp` connections, sign evidence reusable by another expression, rejection of complex arguments, and rejection of `cosh(0)=0`.

### P3b — Hyperbolic quotients and reciprocals

Add `tanh`, `sech`, then guarded `coth`, `csch`, using P3a positivity/nonzero evidence.

```text
tanh(x)*cosh(x) = sinh(x)          sech(x)*cosh(x) = 1
coth(x)*sinh(x) = cosh(x)          csch(x)*sinh(x) = 1   [x != 0]
1 - tanh(x)^2 = sech(x)^2
coth(x)^2 - 1 = csch(x)^2                              [x != 0]
tanh(x)*coth(x) = 1                                   [x != 0]
tanh(x) = sinh(x)*sech(x)
coth(x) = cosh(x)*csch(x)                              [x != 0]
tanh(x+y) = (tanh(x)+tanh(y))/(1+tanh(x)*tanh(y))
```

Add parity (odd: `tanh/coth/csch`; even: `sech`), `tanh(0)=0`, `sech(0)=1`, `-1<tanh(x)<1`, `0<sech(x)<=1`, and strict monotonicity of `tanh`. The addition formula's denominator needs checked nonzero evidence; derive it from the established range or a direct bounded positive-denominator rule, without raising global search permissions.

Acceptance must reject `coth(0)`, `csch(0)`, complex arguments and the false `1+tanh(x)^2=sech(x)^2` at a concrete nonzero real input with sufficient exact inequality evidence. A missing automated proof of a true statement is a separate test category, not a false-mathematics control.

### P4 — Set symmetric difference

Dependencies: union, intersection, set difference and existing logical facts. The defining membership condition uses existing `and/or/not`; no new XOR Fact variant is needed.

```text
x in set_diff(A,B) iff (x in A and x not in B) or (x in B and x not in A)
set_diff(A,B) = set_diff(B,A)
set_diff(set_diff(A,B),C) = set_diff(A,set_diff(B,C))
set_diff(A,{}) = A                  set_diff(A,A) = {}
set_diff(set_diff(A,B),B) = A
set_diff(A,B) = set_minus(union(A,B),intersect(A,B))
intersect(C,set_diff(A,B)) = set_diff(intersect(C,A),intersect(C,B))
set_diff(A,B) subset union(A,B)
```

Conditional connections: disjoint `A,B` imply `set_diff(A,B)=union(A,B)`; `B subset A` implies `set_diff(A,B)=set_minus(A,B)`. For finite sets, require both finite certificates before the cardinality identity:

```text
finite_set_size(set_diff(A,B)) = finite_set_size(A)+finite_set_size(B)-2*finite_set_size(intersect(A,B))
```

Acceptance: `set_diff({1,2},{2,3})={1,3}`, symbolic involutive cancellation, both membership branches, empty/identical sets, and rejection of `set_diff({1},{1})={1}`. Membership descent removes the outer constructor; do not expand arbitrarily nested Boolean formulas into exponential normal forms.

### P5 — Function composition

See the dedicated [composition design and implementation sequence](litex-function-composition.md). Both `compose(f,g)` and `f ∘ g` mean outer `f` after inner `g`; `(f ∘ g)(args)=f(g(args))`. The inner function may have any fixed positive arity and guards, which remain its exact domain. The outer function has one input at this call layer.

The first delivery includes application/anonymous-function definition, associativity only when both sides are WD, exact-domain identity laws, range inclusion, and existing congruence. Right associativity is a parsing choice, not permission to flatten the AST. Later preimage and mapping-property laws remain explicit follow-up work. The new plan also records existing user-defined `compose` name collisions and their migration.

### Former P6 — Native restriction removed from scope

The user chose existing anonymous functions instead of a new restriction object:

```text
fn(x S) B {f(x)}
fn(x, y R: x < y) R {f(x,y)}
```

These construct the explicitly written domain and still check every body call. See the existing [restriction beta tracer](../examples/proof_nodes/equal/by_object_definition/by_fn_application/restricted_literal_beta.lit). Native `restrict`, its AST and its dedicated laws are no longer required to complete Phase 1.

## 7. Code owners and evidence wiring

| Responsibility | Existing owner to extend |
| --- | --- |
| Obj/constructors/conversions | `src/ast/obj.rs` and existing object helpers; exact approved variants only |
| Token/name/arity/parse | `src/parse/keywords.rs`, `src/parse/object/primary.rs`; existing reserved-object binding checks |
| Canonical representation | `src/display_and_ir/obj.rs`, existing alpha normalization, comparison, traversal and instantiation owners |
| WD and result shapes | `src/execute/execute_fact_stmt/well_defined_results/verify_obj/` and its corresponding typed result families |
| Callable applications | Existing `FnObj` call checks, checked-signature evidence and function application/definition rules |
| Native defining equations | Matching native equality family, following `verify_equality/verify_equality_by_builtin_rules/by_native_fixed_base.rs`; named defining-equation evidence |
| Function definition/application | `verify_equality/by_object_definition/`; parent-checked composition applications and existing function unfolding |
| Equality BT | `verify_equality/verify_equality_by_builtin_rules/`; dedicated family files such as conjugation, reciprocal trig, hyperbolic identities and symmetric difference |
| Membership/order/nonzero | `verify_atomic_except_equality/` owning builtin/structural routes; reuse their premise ceilings |
| Exact evaluation | Existing `rational_expression/` and closed calculation/eval paths; no approximate equality |
| Proof explanation | `src/json_output/project_detailed/` plus corresponding equality/atomic result variants |
| LaTeX | `src/compile_to_latex/obj.rs`, `fact.rs` where needed, and conversion tests |
| Lean/replay consumers | Relevant `src/compile_to_lean/` object/WD/rule consumers; support or explicit fail-closed diagnostics |

The shortened equality/atomic paths above are under `src/execute/execute_fact_stmt/verify_atomic_fact/`.

Proof payloads mirror the actual rule. For example, a quotient rule retains its denominator nonzero proof unless the parent WD result already supplies that exact obligation; a composition result retains both signature certificates and the scoped legal-application proof. Use a typed reference to existing parent evidence when appropriate, not a fabricated independent proof or duplicated unchecked Boolean.

Do not append every new law to an unrelated historical `waveN` file. Preserve existing dispatch order and use the matching mathematical family. Add only the new family dispatch entries needed by the approved operations.

## 8. Per-increment execution protocol

1. **Freeze the contract.** Confirm the exact AST addition and public semantics for that increment, including reserved-name impact. Revalidate the current shared worktree.
2. **Baseline and tracer.** Build current release; preserve the missing-interface observation and an existing mathematical expression. Select one persistent positive tracer and executable failure controls.
3. **Wire Obj end to end.** Add the approved parse/AST/IR/traversal/instantiation/display/LaTeX support. Add exhaustive-consumer handling; do not leave a parse-only success presented as a complete feature.
4. **Enforce WD and output carrier.** Check children and guards, retain evidence, support nested consumption. For function-producing objects, finish the callable signature/application path at this step.
5. **Add definitions and BT relationships.** Implement the listed groups with narrow matchers and bounded premise checks. Record rule identity, requirements and proof children. Do not widen global search to make the demonstration pass.
6. **Exercise public source.** Author/revise in one persistent `-session`; preserve accepted context after ordinary failures and journal the exact attempts. Materialize the accepted example at a coherent checkpoint.
7. **Verify and document.** Run direct strict positive files, executable false/domain controls, focused Rust and output checks, then the broader gate justified by the impact. Update Manual/cheatsheet and precise unsupported compiler boundaries.
8. **Close the increment.** Audit every rule row, artifact and output, record the receipt, and proceed to the next dependency. Partial implementation remains explicitly incomplete.

## 9. Validation and completion checklist

Planning is L0: inspect this document's coverage, guards and source links; no build or verification run is necessary to claim that the **plan** has been written.

Implementing new public objects is L4 because it extends shared representation and syntax. Do not call it L1 merely because the mathematical formula is short. After the relevant authorization and code changes:

```sh
cargo build --release
target/release/litex -lang en -strict -f examples/proof_nodes/equal/by_builtin_rule/complex_conjugation.lit
target/release/litex -latex -lang en -f examples/proof_nodes/equal/by_builtin_rule/complex_conjugation.lit
cargo test --release --all-targets --no-fail-fast
python3 tests/tooling/run_docs_markdown_files.py
```

The first tracer path is proposed and does not exist as a result of this planning task. Later increments replace it with their maintained family tracers. Select additional focused filters only after creating/locating the actual tests. Consult [current test architecture](../tests/README.md): a filter named `run_examples` is not evidence that the entire examples corpus ran. Audit corpus collection and run the affected native object/proof fixtures explicitly. No local textbook, packaging or release gate is required by this plan.

Successful proof-file acceptance requires exit 0 and the Normal JSON envelope `kind=run`, `run_result=success`, `session_terminated=false`, `termination=null`. LaTeX acceptance separately requires the expected artifact and notation; `verified=false` remains correct for that parse-only route.

Expected notation: `conj(z)` -> `\overline{z}`; reciprocal/hyperbolic operations -> their mathematical operator names (`\operatorname{sech}` etc. where needed); `set_diff` -> `\triangle`; composition -> `\circ` with preserved grouping. Keep object-output escaping and function-call precedence tests. This plan no longer adds native restriction notation.

For every increment, require:

- [ ] Approved exact Obj shape and public name/domain contract.
- [ ] Definition route, WD, carriers and all required relationship groups implemented.
- [ ] Numeric and symbolic positives; both equality orientations; nested use.
- [ ] Invalid-domain and false-result controls; no accepted fact after failure.
- [ ] Source aliases/module names, substitution and binder capture controls where applicable.
- [ ] Actual proof result and JSON explanation retain the premises used.
- [ ] LaTeX and diagnostic/IR output preserve meaning.
- [ ] Compiler support verified or unsupported path explicitly fails closed.
- [ ] Current-source gates, live documentation and durable acceptance receipt complete.

Phase 1 is complete only when P1, P2, P3a, P3b, P4 and the scoped P5 deliveries meet their checklists. P6 was removed by the user's restriction decision. The overall five-category roadmap remains separate.
