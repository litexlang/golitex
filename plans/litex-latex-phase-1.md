# Phase 1: common native mathematical operations

Date: 2026-10-18. Status: first scalar/set implementation; final validation in progress.

## Current implementation scope

The user approved the Obj additions, then explicitly deferred function composition and restriction. This increment adds the ten scalar/set objects below, using the proposed independent `HyperbolicOperator` family. `compose` and `restrict` remain unimplemented. No existing AST payload fields or Env/Runtime state contracts changed.

Implemented: native parsing, reserved names, display/IR, recursive substitution and congruence, typed WD evidence, result carriers, LaTeX, defining equations and the focused law groups documented in [Native elementary operations](../docs/native-elementary-operators.md). Conjugation and hyperbolic anchors use exact arithmetic. Symmetric difference supports XOR membership/nonmembership and exact rational-list enumeration. Lean replay fails closed.

Remaining from the complete proposal: conjugate fixed-point/zero reflection; hyperbolic general sign, range and monotonicity laws; tanh addition; symmetric-difference subset/disjointness/finite-cardinality laws; all of P5/P6. These are not claimed implemented by adding the objects.

The full inventory below is retained as the roadmap. The original approval language records the planning-stage boundary; the later user approval covers the ten objects in this increment.

Parent roadmap: [Litex support for common LaTeX mathematics](litex-latex-math-support.md).

## 1. Scope and mathematical starting point

Category 1 contains twelve proposed public operations:

```text
conj
sec, csc
sinh, cosh, tanh, coth, sech, csch
sym_diff
compose, restrict
```

Binomial coefficients belong to category 3 in the agreed classification. They are not part of this phase; the earlier abandoned five-scalar proposal is not its scope. Inverse hyperbolic functions, complex analytic extensions and general nth roots retain their own later domain/branch decisions.

The scalar and set operations are defined from existing mathematics. Function composition and restriction additionally require exact callable-domain handling. They are last because returning a new function is more involved than returning a scalar or set.

All new names, Rust shapes and mathematical examples below are **proposed**. A `text` block containing source-like formulas is a rule specification, not a claim that the current executable accepts it.

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
| `sym_diff(A,B)` | `SetOperator::SymmetricDifference` | `SymmetricDifference { left: Box<Obj>, right: Box<Obj> }` |
| `compose(g,f)` | `FunctionSpace::Composition` | `Composition { outer: Box<Obj>, inner: Box<Obj> }` |
| `restrict(f,S)` | `FunctionSpace::Restriction` | `Restriction { function: Box<Obj>, domain: Box<Obj> }` |

### AST Struct Change Proposal

The preferred hyperbolic organization adds `Obj::HyperbolicOperator(HyperbolicOperator)` and a family enum with six variants. This keeps circular trigonometric laws and hyperbolic laws in distinct mathematical families. The alternative is six more variants in `TrigOperator`; it avoids one top-level family but mixes the two groups. Both preserve dedicated leaf identities. Record the chosen organization before implementation.

Together with that family choice, the table proposes additions to existing dedicated enums and twelve leaf payloads. It does not alter existing payload fields, `Identifier`, `Stmt` or `Fact`. These changes require concrete AST authorization before source edits.

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
| `sym_diff(A,B)` | The same set-operand contract as existing union/difference | A set; `union(set_minus(A,B),set_minus(B,A))` |
| `compose(g,f)` | Checked unary function signatures; every admissible input of `f` yields a legal call to `g` | Function with the exact input domain of `f`; application is `g(f(x))` |
| `restrict(f,S)` | Checked unary `f`; every `x in S` is in its complete admissible domain, including guards | Function with exact domain `S`; application is `f(x)` |

Do not invent a stricter set-operand model than existing `union`/`set_minus`: Litex uses its existing pure-set foundation. For function signatures, “unary” includes one tuple-valued input. Multiple separate arguments/dependent outputs need an explicit later extension, not implicit currying or coordinate guessing.

Hyperbolic division must be supported by the relevant evidence: `cosh(x)>0` for all real `x`, and `sinh(x)!=0` when `x!=0`. WD cannot prove these by calling back into the same unverified quotient. Establish the nonzero/sign relations on the primitive hyperbolic functions first.

### Exact function-domain contract

Existing [call WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/core.rs) collects signature candidates with their source FactIds; [FnSet](../src/ast/obj.rs) carries ordered domain facts and can have a dependent return carrier. A native composition/restriction must preserve this evidence rather than copy the first syntactically convenient signature.

For the initial unary, nondependent-output interface:

- Composition preserves the inner function's complete domain and its guards. Under those binders/guards, verify `f(x)` and then `g(f(x))` with the existing application checks. A guarded outer function is allowed only when the inner output satisfies its guard for every admissible input.
- Restriction requires `S` to be a subset of the complete admissible input domain. A subset of the carrier alone is insufficient when the function has a guard. Do not silently filter invalid elements out of `S`.
- Multiple signatures may justify the same result, but must not change the result's domain. Preserve the chosen signature certificates; if they imply genuinely incompatible domain contracts, report that ambiguity instead of selecting by iteration order.
- Return a real callable function and publish/use its checked signature through the existing mechanisms. Its application, membership, substitution and function extensionality must work beyond the initial construction line.
- Local proof scopes retain their existing `local_env` evidence in the success result. No binder identifiers or WD references may escape an unretained scope.

Illustrative guard boundary:

```text
f : fn(x R: x != 0) R
restrict(f, {1,2})           valid if the existing signature is established
restrict(f, {0})             reject: 0 violates f's actual domain
restrict(f, {1,2})(0)        reject: outside the restricted domain
```

The initial unary interface and hyperbolic family placement are explicit design decisions to finalize before their implementation increments. This plan does not promise general dependent/multi-argument composition.

## 5. Definition routes versus BT relationships

Here “BT rules” means the mathematical builtin relationships the user requested. Keep the existing proof owners separate:

- **Defining-equation rules:** expose `conj(z)=re(z)-i*img(z)`, the hyperbolic defining equations and the symmetric-difference expansion as explicit native defining-equation leaves. Current native equations such as `ExpAsEulerPower` already use a BT leaf in `by_native_fixed_base.rs`; preserve that pattern rather than creating a parallel definition registry. Definition equations and derived identities remain separate mathematical groups even when both use BT evidence.
- **Function application route:** the compose/restrict evaluation equations consume the parent call's checked domain and signatures through the existing function application/object-definition responsibility. Ordinary declared function unfolding retains its current proof classification.
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
x in sym_diff(A,B) iff (x in A and x not in B) or (x in B and x not in A)
sym_diff(A,B) = sym_diff(B,A)
sym_diff(sym_diff(A,B),C) = sym_diff(A,sym_diff(B,C))
sym_diff(A,{}) = A                  sym_diff(A,A) = {}
sym_diff(sym_diff(A,B),B) = A
sym_diff(A,B) = set_minus(union(A,B),intersect(A,B))
intersect(C,sym_diff(A,B)) = sym_diff(intersect(C,A),intersect(C,B))
sym_diff(A,B) subset union(A,B)
```

Conditional connections: disjoint `A,B` imply `sym_diff(A,B)=union(A,B)`; `B subset A` implies `sym_diff(A,B)=set_minus(A,B)`. For finite sets, require both finite certificates before the cardinality identity:

```text
finite_set_size(sym_diff(A,B)) = finite_set_size(A)+finite_set_size(B)-2*finite_set_size(intersect(A,B))
```

Acceptance: `sym_diff({1,2},{2,3})={1,3}`, symbolic involutive cancellation, both membership branches, empty/identical sets, and rejection of `sym_diff({1},{1})={1}`. Membership descent removes the outer constructor; do not expand arbitrarily nested Boolean formulas into exponential normal forms.

### P5 — Function composition

Proposed order is `compose(g,f) = g after f`, so `compose(g,f)(x)=g(f(x))`.

Required laws, for compatible exact domains:

```text
compose(g,f)(x) = g(f(x))
compose(h,compose(g,f)) = compose(compose(h,g),f)
compose(id_B,f) = f                 compose(f,id_A) = f
fn_range(compose(g,f)) subset fn_range(g)
```

Here `id_A`/`id_B` denote ordinary existing anonymous identity functions on the matching sets, not additional builtin names. Preserve equality of complete domains before using function extensionality. Do not claim composition is commutative or that `f`'s output need merely intersect `g`'s domain.

Acceptance uses named and anonymous functions, calls to a composed function, declaration of its return function type, aliases and module-qualified operands, and equality proved by the appropriate function rule. Concrete target: `f(x)=x+1`, `g(x)=x^2` yields `compose(g,f)(2)=9` and `compose(f,g)(2)=5`. Reject incompatible carriers and a guarded outer function whose guard fails on some inner output.

If the existing callable-result mechanism cannot expose the new function without changing its state contract, present that exact owner change before implementing P5; do not add an unapproved parallel signature cache.

### P6 — Function restriction and cross-operation relationships

Required laws under the exact subset/guard conditions:

```text
restrict(f,S)(x) = f(x)                         [x in S]
restrict(restrict(f,T),S) = restrict(f,S)        [S subset T subset dom(f)]
restrict(f,dom(f)) = f
restrict(compose(g,f),S) = compose(g,restrict(f,S))
fn_range(restrict(f,S)) subset fn_range(f)
```

`dom(f)` in these formulas is mathematical specification notation, not a proposed extra Obj. Concrete acceptance supplies the known domain set from the function's signature. When `f` has guards, that set must describe its complete admissible domain.

The restriction/composition law does not require restricting `g` to `S`: `S` contains inputs of `f`, not generally inputs of `g`. Add finite-domain and empty-domain cases with the existing callable rules. Do not equate `restrict(f,S)` with `f` for a proper subset merely because their values agree on `S`.

Acceptance: ordinary real functions restricted to `{1,2}`, guarded reciprocal restricted to `{1,2}`, rejection at `{0}`, rejection of application outside the restricted set, nested restriction, compatible cross-operation identity, and use of the new function in an existing function-consuming API.

## 7. Code owners and evidence wiring

| Responsibility | Existing owner to extend |
| --- | --- |
| Obj/constructors/conversions | `src/ast/obj.rs` and existing object helpers; exact approved variants only |
| Token/name/arity/parse | `src/parse/keywords.rs`, `src/parse/object/primary.rs`; existing reserved-object binding checks |
| Canonical representation | `src/display_and_ir/obj.rs`, existing alpha normalization, comparison, traversal and instantiation owners |
| WD and result shapes | `src/execute/execute_fact_stmt/well_defined_results/verify_obj/` and its corresponding typed result families |
| Callable applications | Existing `FnObj` call checks, checked-signature evidence and function application/definition rules |
| Native defining equations | Matching native equality family, following `verify_equality/verify_equality_by_builtin_rules/by_native_fixed_base.rs`; named defining-equation evidence |
| Function definition/application | `verify_equality/by_object_definition/`; parent-checked compose/restrict applications and existing function unfolding |
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

Expected notation: `conj(z)` -> `\overline{z}`; reciprocal/hyperbolic operations -> their mathematical operator names (`\operatorname{sech}` etc. where needed); `sym_diff` -> `\triangle`; composition -> `\circ` with preserved grouping; restriction -> `f|_S`. Keep object-output escaping and function-call precedence tests.

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

Phase 1 is complete only when P1, P2, P3a, P3b, P4, P5 and P6 meet this checklist. The overall five-category roadmap remains separate.
