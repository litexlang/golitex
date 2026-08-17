# Litex-to-Lean Compiler 2

Compiler2 is the new implementation path for the second Litex target ABI. Its
Rust implementation is the root-crate module and binary under
`../src/litex_to_lean_compiler2/`; this directory owns the Lean ABI, generated
examples, and the stable `compiler2.sh` entrypoint. Compiler2 reuses the
verifier's checked IR capture, but it does not use the old universal-object
emitter. That emitter and its `-lean` CLI remain temporarily available outside
the compiler2 design.

The package retains the established `Litex` namespace and `abiVersion` name,
but reports `Litex.abiVersion = 2` so it cannot be mistaken for the old object
ABI.

`Litex/Core.lean` is the single semantic bridge header. It defines every
compiler2 concept that interprets Litex through Lean and Mathlib, including
`Same`, `Set`, `In`, numeric carriers, `AsReal`, `Lt`, and `Le` together with
their bridge/transport interface. `Litex/Rules.lean` contains only concrete
theorems selected by verifier certificates; it introduces no second semantic
layer.

The implemented scope is deliberately small:

- `Litex.BridgeRule` is the controlled extension point for primitive
  representation rules;
- `Litex.Bridge` records one installed cross-carrier representation step;
- `Litex.Same` is their reflexive, symmetric, transitive closure;
- `Litex.Set` packages the exact carrier of a Litex set;
- `Litex.In` defines heterogeneous membership through `Same`;
- `Litex.Fn s S` is the first unary proof-carrying function carrier;
- `Litex.fnSet s S` packages that carrier as a Litex set;
- `Litex.fnApply f hf x hx` consumes both function and argument membership;
- `N`, `Z`, `Q`, `R`, and `C` use Mathlib's native carriers;
- `setBuilder` represents a predicate-defined subset by a subtype carrier;
- `AsReal x r` means that `r : ℝ` is a real representative of `x`;
- `Lt` and `Le` compare heterogeneous objects through such representatives;
- `RealCoherence` is the explicit registry certificate asserting uniqueness of
  real representatives.

Every compiler2 example is a checked-in generated pair:

```text
examples/<name>.lit   authoritative verified Litex source
examples/<name>.lean  generated compiler2 output; never hand-edited
```

`./compiler2.sh generate examples` verifies every source, captures its
verifier-produced IR, and refreshes the paired Lean file. `./compiler2.sh check
examples` recompiles each source in memory, rejects checked-in drift, and
submits every generated file to the real Lean kernel.

To refresh one pair after editing its Litex source, pass only the source path;
compiler2 infers the same-name `.lean` output:

```sh
./compiler2.sh compile examples/1_SetSystem.lit
```

The first executable example translates the intended source shape

```text
have A set = R
have B set = C
forall a A, b B:
    a = b
    =>:
        b $in A
        a $in B
```

to two checked named-set aliases, two complex-valued binders, separate
membership hypotheses, and one heterogeneous `Litex.Same` hypothesis. Because
this tracer is a source `sketch`, compiler2 emits it inside `__Sketch01`, nested
under the namespace derived from the source filename. The theorem retains the
`__fact0` and `__h0_*` naming convention:

```lean
theorem __fact0 :
  ∀ (a : ℂ) (__h0_1 : Litex.In a A)
    (b : ℂ) (__h0_2 : Litex.In b B)
    (__h0_3 : Litex.Same a b),
    Litex.In b A ∧ Litex.In a B
```

See `examples/1_SetSystem.lit` and its generated
`examples/1_SetSystem.lean`. Compiler2 examples live exclusively in that
directory.

The comparison tracer in `examples/2_OrderSystem.lit` translates

```text
forall a, b R:
    a < b
    =>:
        a <= b
```

as complex-valued binders with `In`, `Lt`, and `Le` propositions.  The proof
is the ordinary real theorem `< → ≤` after unpacking the representatives.

The first non-`sketch` tracer is `examples/3_AtomicEquality.lit`:

```text
1 = 1
2 + 3 = 5
```

Both are ordinary top-level facts. Numerals and `+` lower to native `ℂ`
expressions, while equality lowers to `Litex.Same`. Reflexivity consumes the
verifier's `ObjectReflexivity` certificate. Closed addition consumes a checked
rational-normalization certificate, replays its numeric WD membership facts,
and invokes `norm_num` only after compiler2 independently validates that exact
source equality with Litex's rational-expression evaluator.

The first function tracer is `examples/4_FunctionSet.lit`:

```text
forall s, S set, x s, f fn(y s) S:
    f(x) = f(x)
```

The set parameters become `s S : Litex.Set`. The values `x` and `f` keep
independent Lean carriers rather than being retyped to those sets. Their
source parameter facts become `hx : Litex.In x s` and
`hf : Litex.In f (Litex.fnSet s S)`. Each application is emitted as
`Litex.fnApply f hf x hx`, using the exact function-membership FactId and the
exact argument-membership WD edge selected by the verifier. The result already
has carrier `S.Carrier`; no transport back to a native predicate is added.

This first function adapter supports one named unary layer with no extra
domain facts. Anonymous functions, multiple arguments, domain clauses, and
curried function returns remain fail-closed.

Sketch is a real source scope, not an example-file wrapper. Each top-level
sketch is emitted as `__Sketch01`, `__Sketch02`, and so on. Its emitter context
starts with the facts and symbols visible outside the sketch, but definitions
and FactIds created inside it do not leak back out. Facts written directly at
file level, including the function tracer above, remain direct declarations in
the file namespace.

Build and audit with:

```sh
lake build
./compiler2.sh compile examples/1_SetSystem.lit
./compiler2.sh check examples
```

Generated files contain no `sorry`. The compiler2 Rust tests also pass a
Litex-verified but unsupported proof route and require compilation to fail
closed. This project declares no new Lean axioms.

`BridgeRule` is intentionally extensible on the Lean side: an integration may
register a new, reviewed representation relation. The Litex compiler will only
emit/import its own allowlisted rules; ordinary source equality never creates
a bridge by itself.

An arbitrary extension can make real representatives non-unique—for example,
a rule identifying numerical zero and one. The core therefore does not silently
postulate uniqueness. Theorems that need it take a `RealCoherence` certificate;
supplying such a certificate after an incoherent extension requires an explicit
trusted assumption. Transporting an already chosen representative and deriving
`Lt → Le` require no certificate.

`universe u` and `Litex.u := Type u` use Lean's ordinary universe hierarchy;
they do not create a separate Litex universe. Mathlib's usual numeric carriers
therefore work directly. `Same` currently relates different carriers at the
same Lean universe level; cross-universe edges are not part of this slice.
This does not prevent higher-order sets: `Litex.Set.{0}` lives in `Type 1`, so
it can be the carrier of `Litex.Set.{1}`. Only the real-comparison layer is
confined to ordinary `Type`, since its representatives are Mathlib values in
universe zero. A generated example for higher-order set construction is
deferred until the IR and v2 emitter support its Litex statement form; it is
not represented by hand-written code under `examples/`.

The compiler currently emits only the reviewed IR routes exercised by the
four numbered examples. Checked named aliases of `R` and `C`, top-level atomic
equality, nonnegative integer numerals, addition, arbitrary set parameters,
unary function sets, and named unary application are supported. Other atomic
predicates and arithmetic operators, bare arbitrary-set choices
(`have A set`), richer function forms, richer set constructors, and broader
production code-generation are not implemented yet.
