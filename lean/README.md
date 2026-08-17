# Litex-to-Lean Compiler 2

This repository is an independent executable prototype of the second Litex
target ABI. It does not modify or wrap the existing universal-`Litex.Object`
compiler.

The package retains the established `Litex` namespace and `abiVersion` name,
but reports `Litex.abiVersion = 2` so it cannot be mistaken for the old object
ABI.

The implemented scope is deliberately small:

- `Litex.BridgeRule` is the controlled extension point for primitive
  representation rules;
- `Litex.Bridge` records one installed cross-carrier representation step;
- `Litex.Same` is their reflexive, symmetric, transitive closure;
- `Litex.Set` packages the exact carrier of a Litex set;
- `Litex.In` defines heterogeneous membership through `Same`;
- `N`, `Z`, `Q`, `R`, and `C` use Mathlib's native carriers;
- `setBuilder` represents a predicate-defined subset by a subtype carrier;
- `AsReal x r` means that `r : ℝ` is a real representative of `x`;
- `Lt` and `Le` compare heterogeneous objects through such representatives;
- `RealCoherence` is the explicit registry certificate asserting uniqueness of
  real representatives.

The primary executable example translates the intended source shape

```text
forall a R, b C:
    a = b
    =>:
        b $in R
        a $in C
```

to two complex-valued binders, separate membership hypotheses, and one
heterogeneous `Litex.Same` hypothesis. The emitted theorem shape retains the
old compiler's `__SetSystem01`, `__fact0`, and `__h0_*` naming convention:

```lean
theorem __fact0 :
  ∀ (a : ℂ) (__h0_1 : Litex.In a Litex.R)
    (b : ℂ) (__h0_2 : Litex.In b Litex.C)
    (__h0_3 : Litex.Same a b),
    Litex.In b Litex.R ∧ Litex.In a Litex.C
```

See `examples/SetSystem.lean` for the compiled proof. Compiler2 examples live
exclusively in that directory; the `Compiler2Examples` Lake target compiles
them from the compiler2 environment.

The comparison tracer in `examples/OrderSystem.lean` translates

```text
forall a R, b R:
    a < b
    =>:
        a <= b
```

as complex-valued binders with `In`, `Lt`, and `Le` propositions.  The proof
is the ordinary real theorem `< → ≤` after unpacking the representatives.

For an exact user-defined set, the compiler creates a hidden carrier such as
`__Marker` and emits `Markers := Litex.Set.ofType __Marker`. An element of
`__Marker` is automatically in `Markers` via `Litex.In.own`. A proper subset,
such as the nonzero reals, is instead emitted with `Litex.setBuilder`, whose
carrier is a subtype and therefore does not collapse back to all reals.

Build with:

```sh
lake build
```

The example file prints each tracer theorem's Lean axiom dependencies and
contains a checked negative probe showing that the standard header does not
install a `Bool`-to-`Nat` bridge. This project declares no new Lean axioms.
The numeric examples inherit Mathlib's ordinary foundational dependencies for
`ℝ` and `ℂ` (`propext`, `Classical.choice`, and `Quot.sound`); the independent
finite-carrier example has no axiom dependencies.

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
it can be the carrier of `Litex.Set.{1}`. `SetSystem.lean` compiles this exact
use probe. Only the real-comparison layer is confined to ordinary `Type`, since
its representatives are Mathlib values in universe zero.

Function spaces, application, compiler IR, verifier evidence, FactIds,
well-definedness DAGs, set union/intersection/power set, and production
code-generation are not implemented yet.
