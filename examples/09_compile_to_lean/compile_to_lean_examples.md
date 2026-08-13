# Litex-to-Lean universal-object examples

This is the consolidated executable input ledger for the replacement compiler.
Each `litex` fence is compiled independently. Generated output must use one
`LitexObject` ABI and must not contain native numeric binders, `Set ℝ`, carrier
unification, widening, or downcast logic.

## membership_wd

One object begins with complex membership, gains real membership through a
checked equality proof, and is then accepted by a function whose declared
domain is `R`.

```litex
forall a C, f fn(x R) R:
    a = 1
    =>:
        1 $in R
        a $in R
        f(a) = f(a)
```

Required generated shape:

```lean
(a : LitexObject)
(litex_param_fact_1 : Litex.In a Litex.C)
theorem well_defined_fact_3 ... : Litex.In a Litex.R := ...
f [a] (Litex.fnSetApplicable ... (well_defined_fact_3 ...))
```

The same source without a proof of `a $in R` is a negative Rust regression and
must be rejected before Lean emission.

## set_parameter

Both a standard-domain parameter and a set parameter are ordinary
`LitexObject` values. Their declarations contribute different propositions;
neither declaration changes the object's Lean type.

```litex
forall a R, b set:
    a = a
    b = b
```

Required generated shape:

```lean
(a : LitexObject)
(litex_param_fact_1 : Litex.In a Litex.R)
(b : LitexObject)
(litex_param_fact_2 : Litex.IsSet b)
```

## derived_set_predicates

`nonempty_set` and `finite_set` parameters are still universal objects. Their
target predicates are definitions over the primitive `IsSet` and `In`
relations, not independent semantic axioms. `Set.Finite` is used only to state
that the Lean view of one object's `In`-extension is finite; it does not turn a
Litex set into a Lean `Set` value.

```litex
forall s nonempty_set, t finite_set:
    s = s
    t = t
```

Required generated shape:

```lean
namespace Litex

def IsNonemptySet (s : LitexObject) : Prop :=
  IsSet s ∧ ∃ x : LitexObject, In x s

def IsFiniteSet (s : LitexObject) : Prop :=
  IsSet s ∧ Set.Finite {x : LitexObject | In x s}

end Litex

(s : LitexObject)
(litex_param_fact_1 : Litex.IsNonemptySet s)
(t : LitexObject)
(litex_param_fact_2 : Litex.IsFiniteSet t)
```

The `IsSet` conjunct is the boundary: an arbitrary object whose `In`-extension
happens to be finite is not thereby a Litex finite set. Empty sets remain
finite, so `IsFiniteSet` deliberately does not imply `IsNonemptySet`.

## known_forall

An explicit trusted source fact becomes one target axiom. Its concrete use is
not another axiom: the compiler cites the retained theorem `FactId` with the
object, membership proof, and domain proof in order.

```litex
abstract_prop marked(x)

trust forall x R:
    x = 1
    =>:
        $marked(x)

forall a R:
    a = 1
    a != 0
    =>:
        $marked(a)
```

Required generated shape:

```lean
axiom marked : LitexObject → Prop
axiom fact... : ∀ (x : LitexObject) (_ : Litex.In x Litex.R) (_ : x = 1), marked x
theorem fact... : ∀ (a : LitexObject) ... , marked a := by
  ... exact fact... a litex_param_fact_1 litex_domain_fact_1
```

## builtin_theorem

The verifier's not-equality-symmetry certificate calls a real theorem in the
builtin library. The concrete rule is not an axiom.

```litex
forall a, b C:
    a != b
    =>:
        b != a
```

Required generated shape:

```lean
theorem Litex.BuiltinRules.notEqualSymmetry ... := by ...
... exact Litex.BuiltinRules.notEqualSymmetry litex_domain_fact_1
```

## known_equality_path

Known equality remains an equivalence class for fast Litex lookup, while the
compiler certificate retains the exact direct `FactId` edges selected for the
proof. Reversing one edge emits `Eq.symm`; joining two edges emits `Eq.trans`.

```litex
forall a, b set:
    a = b
    =>:
        b = a

forall a, b, c set:
    a = b
    b = c
    =>:
        a = c
```

Required generated shape:

```lean
... exact (Eq.symm (litex_domain_fact_1))
... exact (Eq.trans (litex_domain_fact_1) (litex_domain_fact_2))
```

The malformed-certificate regression replaces the retained equality `FactId`
with an unavailable identity and requires strict emission to fail before Lean.

## exact_application_layers

A comma-separated source group remains one list application. A function-valued
return creates a second genuine list application and obtains its next
function-set membership from `Litex.fnSetResult`.

```litex
forall f fn(x, y, z R) R:
    f(1, 2, 3) = f(1, 2, 3)

forall g fn(x R) fn(y R) R:
    g(1)(2) = g(1)(2)
```

Required generated shape:

```lean
f [1, 2, 3] ...
(g [1] ...) [2] ...
Litex.fnSetResult ...
```

The executable negative regression keeps `f(1)(2, 3)` rejected when `f` was
declared in the single-layer set `fn(x, y, z R) R`.

## arithmetic_forall_wd

A nested source `forall` remains a proposition over `LitexObject`. Its body
uses universal-object subtraction, and each application cites the WD fact
attached to that exact source occurrence. The concluding instance then replays
the verifier's retained rational-normalization certificate.

```litex
forall f fn(x R) R:
    forall y R:
        f(y) = f(y - 1)
    =>:
        f(2) = f(1)
```

Required generated shape:

```lean
(y : LitexObject)
(litex_nested_param_fact_... : Litex.In y Litex.R)
Litex.sub y 1
Litex.BuiltinRules.realSubClosure ...
litex_domain_fact_... (Litex.add 1 1) ...
```

The malformed-certificate regression changes a retained source occurrence ID
and requires strict emission to fail instead of selecting another textually
equal application.

## Gates

```text
cargo test --release universal_examples_ -- --nocapture
LITEX_LEAN_PROJECT=/absolute/path/to/mathlib LITEX_LAKE=/absolute/path/to/lake cargo test --release universal_examples_compile_with_mathlib -- --ignored --nocapture
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_litex_object_abi.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_set_predicate_definitions.lit
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_known_equality_path.lit
```
