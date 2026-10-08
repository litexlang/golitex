# Litex object model for Lean: objects and semantics first

The current design task is to specify what exists: the representations of Litex objects, their mathematical interfaces and their basic semantic laws. Preserve native numeric values and the useful legacy Litex object-model concepts. All other constructions use Litex-owned representations and semantic operations; ordinary Lean/Mathlib structures are external adapter views. Do not preserve its execution or proof-search pipeline. The current equality-class machinery owns equality evidence; translating that evidence belongs to a later compiler stage.

This is a proposed object-model contract, not an implemented Core. Native numeric values and Litex-owned nonnumeric representations/operations are fixed as the baseline. The separate Num proposal is withdrawn. No Rust AST, verifier, Runtime or generated Lean file is changed by this design.

## Objects and facts

A source object has a Lean representative `a : α`; compiler-created nonnumeric constructions use Litex-owned representations. Its mathematical classifications remain propositions. Learning `In a R` and later `In a C` leaves a and α unchanged. There is no universal public target Obj box and no source set of all objects.

The three basic facts are:

```lean
-- Semantic interface sketches; interpretation and universes are suppressed.
Same a b : Prop
In a A : Prop
IsSet a : Prop
```

Same means source equality. All Litex mathematical predicates and constructions respect it; both arguments of membership can be replaced using equality. Every well-defined source object is a set, including numbers, functions, tuples and standard sets. Host typing alone does not prove these semantics. How equality classes produce the corresponding Lean proof is outside this object inventory.

A generic `have A set` keeps a representative A and an IsSet fact. A checked Litex set view exposes its member interface; an external adapter may additionally expose a native element carrier. It does not turn the original source parameter into a backend collection type.

## Representation inventory

| Source family | Representation and mathematical interface |
| --- | --- |
| Identifier | A generic representative or Litex-owned alias; its host type does not exhaust its source properties |
| Number, i, e, pi | Native Mathlib numeric values; preserve reviewed numeral lowering, including retained complex-valued numerals |
| N/Z/Q/R/C and signed/nonzero variants | Litex set objects with internal membership laws; adapters expose numeric carriers and refined native views |
| Arithmetic, integer, trig, exponential and complex operators | Litex-owned operations such as add/div/sin; preserve their mathematical domains and values, with proved native bridges |
| Finite sets, bounded builders and ranges | Litex-owned constructors with explicit membership laws; interval endpoints retain the source convention |
| Union, intersection, difference, powerset and family operations | Set constructors with their own member characterizations and boundedness requirements |
| Cartesian products, tuples and sequence spaces | Litex-owned product/tuple/sequence objects; tuples use their one-based finite-function meaning; native products are adapter views |
| Function spaces, function values, application and range | The distinct interfaces specified below |
| Iteration and finite-set statistics | Values of mathematically defined sums/products/folds/cardinality/extrema, with their precise domains |
| Structs and fields | Litex definition-owned objects, field access and mathematical laws; native records are adapter views |
| Template instances | Instantiated declaration/object families preserving their source definition identity |

Litex.Set is an internal set representation, not the source classification of every set object. Numbers keep their native values. Generated/internal arithmetic stays behind Litex.add/sub/mul/div and the other Litex operations. Numeric result storage and native implementations do not authorize replacing those internal operations by raw Mathlib expressions. The exact concrete expression carriers remain part of the per-family design, not a reason to bypass the Litex interface.

## Internal operations receive their WD proofs

Litex-owned operations in Lean must explicitly consume their source admissibility proofs. The source verifier discovers the evidence; compilation supplies its Lean proof terms. A constructor or call must not search for the premises or infer them from the host type. Earlier proof-free operation spellings were incomplete shorthand.

```lean
-- Proposed invocation contracts; names are not implemented declarations.
-- haC : Litex.In a Litex.C
-- hbC : Litex.In b Litex.C
-- hb0 : ¬ Litex.Same b (0 : ℂ)
Litex.add a b haC hbC
Litex.div a b haC hbC hb0
```

Each child object's construction/use must also account for its recursive WD obligations. IsSet alone does not supply numeric membership, nonzero conditions or a function guard. The complete per-family interface must carry all applicable premises, not only the examples above.

Proof parameters are not additional mathematical operands or source function arguments. Changing the proof of the same premise must not change the represented value. In particular, a two-argument source call remains a two-argument application layer even when its Lean interface also receives function membership, input memberships and guard proofs.

For an internal function definition, construct the body under its parameter memberships and guards, deriving any required C-memberships from R-memberships through actual proofs. For application, pass the function-space membership and every instantiated domain premise to the Litex application interface. External native adapters come afterward and do not replace this proof-bearing internal contract.

## Four function concepts

Current Rust uses these names:

- FnSet is a set of functions satisfying a signature.
- AnonymousFn constructs a function value from a signature and expression. Named and opaque functions are also function values represented by identifiers.
- FnObj is an application expression: its head and ordered argument groups describe `f(a,b)(c)`.
- FnRange is the actual image of a function.

This distinction follows [the current object declarations](../src/ast/obj.rs), not an old compiler implementation. A function value may also come from a previous application, a field or a tuple. Its internal representation is Litex-owned; a native function is exposed only by a reviewed external adapter.

## A function signature describes its complete domain

For one source application layer, retain the ordered parameter sets, all domain guards and the return set. The parameter sets and return set are fixed relative to the signature's own binders; guards and the defining expression may use those binders. The current [parameter contract](../src/ast/param.rs) specifies this restriction; dependent-looking comments on FnSet in obj.rs are stale.

For example:

```litex
# Interface example; no new execution was performed for this design.
fn(x R, y R: y != 0) R {x / y}
```

Its internal function object retains the source signature, guard and Litex body operation:

```text
# Proposed constructor notation, not compilable Lean declarations.
f := Litex.fn2
       domains: R, R
       guard:   not Same(y, 0)
       returns: R
       body:    Litex.div x y hxC hyC hy0
```

Inputs remain generic representatives with membership facts. The guard belongs to the complete mathematical domain. The return R is an output upper bound, not necessarily the image or an identity tag attached to the graph. The definition must supply the body's WD proofs under the parameter memberships and guard, including hxC/hyC derived from real membership and hy0. The constructor does not discover these proofs.

## Function values are Litex-owned objects

Provide an internal Fn representation, function-space constructors, function construction and application. Their public contract retains the domains, guards, return bound and internal body, without turning the primary representation into a native subtype arrow.

For an anonymous function, its defining law relates internal application to the instantiated internal body. Under the exact admissibility premises for the example:

```text
Same (Litex.apply2 f a b hf haR hbR hb0) (Litex.div a b haC hbC hb0)
In (Litex.apply2 f a b hf haR hbR hb0) R
IsSet (Litex.apply2 f a b hf haR hbR hb0)
```

These are mathematical contracts to prove in Lean, not added project axioms. The concrete binder/body representation and proof-independent application implementation still need a complete definition. Generic source representatives remain unchanged; numeric facts do not replace them by ℝ binders.

Function identity is exact graph identity: equal complete domains and semantically equal values everywhere. Different return upper bounds can describe the same function. Empty complete domains give the empty graph, preserving the source empty-function/empty-set identity. The n-ary graph-key encoding still needs a source-compatible construction before implementation; preserving application layers alone does not select that encoding.

The native expression below belongs exclusively to an external function adapter:

```lean
-- Optional native adapter view; NOT the Litex internal function representation.
{p : ℝ × ℝ // p.2 ≠ 0} → ℝ
```

Prove that this view represents the internal function and that its native division agrees with Litex.div on admitted inputs. A native view must not become an additional source restriction or the primary construction path.

## FnObj denotes the application result

FnObj contains a head and a list of argument groups in the current AST. Interpret those groups sequentially as applications of mathematical function values:

```text
f(a,b)    = one application layer with two argument positions
f(a)(b)   = two application layers
f(a,b)(c) = apply f to a,b; apply the returned function to c
```

Each layer requires its own callable interface, exact arity, argument memberships and instantiated guards. These are the admissibility conditions for the expression. This object-model document does not specify how the verifier finds their proofs.

Represent the application through Litex-owned application operations/objects. Its mathematical result belongs to the declared return set and can be a number, set, function or another supported object. Internal application consumes generic representatives and their exact admissibility evidence. It must not first rewrite the source function into a native arrow as its required public interface. Application respects equality of the function and arguments and does not depend on the selected admissibility proof or adapter view.

For `fn(x R) R {x + 1}`, the internal body uses Litex.add x (1 : ℂ) hxC hOneC. Under In a R, its defining law relates proof-bearing internal application to Litex.add a (1 : ℂ) haC hOneC. Result membership and sethood are internal facts. An external real-function adapter subsequently exposes ordinary real addition with a proved correspondence law.

An opaque function has application and return membership but no invented evaluation formula. FnRange denotes the actual image, not the whole written return set.

## Basic semantic examples

The initial contract includes:

```text
1 = 1                 -> Same (1 : ℂ) (1 : ℂ)
$is_set(1)            -> IsSet (1 : ℂ)
have a C; a = a      -> generic a with C-membership, then reflexivity
x in R               -> x in C without changing x's host type
fn(x R) R {x+1}(2)   -> Litex application with the internal add-body law
f(a,b)(c)            -> two retained application layers
```

The numeric source baselines and four retained Lean library interfaces were checked earlier: generic reflexivity, generic R-to-C, complex one reflexivity and one-in-R. Their Lean 4.31.0 axiom reports contained only propext, Classical.choice and Quot.sound. The function shapes in this document are proposals grounded in current source contracts, not new kernel-checked implementations.

The next design deliverable is the per-family Litex-owned object contract: representation, construction/admissibility conditions, result membership, sethood, equality meaning and external native adapter. Equality-class proof translation, current Result replay, source capture and compiler execution follow once these interfaces are fixed. Historical feasibility and legacy audits remain in [the broader design](litex-to-lean-design-2026-10-07.md); they do not dictate a replacement proof pipeline.
