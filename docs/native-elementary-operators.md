# Native elementary operations

Litex has native objects for complex conjugation, reciprocal trigonometry,
real hyperbolic functions and set symmetric difference. These are ordinary
Litex spellings; this feature does not parse raw LaTeX commands.

| Object | Domain | Defining equation / result |
| --- | --- | --- |
| `conj(z)` | `z in C` | `re(z)-i*img(z)`, in `C` |
| `sec(x)` | `x in R`, `cos(x)!=0` | `1/cos(x)`, in `R*` |
| `csc(x)` | `x in R`, `sin(x)!=0` | `1/sin(x)`, in `R*` |
| `sinh(x)` | `x in R` | `(exp(x)-exp(-x))/2`, in `R` |
| `cosh(x)` | `x in R` | `(exp(x)+exp(-x))/2`, in `R+` |
| `tanh(x)` | `x in R` | `sinh(x)/cosh(x)`, in `R` |
| `coth(x)` | `x in R`, `x!=0` | `cosh(x)/sinh(x)`, in `R*` |
| `sech(x)` | `x in R` | `1/cosh(x)`, in `R+` |
| `csch(x)` | `x in R`, `x!=0` | `1/sinh(x)`, in `R*` |
| `sym_diff(A,B)` | Both objects are well-defined in Litex's pure-set model | `union(set_minus(A,B),set_minus(B,A))` |

These ten spellings are reserved object names. They cannot be declaration or
parameter names. `compose` and `restrict` are deferred.

```litex
conj(3-4*i) = 3+4*i
forall z C:
    conj(conj(z)) = z
    z*conj(z) = C_abs(z)^2

sec(0) = 1
forall x R:
    cos(x)!=0
    =>:
        sec(x)*cos(x) = 1
        sec(x)^2 = 1+tan(x)^2

forall x R:
    cosh(x)^2-sinh(x)^2 = 1
    tanh(x) = sinh(x)/cosh(x)
forall x R*:
    coth(x) = cosh(x)/sinh(x)

forall A set:
    sym_diff(A,A) = {}
1 $in sym_diff({1,2},{2,3})
not 2 $in sym_diff({1,2},{2,3})
sym_diff({1,2},{2,3}) = {1,3}
```

The current builtin equations cover conjugation's coordinates, involution,
arithmetic, natural powers and modulus; sec/csc reciprocal, Pythagorean,
parity, period and complement relations; hyperbolic definitions, parity,
addition, double angles and basic reciprocal identities; and symmetric
difference's definition, commutativity, associativity, empty/self identities,
cancellation and distribution of intersection. Each equality checks both
operands' domains first. Builtin equation matching preserves native operands;
it cannot cancel an undefined synthetic operand to justify a rule.

For example, `csc(0)`, `coth(0)` and `conj({1})` fail domain checks, including
inside `0*coth(0)`. The false statement `cosh(0)=0` is rejected. A real-input
check remains necessary even for a nonzero argument: `coth(i)` is undefined.

Symmetric-difference membership checks the exclusive alternatives `in A,
not in B` and `not in A, in B`. Nonmembership checks `in both` or `in neither`.
Direct finite enumeration is currently provided for lists whose entries have
exact rational values; unknown symbolic overlaps are not guessed.

The remaining roadmap includes hyperbolic range inequalities, general
monotonicity/sign transport, realness reflection from a fixed conjugate,
and symmetric-difference subset/disjointness/cardinality laws. See the
[phase-1 plan](../plans/litex-latex-phase-1.md) for the complete inventory;
the inventory is broader than the current builtin coverage.

LaTeX output preserves these objects, including `\overline{z}` and
`A\triangle B`. As usual, `-latex` is parse-only and reports `verified: false`.
Lean replay for these new objects is not implemented; `-lean` rejects the
unsupported proof instead of emitting a claimed verification.

Runnable acceptance files:

- [Conjugation](../examples/proof_nodes/equal/by_builtin_rule/complex_conjugation.lit)
- [Reciprocal trigonometry](../examples/proof_nodes/equal/by_builtin_rule/reciprocal_trigonometry.lit)
- [Hyperbolic functions](../examples/proof_nodes/equal/by_builtin_rule/hyperbolic_functions.lit)
- [Symmetric difference](../examples/proof_nodes/equal/by_builtin_rule/symmetric_difference.lit)

Executable false/domain, substitution, parser, output and proof-evidence
controls live in [the focused Rust tests](../tests/unit/execute/native_latex_operations/tests.rs).
