# Common Obj relations: final audit, 2026-10-05

Follow-up: the user subsequently authorized implementing the selected simple
interfaces. The [completion record](../proof_nodes/experience/problem_notes/common-obj-relations-2026-10-05.md)
tracks gcd/lcm divisibility, the checked factorial/product theorem, both selected
sine intervals, and positive nonunit logarithm-base relations. The report below
retains the original audit snapshot and its original failure observations;
it is not a claim that all 81 relations were rerun after implementation.

Task context: the user requested a final review of common Obj properties,
emphasizing relationships between objects after their individual defining rules
were supplemented. This is a relation audit and a collection of checked author
routes; it makes no Rust, AST, trust, or mathematical-domain changes.

Most selected relationships are already provable. The clearest remaining
interface candidates are **gcd/lcm divisibility**, **factorial as a product**, and
**trigonometric interval order/sign**. A second concern is exposing existing
bridges as convenient named theorems rather than repeatedly rebuilding them.

## Evidence and scope

- The repository's `coverage.json` inventory contains 99 Obj entries. The
  groups below account for every entry; 81 representative relation goals were
  tested. This is not an enumeration of every pair or every mathematical law.
- On the final rebuilt binary, 38 original forms pass directly. Another 35
  have checked routes for the same mathematical statement, including corrected
  author syntax and the canonical inclusion-exclusion formula. Three entries
  have a checked restricted domain only; five remain unproved in this audit.
- The 38 explicit author routes are saved in
  [common_obj_relation_author_routes.lit](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit).
  They use independent discarded sketches; this file is a runnable example,
  not an exported theorem library.
- The combined 75-frame cold gate passed. The final Cartesian-product route
  subsequently passed both session and cold checks. The promoted 38-route file
  also passed `-strict -f`, with exit `0` and top-level `success: true`.
- Eight nearby false or illegal formulas rejected, with nonzero exit and
  `success: false`. They cover quotient divisor sign, real/complex modulus,
  min/max, floor/ceil, square-root domains, coprime domains, empty extrema, and
  the false powerset/union distribution law.
- All sources, failed variants, exact outputs, build fingerprints, and final
  diagnostic probes are in the
  [journal](proof_journals/obj_relations_final_2026-10-05.json).

The first build was stable, but shared source changed during the audit. A
second `cargo build --release --offline --lib --bin litex` succeeded on a stable
source snapshot. The final gates used binary SHA-256
`d54252987afa5ced9324ceb9834ae3aa5fb9d2d9eb7eb12fb984105d13d75ccd`.
The journal retains both snapshots. No whole-repository or whole-Obj regression
gate is claimed.

At record end, seven shared CLI/output/test source files changed again while
the executable remained identical. Their manifest is retained separately.
The verification receipts certify the rebuilt snapshot above; the later
working tree has not been rebuilt or certified by this audit.

## Producer-to-consumer map

| Producer | Consumer | Domain or bridge contract | Final status |
| --- | --- | --- | --- |
| `quot`, `%` | `/`, `floor` | Integer numerator, positive integer divisor; quotient/remainder window determines floor | Checked explicit route |
| `floor`, `ceil` | Integer order, fractional part | Integer adjacency and defining real bounds | Checked explicit routes |
| `sqrt`, powers | `abs`, multiplication, division | Real nonnegative radicands; strictly positive divisor | Available; exact order guards matter |
| `min`, `max` | `abs`, distance, arithmetic | Total real order and two cases | Checked explicit routes |
| `re`, `img`, `C_abs` | Real arithmetic and `abs` | Rectangular reconstruction; nonnegative principal modulus | Available; checked real/complex bridge |
| `exp`, `ln` | `log`, integer powers of `e` | Positive arguments and legal base/divisor facts | Checked; general-base limitations below |
| Set operations | `power_set`, builders, refined carriers | Membership/subset definitions and extensionality | Checked explicit routes |
| Integer ranges | Closed ranges, sums/products | Integer adjacency; legal nonempty aggregate range | Checked |
| Cartesian membership | Coordinates, tuple equality | Tuple reconstruction and coordinate membership | Checked; changed native-call boundary below |
| Sequences | Function spaces, application | One-based indices and exact bounded signatures | Directly checked |
| Functions | Range, arithmetic, elementary functions, composition | Domain/codomain transport | All seven selected probes pass directly |
| Struct fields/templates | Tuples, carriers, callable functions | Structural field order and exact specialization | Field bridge checked; templates reviewed in owning examples |
| `reduce`/finite reduce | `sum`/finite-set sum | Additive operation and identity, exact function carrier | Directly checked |
| Finite-set extrema | Scalar `min`/`max`, union | Finite/nonempty real sets, explicit member and carrier evidence | Checked explicit routes |
| `gcd`, `lcm` | Divisibility expressed by `%` | Universal divisor/multiple property, not merely a numerical bound | Candidate interface; not proved here |
| `factorial` | Range `product` | Positive integer upper endpoint; identity factor function | Candidate theorem; not proved here |

The useful implementation unit is a **bridge theorem** with its domain and
premises. Direct search convenience is a separate choice. For example,
`quot(a,d)=floor(a/d)` is not missing mathematics: the existing remainder bounds,
division/order rules, and floor characterization already prove it.

## Original audit candidates (follow-up linked above)

### 1. Universal gcd/lcm divisibility

The current source has gcd/lcm identities, Euclidean recursion, and order
bounds for common divisors/multiples. Those do not themselves expose the
universal divisibility clauses. Both legal claim probes below reached the
conclusion and failed at `search_proof`.

<!-- litex:skip-test -->
```litex
forall a,b Z,d N+:
    a!=0
    a%d=0
    b%d=0
    =>:
        gcd(a,b)%d=0
```

<!-- litex:skip-test -->
```litex
forall a,b N+,m Z:
    m%a=0
    m%b=0
    lcm(a,b)!=0
    =>:
        m%lcm(a,b)=0
```

Classification: provisional missing reusable interface, not a demonstrated
soundness defect. The lcm nonzero premise was added only to isolate conclusion
search; a complete public theorem should also derive it from positive inputs.
Next action: inspect the existing divisibility owners, choose a general author
theorem or a bounded rule, and verify symbolic positive/negative and zero
boundaries. Do not substitute `d<=gcd(a,b)` or `lcm(a,b)<=m` for divisibility.

### 2. Factorial/product bridge

The defining factorial recurrence exists. This relation is a reusable induction
theorem, not another recurrence rule. Its legal claim probe reaches the equality
and fails at `search_proof`.

<!-- litex:skip-test -->
```litex
forall n N+:
    factorial(n)=product(1,n,fn(k Z) Z {k})
```

Classification: provisional author/library theorem gap. Next action: try an
integer induction using the existing product endpoint recurrence, preserving
the `N+` statement and `Z` identity-function signature. Check `n=1` and an
unrelated/wrong factor function as boundaries. This audit did not execute that induction.

### 3. Trigonometric sign and order on intervals

Inverse compositions on their principal intervals pass. The two ordinary
interval relationships below still reach their conclusion and fail at
`search_proof`. They are the existing LEG35/LEG36 subjects, not new duplicate
issues; see the [central plan](../../plan/src收尾总清单.md).

<!-- litex:skip-test -->
```litex
forall x R:
    0<x
    x<pi
    =>:
        0<sin(x)

forall a,b R:
    -pi/2<=a
    b<=pi/2
    a<b
    =>:
        sin(a)<sin(b)
```

Next action: retain the exact principal intervals and endpoint behavior when
implementing the existing local-rule candidates. A global monotonicity rule
would change the intended mathematics.

### 4. General logarithm bases need a separate completion pass

The change-of-base and base-power probes pass for bases greater than one, with
explicit legal-divisor/base premises. The original `b>0, b!=1` versions are not
closed by those narrower successes: bases in `(0,1)` are legitimate.

The general change-of-base claim first fails well-definedness at
`log(b,a)!=0`; the general base-power claim first fails at `b^n!=1`. Their
bodies cannot establish a premise needed to admit the claim goal itself.
The existing equality owners also have greater-than-one guards. Next action:
derive and expose nonzero/power-not-one carrier facts before the consuming
statement, then check the full positive-base theorem, including `(0,1)`.
This is a partial-domain observation, not evidence that the formulas are false.

## Relationships worth exposing as named theorems

These are proven by the saved author routes and need no new mathematical
primitive merely to become usable:

- `quot(a,d)=floor(a/d)` and `a%d=a-d*floor(a/d)` for `a Z,d N+`.
- `ceil(x)=-floor(-x)`, the floor/ceil gap, fractional-part bounds, and the
  interval characterization of `floor`.
- `abs(x)=max(x,-x)`, `min(x,-x)=-abs(x)`, min/max sum and distance identities,
  and their half-sum formulas.
- `C_abs(x)=abs(x)` on `R`, and the modulus-square coordinate formula on `C`.
- Powerset/intersection, product/union distribution, positive-set builders,
  refined-carrier intersections, and range/closed-range equality.
- Pair-set extrema and the extremum of a union of two nonempty finite real
  sets. The latter proof needs explicit finiteness of the union before using
  its maximum; the former needs explicit member facts for bound consumption.

These candidates should first be organized as named reusable theorems. A short
BT form is justified only by demonstrated repeated caller burden and an
appropriate existing rule/evidence owner.

## Domain and migration observations

- `$coprime` currently takes natural inputs. The initial signed-integer probe
  was ill-defined; `a,b N` with `a!=0` and `gcd(a,b)=1` succeeds using `by def`.
  Changing that domain is a modeling decision, not an ordinary missing rule.
- `quot` requires a positive divisor. Signed modulus support does not make a
  signed-divisor quotient/floor theorem part of the current object contract.
- List-set entries need provable distinctness. The pair-extremum theorem keeps
  `a!=b`; equal inputs can use a singleton without changing this convention.
- `index_cart` is function-valued. Ordinary `cart` contains tuples; a conversion
  requires an explicit encoding rather than asserting the two sets are equal.
- `proj(cart(...),k)` is a factor-view constructor, not the image of an arbitrary
  subset under coordinate projection. Empty-factor image laws cannot be copied
  to it without checking its intended contract.
- The inventory still lists `cart_dim`. During shared source migration,
  `cart_dim` became rejected as a property of a Cartesian set. The previously
  passing `cart_member_from_coordinates` proof call then failed on its generated
  `cart_dim` premise. The same distribution theorem now passes through explicit
  tuple reconstruction/membership. This is a native-consumer migration boundary,
  not missing product-distribution mathematics. The journal preserves both
  binary observations; the audit does not certify the old `cart_dim` fixtures.
- Real exponents, complex logarithm branches, empty indexed-family conventions,
  and arbitrary function/tuple encodings were not added to this task's scope.

## Inventory groups

The table below is a partition of the recorded 99 entries, not a claim that
every relation of every entry has been tested.

<!-- Generated inventory and relation matrix follow. -->

| Group | Count | Recorded Obj names |
| --- | --- | --- |
| Identifiers and literals | 4 | `identifier_plain`, `identifier_with_export_file_id`, `identifier_with_mod_and_export_file_id`, `number` |
| Constants | 3 | `imaginary_unit`, `euler_number`, `pi` |
| Real/arithmetic interfaces | 12 | `add`, `sub`, `neg`, `mul`, `div`, `pow`, `abs`, `min`, `max`, `floor`, `ceil`, `sign` |
| Discrete interfaces | 5 | `mod`, `quot`, `gcd`, `lcm`, `factorial` |
| Elementary functions | 12 | `sin`, `cos`, `tan`, `cot`, `arcsin`, `arccos`, `arctan`, `arccot`, `exp`, `ln`, `log`, `sqrt` |
| Complex interfaces | 3 | `real_part`, `imaginary_part`, `complex_abs` |
| Set operations/formers | 10 | `union`, `intersect`, `set_minus`, `family_union`, `family_intersect`, `power_set`, `index_union`, `index_intersect`, `list_set`, `set_builder` |
| Integer ranges | 2 | `range`, `closed_range` |
| Products/sequences | 9 | `finite_seq_set`, `seq_set`, `cart`, `tuple`, `cart_dim`, `tuple_dim`, `proj`, `obj_at_index`, `index_cart` |
| Function interfaces | 4 | `fn_obj`, `fn_set`, `anonymous_fn`, `fn_range` |
| Aggregates/statistics | 9 | `sum`, `product`, `sum_of_finite_set`, `product_of_finite_set`, `reduce`, `finite_set_reduce`, `finite_set_size`, `finite_set_max`, `finite_set_min` |
| Structures/specialization | 3 | `struct_obj`, `field_access`, `instantiated_template_obj` |
| Standard carriers | 15 | `standard_set_c`, `standard_set_c_star`, `standard_set_n`, `standard_set_n_pos`, `standard_set_q`, `standard_set_q_neg`, `standard_set_q_pos`, `standard_set_q_star`, `standard_set_r`, `standard_set_r_neg`, `standard_set_r_pos`, `standard_set_r_star`, `standard_set_z`, `standard_set_z_neg`, `standard_set_z_star` |
| Real intervals | 8 | `interval_closed_closed`, `interval_closed_open`, `interval_open_closed`, `interval_open_open`, `one_side_interval_lower_closed`, `one_side_interval_lower_open`, `one_side_interval_upper_closed`, `one_side_interval_upper_open` |

## Selected relation matrix

`Direct` means the exact original form passes. `Route` means the same mathematics has a checked explicit route. `Restricted` retains a narrower valid domain; the original general statement remains open. `Open` means this audit found no complete accepted route, not that none exists.

| ID | Family | Goal | Final classification |
| --- | --- | --- | --- |
| D01 | discrete-real | `quot(a,d)=floor(a/d)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L111) |
| R01 | real-scalar | `sqrt(x^2)=abs(x)` | Direct |
| R02 | real-scalar | `sqrt(x)=y` | Direct |
| R03 | real-scalar | `sqrt(x*y)=sqrt(x)*sqrt(y)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L432) |
| R04 | real-scalar | `sqrt(x/y)=sqrt(x)/sqrt(y)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L441) |
| R05 | real-scalar | `sign(x)*abs(x)=x` | Direct |
| R06 | real-scalar | `abs(x)=max(x,-x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L454) |
| R07 | real-scalar | `min(x,-x)=-abs(x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L472) |
| R08 | real-scalar | `min(x,y)+max(x,y)=x+y` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L494) |
| R09 | real-scalar | `max(x,y)-min(x,y)=abs(x-y)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L512) |
| R10 | real-scalar | `min(x,y)=(x+y-abs(x-y))/2` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L534) |
| R11 | real-scalar | `max(x,y)=(x+y+abs(x-y))/2` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L576) |
| R12 | real-scalar | `ceil(x)=-floor(-x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L618) |
| R13 | real-scalar | `ceil(x)<=floor(x)+1` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L627) |
| R14 | real-scalar | `floor(x+n)=floor(x)+n` | Direct |
| R15 | real-scalar | `ceil(x+n)=ceil(x)+n` | Direct |
| R16 | real-scalar | `0<=x-floor(x)` | Direct |
| R17 | real-scalar | `x-floor(x)<1` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L637) |
| R18 | real-scalar | `floor(x)=n` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L646) |
| E01 | elementary | `exp(ln(x))=x` | Direct |
| E02 | elementary | `ln(exp(x))=x` | Direct |
| E03 | elementary | `ln(x)=log(e,x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L195) |
| E04 | elementary | `exp(n)=e^n` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L210) |
| E05 | elementary | `ln(x*y)=ln(x)+ln(y)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L227) |
| E06 | elementary | `ln(x/y)=ln(x)-ln(y)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L258) |
| E07 | elementary | `ln(x^n)=n*ln(x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L314) |
| E08 | elementary | `exp(-x)=1/exp(x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L330) |
| E09 | elementary | `log(a,x)=log(b,x)/log(b,a)` | Restricted: bases > 1; legal divisor premise · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L357) |
| E10 | elementary | `log(b^n,x)=log(b,x)/n` | Restricted: base > 1; powered base != 1 · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L367) |
| E11 | elementary | `sin(arcsin(x))=x` | Direct |
| E12 | elementary | `cos(arccos(x))=x` | Direct |
| E13 | elementary | `arcsin(sin(x))=x` | Direct |
| E14 | elementary | `arctan(tan(x))=x` | Direct |
| E15 | elementary | `arccot(cot(x))=x` | Direct |
| E16 | elementary | `0<sin(x)` | Open |
| E17 | elementary | `sin(a)<sin(b)` | Open |
| D02 | discrete-real | `a=d*quot(a,d)+a%d` | Direct |
| D03 | discrete-real | `quot(a,d)=(a-a%d)/d` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L140) |
| D04 | discrete-real | `a%d=a-d*floor(a/d)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L149) |
| D05 | discrete-real | `gcd(a,b)*lcm(a,b)=abs(a*b)` | Direct |
| D06 | discrete-real | `gcd(a,b)%d=0` | Open |
| D07 | discrete-real | `m%lcm(a,b)=0` | Open |
| D08 | discrete-real | `$coprime(a,b)` | Restricted: natural inputs; `by def` · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L184) |
| D09 | discrete-real | `factorial(n)=product(1,n,fn(k Z) Z {k})` | Open |
| C01 | complex-real | `z=re(z)+i*img(z)` | Direct |
| C02 | complex-real | `C_abs(z)^2=re(z)^2+img(z)^2` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L88) |
| C03 | complex-real | `C_abs(x)=abs(x)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L98) |
| C04 | complex-real | `re(x)=x` | Direct |
| C05 | complex-real | `img(x)=0` | Direct |
| C06 | complex-real | `re(z*w)=re(z)*re(w)-img(z)*img(w)` | Direct |
| C07 | complex-real | `img(z*w)=re(z)*img(w)+img(z)*re(w)` | Direct |
| C08 | complex-real | `C_abs(z*w)=C_abs(z)*C_abs(w)` | Direct |
| S01 | sets-carriers | `intersect(A,union(A,B))=A` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L663) |
| S02 | sets-carriers | `set_minus(A,union(B,C))=intersect(set_minus(A,B),set_minus(A,C))` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L671) |
| S03 | sets-carriers | `power_set(intersect(A,B))=intersect(power_set(A),power_set(B))` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L677) |
| S04 | sets-carriers | `u $in {x R: x>0}` | Direct |
| S05 | sets-carriers | `{x R: x>0}=R+` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L709) |
| S06 | sets-carriers | `intersect(Z,R+)=Z+` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L722) |
| S07 | sets-carriers | `x $in R` | Direct |
| S08 | sets-carriers | `range(a,b+1)=closed_range(a,b)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L727) |
| P01 | products-sequences | `cart(union(A,B),C)=union(cart(A,C),cart(B,C))` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L376) |
| P02 | products-sequences | `p=(p[1],p[2])` | Direct |
| P03 | products-sequences | `p=q` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L419) |
| P04 | products-sequences | `finite_set_size(cart(A,B))=finite_set_size(A)*finite_set_size(B)` | Direct |
| P05 | products-sequences | `seq(R)=fn(n N+) R` | Direct |
| P06 | products-sequences | `finite_seq(R,n)=fn(k closed_range(1,n)) R` | Direct |
| F01 | functions-structures | `f(x) $in fn_range(f)` | Direct |
| F02 | functions-structures | `fn_range(f) $subset R` | Direct |
| F03 | functions-structures | `f(x)=g(x)` | Direct |
| F04 | functions-structures | `f(x)+1 $in R` | Direct |
| F05 | functions-structures | `ln(exp(f(x)))=f(x)` | Direct |
| F06 | functions-structures | `f(g(x)) $in R` | Direct |
| F07 | functions-structures | `p.x=p[1]; p.y=p[2]` | Direct |
| A01 | aggregates | `sum(a,b,f)=finite_set_sum(closed_range(a,b),f)` | Direct |
| A02 | aggregates | `product(a,b,f)=finite_set_product(closed_range(a,b),f)` | Direct |
| A03 | aggregates | `reduce(a,b,f,fn(x,y R) R {x+y},0)=sum(a,b,f)` | Direct |
| A04 | aggregates | `finite_set_reduce(S,f,fn(x,y R) R {x+y},0)=finite_set_sum(S,f)` | Direct |
| A05 | aggregates | `finite_set_max({a,b})=max(a,b)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L6) |
| A06 | aggregates | `finite_set_max(union(S,T))=max(finite_set_max(S),finite_set_max(T))` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L28) |
| A07 | aggregates | `finite_set_size(union(S,T))+finite_set_size(intersect(S,T))=finite_set_size(S)+finite_set_size(T)` | Route (canonical inclusion-exclusion) · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L71) |
| A08 | aggregates | `finite_set_size(set_minus(S,T))=finite_set_size(S)-finite_set_size(T)` | Route · [source](../proof_nodes/equal/by_builtin_rule/common_obj_relation_author_routes.lit#L77) |
