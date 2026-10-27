# Real regularity on actual open domains

Import this optional source module with `Reg = real_regularity`. Its namespace is
`Reg::main`; it imports `real_multivariable` and adds no native Obj, Fact, BT,
strategy or runtime state.

`is_unary_c_k_on_open(D,k,f)` concerns a complete function from an open subset D
of R to R. `is_scalar_c_k_on_open(n,D,k,f)` concerns a complete function from an
open subset D of cart_n(R,n) to R, with one vector argument. These are separate
propositions. The vector interface does not reinterpret a unary real function,
introduce n positional arguments or assert vector-valued regularity.

Both predicates require ordinary continuity of f. At every positive order
1 through k, they also require derivatives everywhere on exactly D and continuity
of the canonical derivative functions on D. The scalar predicate quantifies
every ordered coordinate path of that length. A continuity clause's explicit
existence premise licenses the selected function; the same existence is also
required unconditionally. `is_unary_smooth_on_open(D,f)` and
`is_scalar_smooth_on_open(n,D,f)` mean all finite k.

The `_on_open` condition applies at k=0 too. Arbitrary-domain relative continuity
remains available through the existing ordinary continuity predicates. An
isolated domain can support zero-order evaluation without satisfying this open
regularity class. The empty open domain is allowed and supplies no point value.

Source constructors and consequences:

- `unary_c_k_from_profiles(D,k,functions)` checks a supplied continuous derivative
  chain on D, including its original function at stage0.
- `is_continuous_ordered_partial_on(n,D,k,f,path,g)` states that a supplied complete
  function g on D gives the ordered derivative candidate at every point and is
  continuous there. `scalar_c_k_from_continuous_candidates(n,D,k,f)` consumes such
  a function for each positive order and path. It does not choose one silently.
- `unary_c_zero_from_continuity/2` and `scalar_c_zero_from_continuity/3` consume
  openness and ordinary continuity. `unary_c_k_lower_order/4` and
  `scalar_c_k_lower_order/5` lower k to any m in0..k, including0.
- `unary_constant_smooth(f,a)` and `scalar_constant_smooth(n,f,a)` check constant
  functions on their respective full spaces, using the supplied pointwise
  formula f(x)=a. They prove all finite orders.
- `ordered_second_partials_swap_c_two(n,D,f,p,alpha,beta,A,B)` consumes C^2,
  reversed length-2 paths, point membership and both candidate values. It returns
  A=B through the existing Schwarz BT. It does not sort arbitrary paths.

The geometry bridge `real_euclidean_interior_native_neighborhood/3` connects the
source distance definition to the native norm-ball neighborhood;
`real_vector_norm_congruence/3` and
`real_euclidean_distance_coordinate_norm/3` supply its explicit equality steps.

The package contains five source propositions and twelve source theorems,
without source trust or axioms. It does not add D^alpha, vector-output smoothness,
a higher total multilinear derivative, general mixed-path permutation or an
automatic differentiability/continuity search strategy. Examples and focused
installed acceptance are in examples/real_analysis/regularity; verification
receipts are maintained in the local native-analysis inventory.
