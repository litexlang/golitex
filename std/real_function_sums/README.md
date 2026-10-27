# Finite real function sums

Import as `Sums = real_function_sums`. No other std package is imported.
All interfaces are source definitions/theorems in Sums::main; there is no new
native Obj, Fact, BT, strategy or runtime state.

`\finite_real_prefix_sum<count>(values,m)` is a real number: count is natural,
values is a complete real function on1..count and m is in0..count. Its definition
is finite_set_sum(closed_range(1,m),values). Zero is the empty prefix. The source
zero/successor theorems and finite_real_prefix_sum_index_equal make computation
and equal-index transport explicit.

`\unary_function_prefix_sum<D,count>(terms,m)` returns a complete function D→R,
where D⊆R and terms maps1..count to complete functions D→R. It sums the first m
functions pointwise, retaining exactly D. Equivalent finite_seq function families
are accepted by the existing fn/finite_seq contract. No implicit domain
restriction or extension occurs.

`unary_function_prefix_derivative(D,count,terms,values,p,m)` consumes p∈D, a
positive two-sided real neighborhood in D, and each used summand's derivative
candidate values(j), for j≤m. It proves the sum's candidate with value
\finite_real_prefix_sum<count>(values,m). Unused tail derivatives are not needed.
Even the empty sum needs that neighborhood under the existing derivative contract.
`unary_function_prefix_continuous(D,count,terms,p,m)` consumes continuity of each
used term at p and proves ordinary relative continuity of the sum, without an
interior premise. Zero/successor value theorems expose the returned function.

The module has two function templates and eleven top-level source thms. Four
numeric support facts handle integer-prefix inclusion, nonnegative prefix
splitting, real aggregate recurrence and real carrier membership. Proof-local
induction invariants and equality lemmas are scoped inside their source thms.
There is no trust or axiom. Infinite function series, uniform convergence and
higher derivative sum rules are outside this module.
