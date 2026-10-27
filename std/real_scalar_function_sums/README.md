# Finite sums with one vector input

Import as `MultiSums = real_scalar_function_sums`, alongside
`Sums = real_function_sums` for numeric prefix values. This optional module
imports real_function_sums and real_multivariable.

`\scalar_function_prefix_sum<n,D,count>(terms,m)` returns exactly D→R, with
n∈N+, D⊆cart_n(R,n), a finite family of complete functions on D, and m∈0..count.
There is one vector argument and a real output. It is distinct from the unary
real constructor, and does not convert R to cart_n(R,1).

`scalar_function_prefix_partial(n,D,count,terms,values,p,axis,m)` consumes the
used partial-derivative candidates and a positive two-sided coordinate
neighborhood in D. Its result is the corresponding partial of the sum, with the
numeric Sums prefix as value. It preserves D, and unused tail candidates are not
required. `scalar_function_prefix_continuous_interior(n,D,count,terms,p,m)`
consumes each used continuity fact and an explicit Euclidean neighborhood at p.
That sufficient interior theorem does not claim arbitrary relative-domain
continuity. Zero/successor value thms and a checked index-inclusion dependency
complete the five source thms and one function template.

No native Obj/Fact, BT, strategy, trust, axiom or state is added. Arbitrary relative
domain continuity, vector-valued sums, infinite series, gradients and higher
partials of these sums are not implemented here.
