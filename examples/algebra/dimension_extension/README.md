# Guarded finite dimension and ordered basis extension

The primary real-plane example computes dimension 2, proves (e1) independent
by appending e1 to the empty list, and extends that nonempty prefix to a basis.
It proves that the returned basis has length 2 and still starts with e1, then
uses the existing unique-coordinate interface at (3,4). No particular second
vector or coordinates are selected. model.lit reuses the checked lecture
prefix through the standard plane basis, adding one named export of that result.

scalar/main.lit computes real-line dimension 1 and extends an empty prefix.
zero/main.lit computes dimension 0 and extends the empty zero-space prefix.
The original field/space contexts come from the existing basis examples.
contracts.lit independently calls all ten new theorems over arbitrary supplied
fields and checks both construction carriers.

The value call is \Algebra::dimension::finite_dimension<K,F,V>(X), requiring
known finite-dimensionality. Appending is the complete finite sequence
\Algebra::basis_extension::append_vector<V,m,u,x>, of length m+1. Scalar
ordering, a default basis and operation overloading are not introduced.

Run python3 examples/algebra/dimension_extension/check.py after a release build.
It checks six positive files, sixteen final-statement rejections, actual
archive/shared-data imports and complete std/WiX equality. Missing domains or
mathematical hypotheses, wrong dimensions/sizes, invalid append indices and a
concretely changed first entry reject. All maintained source is trust-free.
General rank-nullity and further course lanes remain separate work.
