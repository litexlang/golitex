# Set-law proof dependencies

`set_with_member_is_nonempty` supplies the actual member to the existing native
`witness $is_nonempty_set(S) from x` interface. That interface checks membership
and publishes nonemptiness. Finite-product nonemptiness reuses the source law
after constructing its actual selection. No additional native rule or parallel
nonemptiness definition is introduced.

`singleton_union_display` proves both inclusion directions by two membership
cases and then applies native set extensionality. Distinctness belongs to the
displayed set's well-definedness. General unordered pairs already have the
native expression `union({a},{b})`, including equal inputs, so no second pair
constructor is introduced.

`relative_complement_partition` first exposes `A subset X`. The native identity
`union(A,set_minus(X,A))=union(A,X)` and the ambient inclusion give the full
union; the native disjointness law gives the empty intersection. Other Boolean
algebra laws remain available directly from native operations.

`russell_diagonal_outside` forms the actual bounded set
`D={x U:not x in x}`. Under the supposition `D in U`, membership in `D` would
imply nonmembership, so `D not in D`. The two defining membership conditions
then put `D` into itself, a contradiction. This derivation uses no Regularity
or Choice release. It establishes the obstruction to a universal set in the
existing pure-set foundation without asserting unrestricted comprehension.
