# Mathematical organization

A subspace contains every partial sum of a finite combination of its members.
A delta coefficient list places each generator in its own span. Their span is
therefore the least subspace containing them, and membership of each generator
in another span suffices for inclusion of the entire span.

The removed-list relation matches generators before k directly, and those
after k with index shifted by one. The surviving generators give one span
inclusion; the deleted vector's membership supplies the reverse inclusion.
This proves equality for any legal index, including endpoints.

For a dependent positive-length list, the preceding-prefix dependence lemma
produces a removable vector. Prefix generators survive the removal, so their
span lies in the remaining span and the deletion criterion applies. The result
only shortens one list by one. Iterated basis extraction, exchange and invariant
length need separate mathematical proofs; no dimension selector is inferred.
