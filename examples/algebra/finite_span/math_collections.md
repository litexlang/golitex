# Mathematical organization

The examples use the shared field, vector-space and finite-span exports. The
scalar-line instance has the usual real operations. Its trace starts at zero,
adds `2*1`, then `3*4`; the partial-sum theorem identifies the selected result
with the last trace value. No local copy of the generic existence/uniqueness,
coefficient algebra or span-closure proof is introduced.

Candidate value, existence, uniqueness and selected value are distinct roles.
The selector applies to exact-length ordered coefficient/vector lists. Their
indices run from one to n, while trace indices run from zero to n. Empty lists
therefore have the single trace value zero. Set extensionality and the shared
empty-value theorem establish that the empty span is precisely `{zero}`.
Repeated list entries remain valid; the model is not a set of directions.

The singleton vector-space example retains a nontrivial scalar field but has
only vector zero. All coefficient combinations still exist and give zero.
This distinguishes the field's zero-versus-one requirement from the vector
space's allowed zero dimension.

Zero/add/neg/smul coefficient constructions remain values/functions with exact
finite_seq carriers. A named carrier theorem supplies the imported zero list's
type; a named defining-property theorem supplies the selected result's candidate
relation. Imported declarations do not merge the producer's ambient generated
facts. These interfaces let consumers use the checked abstraction directly.

The generic contract file checks every promoted theorem and both import-facing
definition consequences. The concrete examples and executable negatives check
actual values, domains, trace recurrence and linearity requirements independently
of those contract wrappers. They establish a reusable finite-combination slice,
not general basis existence or a dimension selector.
