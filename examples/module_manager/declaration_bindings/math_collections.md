# Declaration binding interfaces

`have fn ident(x R) R = x` introduces a function with a fixed binding identity.
That identity survives the end of its parse scope while its definition and
membership facts remain usable inside the proof. A later file-root function
with the same name has a separate identity and may be exported.

`have by fn_preimage: source from ident(2) $in fn_range(ident)` introduces an
opaque real preimage and the equation `ident(2) = ident(source)`. It depends
on the function signature and verified range membership. The witness's ID
belongs to this declaration and cannot be replaced by a later name lookup.

The module consumer uses `release obj def` to obtain facts about each qualified
function. The two exported functions have the same terminal name and different
formulas. Wrong equations and escaped local names remain rejected. Function
cache records preserve and remap the declaration ID together with body IDs.
