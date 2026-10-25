# Rank-nullity consumer mathematics

The inherited image uses target addition and scalar multiplication restricted
to fn_range(T). The inherited kernel uses source operations restricted to
preimage(T,target.zero). Both are nonempty subspaces for a linear map. Their
selected dimensions require their own finite-dimensional evidence.

Finite source implies both dimensions exist. Extend a finite kernel basis to a
source basis without changing its prefix. The image of the remaining tail spans
the image because the prefix is killed, and is independent because every kernel
vector is in the prefix span. The three basis lengths yield rank+nullity=dim V.

The real-plane projection supplies an explicit rank-one image basis. The zero
map and identity exercise rank-zero and nullity-zero boundaries through empty
bases. Separate finite-list checks include two empty pieces and preserve the
exact 1-based index domain. Missing finiteness or linearity is never replaced by
trust, a narrower target, or an arbitrary dimension default.
