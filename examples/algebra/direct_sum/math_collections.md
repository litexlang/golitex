# Direct-sum example design

The standard plane and scalar field are reused exactly. Horizontal/vertical
axes first give a unique decomposition with projections(3,4)->(3,0)/(0,4).
The diagonal plus vertical axis gives an oblique split(3,4)->(3,3)/(0,1),
showing that no orthogonality or standard-coordinate assumption is present.
Each example proves the actual two subspace facts, full sum and zero
intersection before selecting a decomposition or evaluating a projection.

The source predicate internal direct sum follows from unique decomposition
and implies it. Pair selection follows that unique existence. Public
projection reconstruction uses V->V functions rather than asking an imported
header to infer the ambient type of a raw selected tuple coordinate.

The generic contracts retain arbitrary fields/spaces and all source domains.
Dimension callers first prove inherited finiteness, then apply the guarded
formula. Full/zero and zero/full preserve legitimate zero summands; the
inherited zero ambient space permits both summands to be zero. A linear
idempotent's range/kernel gives another direct sum without any finite basis.

Nearest rejected forms omit sum/subspace/intersection obligations, omit
equality of component sums, omit selected-dimension domains, or omit
linearity/idempotence. Concrete controls change the oblique component,
reverse the ordered pair or apply a plane projection to a triple. Every
control isolates its final statement. No control failure substitutes for the
separately proved negative mathematical statement about repeated axes.
