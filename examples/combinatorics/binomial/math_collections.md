# Pascal recursion and row properties

The natural construction has a zero-column value1, a zero-row value0 at all
positive columns, and the Pascal step decreasing the row index. A row-wide
induction proves entries above the diagonal vanish. Diagonal and first/two
column formulas follow. Row-wide symmetry and positivity support penultimate
entries and strict row monotonicity. These are the actual proof dependencies;
private row invariants stay inside source proofs.

The generic consumer uses all nine source theorems and independently checks
natural codomain, arbitrary-row column0, positive zero-row columns and the full
Pascal identity. In particular, n=0 and k=1 remain legal. Strict row order
requires k>0 and k<=n+1; column0 stays1, and two entries sufficiently far above
the diagonal stay0. The actual caller checks both boundaries.

Imported function definitions are released explicitly before applying them.
The separate negative consumer omits only that step and confirms failure at
its final call. Mathematical domain and missing-hypothesis controls first run
the same complete positive39-statement prefix.

The combinatorial subset-counting interpretation, factorial formula, row sums
and binomial theorem are separate later mathematical tasks.
