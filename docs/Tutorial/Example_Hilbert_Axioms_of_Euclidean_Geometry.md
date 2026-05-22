# Litex Tutorial: Hilbert Axioms of Euclidean Geometry

Jiachen Shen and The Litex Team, 2026-05-22. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry.md

This example is a good way to see what Litex is designed for. It does not try to build a rich geometric universe into the kernel. Instead, it lets the file introduce the objects and relations it needs, then checks that later statements use those relations consistently.

The important style is:

- domains such as `point`, `line`, and `plane` are objects introduced by the file;
- geometric words such as `between`, `line_through`, and `segment_congruent` are relations;
- axioms are stored as `know` facts;
- uniquely determined objects such as `line_of(A, B)` are introduced from `exist!` statements.

## Primitive Objects

The example starts by introducing primitive domains.

```litex
have point nonempty_set
have line nonempty_set
have plane nonempty_set
```

Litex does not need to know what a point “really is”. It only needs a context where `point`, `line`, and `plane` are valid sets of objects. Later facts give these domains their useful behavior.

For example, the file states that lines and planes are sets of points:

```litex
have point nonempty_set
have line nonempty_set
have plane nonempty_set

know:
    forall l line:
        l $in power_set(point)

    forall alpha plane:
        alpha $in power_set(point)
```

After this, expressions such as `A $in l` become meaningful when `A` is a point and `l` is a line.

## Primitive Relations

Many geometric concepts are introduced as relation symbols:

```litex
abstract_prop line_through(A, B, l)
abstract_prop between(A, B, C)
abstract_prop segment_congruent(A, B, C, D)
abstract_prop angle_congruent(A, B, C, D, E, F)
```

This is one of the clearest features of Litex. A relation does not need an internal computational meaning before it can be used. Its meaning is given by the facts you store about it.

For instance, betweenness can imply symmetry and collinearity because the file says so:

```litex
have point nonempty_set
abstract_prop between(A, B, C)
abstract_prop collinear(A, B, C)

know:
    forall A, B, C point:
        $between(A, B, C)
        =>:
            $between(C, B, A)
            $collinear(A, B, C)
```

Litex is therefore relation-first. It checks whether the relations can be applied, stored, and reused; it does not require each geometric word to have a built-in interpretation.

## Derived Predicates

The file also defines derived predicates using `prop`. This gives a relation a definition in terms of other facts.

```litex
have point nonempty_set
have line nonempty_set

know forall l line:
    l $in power_set(point)

prop collinear(A, B, C point):
    exist l line st {A $in l, B $in l, C $in l}
```

Here `collinear(A, B, C)` is not primitive. It means that there exists a line containing all three points. This shows the difference between `abstract_prop` and `prop`:

- `abstract_prop` introduces a relation name only;
- `prop` introduces a relation name together with facts that define it.

## Unique Objects From Relations

Hilbert-style geometry often says that some object exists uniquely. Litex can turn this pattern into a function-like object.

```litex
have point nonempty_set
have line nonempty_set
abstract_prop line_through(A, B, l)

know:
    forall A, B point:
        A != B
        =>:
            exist! l line st {$line_through(A, B, l)}

have fn line_of as set:
    forall A, B point:
        A != B
        =>:
            exist! l line st {$line_through(A, B, l)}
```

After this, `line_of(A, B)` is the line determined by two distinct points. The name is not magic. It is justified by the `exist!` fact.

The full example repeats this pattern for planes:

- `line_of(A, B)` comes from the unique line through two distinct points;
- `plane_of(A, B, C)` comes from the unique plane through three noncollinear points;
- `plane_of_point_and_line(A, l)` comes from the unique plane through a point and a line.

## Axioms as Reusable Facts

Most of the file is a sequence of `know` blocks. Each block stores reusable mathematical information.

For example:

```litex
have point nonempty_set
abstract_prop segment_congruent(A, B, C, D)

know:
    forall A, B point:
        A != B
        =>:
            $segment_congruent(A, B, A, B)

    forall A, B, C, D point:
        $segment_congruent(A, B, C, D)
        =>:
            $segment_congruent(C, D, A, B)
```

This style is close to textbook axiomatization. You do not need to prove every axiom inside the file; you can record it as a trusted mathematical assumption and then build later statements from it.

## What This Example Teaches

The Hilbert geometry file is useful because it exercises many basic Litex forms in one place:

- `have` introduces domains and objects;
- `abstract_prop` introduces primitive relations;
- `prop` defines derived relations;
- `know` stores axioms and consequences;
- `forall` expresses reusable general statements;
- `exist` and `exist!` express existence and uniqueness;
- `have fn ... as set` turns uniqueness into a named object constructor.

The main lesson is that Litex is not trying to encode the internal meaning of Euclidean geometry into special syntax. It is checking a network of objects and relations. That makes the language convenient for abstract mathematics: once the relations are named and the facts are stated, Litex can reuse them without needing built-in geometric semantics.

## Full Litex Source

The complete example is reproduced below as one block, so the shape of the whole file is visible at once.

```litex
"""
This is a current Litex version of a Hilbert-style axiomatization sketch for
Euclidean geometry.

Compared with the older draft, this version follows the current style:
primitive geometric relations are introduced with `abstract_prop`, while
uniquely determined geometric objects such as `line_of(A, B)` and
`plane_of(A, B, C)` are introduced from `forall ... exist! ...` facts.
"""

# Primitive domains.
have point nonempty_set
have line nonempty_set
have plane nonempty_set

# Lines and planes are sets of points.
know:
    forall l line:
        l $in power_set(point)

    forall alpha plane:
        alpha $in power_set(point)

# Primitive relations.
abstract_prop line_through(A, B, l)
abstract_prop plane_through(A, B, C, alpha)
abstract_prop plane_through_point_and_line(A, l, alpha)
abstract_prop between(A, B, C)
abstract_prop line_intersects_segment(l, A, B)
abstract_prop on_ray(A, B, C)
abstract_prop same_side_of_line(P1, P2, l)
abstract_prop segment_congruent(A, B, C, D)
abstract_prop angle_congruent(A, B, C, D, E, F)
abstract_prop parallel_line(l1, l2)
abstract_prop archimedes_number(A, B, C, D, n)

# Derived predicates.
prop collinear(A, B, C point):
    exist l line st {A $in l, B $in l, C $in l}

prop noncollinear(A, B, C point):
    A != B
    A != C
    B != C
    not $collinear(A, B, C)

prop line_on_plane(l line, alpha plane):
    forall P l:
        P $in alpha

prop four_points_not_coplanar(A, B, C, D point):
    A != B
    A != C
    A != D
    B != C
    B != D
    C != D
    forall alpha plane:
        not A $in alpha or not B $in alpha or not C $in alpha or not D $in alpha

# I1: unique line through two distinct points.
know:
    forall A, B point:
        A != B
        =>:
            exist! l line st {$line_through(A, B, l)}

    forall A, B point, l line:
        $line_through(A, B, l)
        =>:
            A $in l
            B $in l

have fn line_of as set:
    forall A, B point:
        A != B
        =>:
            exist! l line st {$line_through(A, B, l)}

know:
    forall A, B point:
        A != B
        =>:
            $line_through(A, B, line_of(A, B))
            A $in line_of(A, B)
            B $in line_of(A, B)

# I2: every line contains at least two distinct points.
know:
    forall l line:
        exist A, B point st {A != B, A $in l, B $in l}

# I3: there exist three noncollinear points.
know:
    exist A, B, C point st {$noncollinear(A, B, C)}

# I4: unique plane through three noncollinear points.
know:
    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            exist! alpha plane st {$plane_through(A, B, C, alpha)}

    forall A, B, C point, alpha plane:
        $plane_through(A, B, C, alpha)
        =>:
            A $in alpha
            B $in alpha
            C $in alpha

have fn plane_of as set:
    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            exist! alpha plane st {$plane_through(A, B, C, alpha)}

know:
    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            $plane_through(A, B, C, plane_of(A, B, C))
            A $in plane_of(A, B, C)
            B $in plane_of(A, B, C)
            C $in plane_of(A, B, C)

# I5: every plane contains three noncollinear points.
know:
    forall alpha plane:
        exist A, B, C point st {A $in alpha, B $in alpha, C $in alpha, $noncollinear(A, B, C)}

# I6: if two points of a line lie in a plane, the whole line lies in the plane.
know:
    forall A, B point, alpha plane:
        A != B
        A $in alpha
        B $in alpha
        =>:
            $line_on_plane(line_of(A, B), alpha)

# I7: two planes with one common point have a second common point.
know:
    forall A point, alpha, beta plane:
        A $in alpha
        A $in beta
        =>:
            exist B point st {B != A, B $in alpha, B $in beta}

# I8: there exist four points not lying in one plane.
know:
    exist A, B, C, D point st {$four_points_not_coplanar(A, B, C, D)}

# B1: betweenness symmetry and collinearity.
know:
    forall A, B, C point:
        $between(A, B, C)
        =>:
            $between(C, B, A)
            A != B
            A != C
            B != C
            $collinear(A, B, C)

# B2: given A != C, C lies between A and some B on the extension of AC.
know:
    forall A, C point:
        A != C
        =>:
            exist B point st {$between(A, C, B)}

# B3: among three distinct collinear points, at most one lies between the other two.
know:
    forall A, B, C point:
        A != B
        A != C
        B != C
        $collinear(A, B, C)
        $between(A, B, C)
        =>:
            not $between(B, A, C)
            not $between(A, C, B)

# Pasch's axiom in a segment-intersection form.
know:
    forall A, B, C point, l line:
        $noncollinear(A, B, C)
        $line_on_plane(l, plane_of(A, B, C))
        not A $in l
        not B $in l
        not C $in l
        $line_intersects_segment(l, A, B)
        =>:
            $line_intersects_segment(l, B, C) or $line_intersects_segment(l, A, C)

# C1: segment copying on a chosen ray.
know:
    forall A, B point, A2, side_point point:
        A != B
        A2 != side_point
        =>:
            exist B2 point st {$on_ray(A2, side_point, B2), $segment_congruent(A, B, A2, B2)}

# C2: segment congruence is reflexive, symmetric, and transitive.
know:
    forall A, B point:
        A != B
        =>:
            $segment_congruent(A, B, A, B)

    forall A, B, C, D point:
        $segment_congruent(A, B, C, D)
        =>:
            $segment_congruent(C, D, A, B)

    forall A, B, C, D, E, F point:
        $segment_congruent(A, B, C, D)
        $segment_congruent(C, D, E, F)
        =>:
            $segment_congruent(A, B, E, F)

# C3: addition of congruent segments.
know:
    forall A, B, C, A2, B2, C2 point:
        $between(A, B, C)
        $between(A2, B2, C2)
        $segment_congruent(A, B, A2, B2)
        $segment_congruent(B, C, B2, C2)
        =>:
            $segment_congruent(A, C, A2, C2)

# C4 and C5: angle copying and transitivity.
know:
    forall A, B, C point, D, E, side_point point, alpha plane:
        $noncollinear(A, B, C)
        D != E
        D $in alpha
        E $in alpha
        side_point $in alpha
        not side_point $in line_of(D, E)
        =>:
            exist F point st {F $in alpha, $same_side_of_line(F, side_point, line_of(D, E)), $angle_congruent(A, B, C, D, E, F)}

    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            $angle_congruent(A, B, C, A, B, C)

    forall A, B, C, D, E, F point:
        $angle_congruent(A, B, C, D, E, F)
        =>:
            $angle_congruent(D, E, F, A, B, C)

    forall A, B, C, D, E, F, G, H, I point:
        $angle_congruent(A, B, C, D, E, F)
        $angle_congruent(D, E, F, G, H, I)
        =>:
            $angle_congruent(A, B, C, G, H, I)

# C6: SAS triangle congruence consequence.
know:
    forall A, B, C, A2, B2, C2 point:
        $noncollinear(A, B, C)
        $noncollinear(A2, B2, C2)
        $segment_congruent(A, B, A2, B2)
        $segment_congruent(A, C, A2, C2)
        $angle_congruent(B, A, C, B2, A2, C2)
        =>:
            $angle_congruent(A, B, C, A2, B2, C2)
            $angle_congruent(A, C, B, A2, C2, B2)

# A unique plane through a line and an external point.
know:
    forall A point, l line:
        not A $in l
        =>:
            exist! alpha plane st {$plane_through_point_and_line(A, l, alpha)}

    forall A point, l line, alpha plane:
        $plane_through_point_and_line(A, l, alpha)
        =>:
            A $in alpha
            $line_on_plane(l, alpha)

have fn plane_of_point_and_line as set:
    forall A point, l line:
        not A $in l
        =>:
            exist! alpha plane st {$plane_through_point_and_line(A, l, alpha)}

# P1: Playfair's axiom.
know:
    forall l1, l2 line:
        $parallel_line(l1, l2)
        =>:
            l1 != l2

    forall l1, l2 line:
        $parallel_line(l1, l2)
        =>:
            $parallel_line(l2, l1)

    forall A point, l line:
        not A $in l
        =>:
            exist! l1 line st {A $in l1, $line_on_plane(l1, plane_of_point_and_line(A, l)), $parallel_line(l1, l)}

# Ct1: Archimedes' axiom in abstract form.
know:
    forall A, B, C, D point:
        A != B
        C != D
        =>:
            exist n N_pos st {$archimedes_number(A, B, C, D, n)}
```
