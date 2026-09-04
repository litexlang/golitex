# Building a Mathematical System With Litex

Created and maintained by Jiachen shen, Keyao Zhu

This showcase illustrates **checked vocabulary growth**: build a mathematical
system by adding representations, domain concepts, and reusable facts in an
order that lets later mathematics depend on earlier checked knowledge. The
geometry is only the example; the reusable result is the construction process.
The workflow is: representation → domain vocabulary → computational bridges →
new consumers.

## 1. Choose a world that can compute

Begin with a concrete carrier and a small computational basis. In
[`main.lit`](main.lit), points and geometric calculations share one meaning:

```text
have points set = cart(R, R)
have fn vec(A, B cart(R, R)) cart(R, R) = (B[1] - A[1], B[2] - A[2])
have fn dot(u, v cart(R, R)) R = u[1] * v[1] + u[2] * v[2]
have fn det(u, v cart(R, R)) R = u[1] * v[2] - u[2] * v[1]
```

## 2. Give the domain its own vocabulary

Public statements should name mathematical ideas, not repeat their coordinate
expansions. A Litex `prop` gives a concept a readable interface and a precise
meaning that proofs can unfold when needed.

```text
prop is_right_angle(p, q, r cart(R, R)):
    p != q
    r != q
    dot(vec(q, p), vec(q, r)) = 0
```

## 3. Prove bridges where meanings meet

Do not make each large theorem rediscover how an abstract concept computes.
Prove a small reusable bridge exactly where the domain and representation meet.

```text
thm on_line_implies_affine_parameter:
    ? forall a, b, p cart(R, R):
        $is_on_line(p, a, b)
        =>:
            exist t R st {p[1] = (1 - t) * a[1] + t * b[1], p[2] = (1 - t) * a[2] + t * b[2]}
```

## 4. Test the language with a new consumer

A mathematical system earns its abstraction only when a later theorem can use
its public concepts and bridges without rebuilding their definitions.

```text
$geo::is_on_extension(m, pe, a),
$geo::is_on_line(m, b, d),
$geo::is_right_angle(a, pe, c)
=>:
    $geo::is_midpoint(m, b, d)
```

In [`problem_217_midpoint.lit`](problem_217_midpoint.lit), the statement stays
geometric while the proof crosses into coordinate calculation and then returns
to `is_midpoint`. That round trip tests whether the vocabulary is genuinely
reusable.

## Run and boundary

```bash
target/release/litex -r showcases/Example_of_Building_A_Math_System_With_Litex
```

The example is checked relative to 15 explicit axioms in `main.lit`; neither
source file contains `trust` or `abstract_prop`, and the consumer adds no new
axiom. It demonstrates a way to grow and reuse checked mathematical language,
not an axiom-free Euclidean foundation. A complete current-HEAD module replay
has not yet been recorded.
