// Set unions, intersections, subset, finite_set count, etc.

pub const BUILTIN_ENV_CODE_FOR_SET_OPERATORS: &str = r#"

thm in_intersect_is_in_both:
    ? forall z set, A set, B set:
        $in(z, intersect(A, B))
        =>:
            $in(z, A)
            $in(z, B)
    trust:
        $in(z, A)
        $in(z, B)

thm in_set_minus_is_in_first_operand:
    ? forall z set, A set, B set:
        $in(z, set_minus(A, B))
        =>:
            $in(z, A)
    trust:
        $in(z, A)

thm in_set_minus_is_not_in_second_operand:
    ? forall z set, A set, B set:
        $in(z, set_minus(A, B))
        =>:
            not $in(z, B)
    trust:
        not $in(z, B)

thm in_cup_via_member_set:
    ? forall z set, F set, Y set:
        $in(Y, F)
        $in(z, Y)
        =>:
            $in(z, cup(F))
    trust:
        $in(z, cup(F))

thm subset_of_finite_set_is_finite:
    ? forall A set, B finite_set:
        A $subset B
        =>:
            $is_finite_set(A)
    trust:
        $is_finite_set(A)

trust:
    forall z set, A set, B set:
        $in(z, A)
        =>:
            $in(z, union(A, B))

    forall z set, A set, B set:
        $in(z, B)
        =>:
            $in(z, union(A, B))

    forall z set, A set, B set:
        $in(z, union(A, B))
        =>:
            $in(z, A) or $in(z, B)

    forall z set, A set, B set:
        $in(z, A)
        $in(z, B)
        =>:
            $in(z, intersect(A, B))

    forall z set, A set, B set:
        not $in(z, A)
        =>:
            not $in(z, intersect(A, B))

    forall z set, A set, B set:
        not $in(z, B)
        =>:
            not $in(z, intersect(A, B))

    forall A, B set:
        intersect(A, B) $subset A

    forall A, B set:
        intersect(A, B) $subset B

    forall A, B set:
        A $subset union(A, B)

    forall A, B set:
        B $subset union(A, B)

    forall A, B set:
        union(A, B) = union(B, A)

    forall A, B set:
        intersect(A, B) = intersect(B, A)

    forall A, B, C set:
        union(union(A, B), C) = union(A, union(B, C))

    forall A, B, C set:
        intersect(intersect(A, B), C) = intersect(A, intersect(B, C))

    forall A, B set:
        union(A, intersect(A, B)) = A

    forall A, B set:
        intersect(A, union(A, B)) = A

    forall A set:
        union(A, A) = A

    forall A set:
        intersect(A, A) = A

    forall A set:
        union(A, {}) = A

    forall A set:
        intersect(A, {}) = {}

    forall A, B, C set:
        intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))

    forall A, B, C set:
        union(A, intersect(B, C)) = intersect(union(A, B), union(A, C))

    forall z set, A set, B set:
        $in(z, A)
        not $in(z, B)
        =>:
            $in(z, set_minus(A, B))

    forall A, B set:
        set_minus(A, B) $subset A

    forall A, B set:
        set_diff(A, B) = union(set_minus(A, B), set_minus(B, A))

    forall A, B finite_set:
        $is_finite_set(union(A, B))
        $is_finite_set(intersect(A, B))
        $is_finite_set(set_minus(A, B))
        $is_finite_set(set_diff(A, B))

    forall A finite_set:
        count(A) $in N

    forall A finite_set, B set:
        B $subset A
        =>:
            $is_finite_set(B)
            $is_finite_set(set_minus(A, B))
            count(set_minus(A, B)) = count(A) - count(B)

    forall A, B finite_set:
        count(union(A, B)) = count(A) + count(B) - count(intersect(A, B))
        count(A) = count(intersect(A, B)) + count(set_minus(A, B))
        count(B) = count(intersect(A, B)) + count(set_minus(B, A))
        count(set_minus(A, B)) = count(A) - count(intersect(A, B))
        count(set_minus(B, A)) = count(B) - count(intersect(A, B))
        count(set_diff(A, B)) = count(set_minus(A, B)) + count(set_minus(B, A))

    forall A, B finite_set:
        A $subset B
        =>:
            count(A) <= count(B)

    forall A, B finite_set:
        A $superset B
        =>:
            count(A) >= count(B)

    forall A, B finite_set:
        count(intersect(A, B)) <= count(A)
        count(intersect(A, B)) <= count(B)
        count(set_minus(A, B)) <= count(A)
        count(union(A, B)) <= count(A) + count(B)
        count(set_diff(A, B)) <= count(A) + count(B)
"#;
