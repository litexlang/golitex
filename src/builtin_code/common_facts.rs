pub const COMMON_FACTS: &str = r#"
know:
    + $in fn(a, b R) R
    - $in fn(a, b R) R
    * $in fn(a, b R) R
    / $in fn(a R, b R: b != 0) R
    % $in fn(a Z, b Z: b != 0) Z
    ^ $in fn(a, b R: a $in R_pos or a = 0 and b $in R_pos or a $in R_nz and b $in Z or b $in N_pos) R

know:
    forall a, b R:
        =>:
            a = 0 and b = 0
        <=>:
            a ^ 2 + b ^ 2 = 0


    forall a, b R:
        a <= max(a, b)
        b <= max(a, b)

    forall a, b R:
        min(a, b) <= a
        min(a, b) <= b

    forall a, b R:
        max(a, b) = max(b, a)
        min(a, b) = min(b, a)

    forall a,b R:
        a*b!=0
        =>:
            a!=0 and b!=0

    forall a R_pos, b R_nz:
        0 < a ^ b
        a = (a^b)^(1/b)

    forall a R_pos, b R_nz:
        a = (a^(1/b))^b

    forall a R_pos, b R, c R:
        (a^b)^c = a^(b*c)

    forall a R_pos, b R, c R:
        a^(b+c) = a^b * a^c

    forall a R_pos, b R:
        a * a^b = a^(b+1)
        a^b * a = a^(b+1)

    forall a R_nz, b Z:
        a * a^b = a^(b+1)
        a^b * a = a^(b+1)
    
    forall a R_pos, b R_pos:
        a != 1
        =>:
            a ^ (log(a, b)) = b

    forall a, b, c Z:
        c != 0
        =>:
            (a + b) % c = ((a % c) + (b % c)) % c
            (a - b) % c = ((a % c) - (b % c)) % c

    forall n Z, k N_pos:
        (-n) % k = (k - (n % k)) % k

    forall n Z, m Z:
        n <= m or n >= m + 1
        n < m or n >= m
        n >= m or n <= m - 1
        n > m or n <= m

    forall n Z, m N_pos, k N_pos:
        n^m % k = ((n % k)^m) % k

    forall a, b N:
        a <= b
        b != 0
        =>:
            a % b = b

thm archimedean_property:
    prove:
        forall e R_pos:
            exist n N_pos st {1/n < e}
    know:
        exist n N_pos st {1/n < e}

know:
    forall s set:
        seq(s) = fn(x N_pos) s

    forall s set, n N_pos:
        finite_seq(s, n) = fn(x N_pos: x <= n) s

    forall s set, m N_pos, n N_pos:
        matrix(s, m, n) = fn(x, y N_pos: x <= m, y <= n) s

    forall a Z, m N_pos:
        (a % m) $in N
        (a % m) < m

    forall a Z, m N_pos, k N:
        a % m = k
        =>:
            exist r Z st {a = m * r + k}

    forall a Z, m N_pos, k N:
        k < m
        exist r Z st {a = m * r + k}
        =>:
            a % m = k

    forall a Z, m N_pos:
        exist r Z st {a = m * r}
        =>:
            a % m = 0

    forall a Z, m N_pos:
        exist r Z st {a = r * m}
        =>:
            a % m = 0

    forall a Z, m N_pos:
        a % m = 0
        =>:
            exist r Z st {a = m * r}

    forall a Z, m N_pos:
        a % m = 0
        =>:
            exist r Z st {a = r * m}

    forall a Z, m N_pos, k N:
        k < m
        exist r Z st {a = r * m + k}
        =>:
            a % m = k

    forall a N, m N_pos, k N:
        a % m = k
        =>:
            exist r N st {a = m * r + k}

    forall a N, m N_pos, k N:
        k < m
        exist r N st {a = m * r + k}
        =>:
            a % m = k

    forall a N, m N_pos:
        exist r N st {a = m * r}
        =>:
            a % m = 0

    forall a N, m N_pos:
        exist r N st {a = r * m}
        =>:
            a % m = 0

    forall a N, m N_pos:
        a % m = 0
        =>:
            exist r N st {a = m * r}

    forall a N, m N_pos:
        a % m = 0
        =>:
            exist r N st {a = r * m}

    forall a N, m N_pos, k N:
        k < m
        exist r N st {a = r * m + k}
        =>:
            a % m = k

    forall a finite_set:
        count(a) = 0
        =>:
            not $is_nonempty_set(a)
            a = {}

    forall a, b N_pos:
        a % b = 0
        =>:
            b <= a

    forall a Q:
        exist p Z, q N_pos st {a = p / q}

    forall a Q:
        a >= 0
        =>:
            exist p N, q N_pos st {a = p / q}

thm even_power_abs_bound:
    prove:
        forall x, y R, k N_pos:
            k % 2 = 0
            x^k <= y^k
            =>:
                abs(x) <= abs(y)
    know:
        abs(x) <= abs(y)

thm even_power_bound_by_nonnegative_rhs:
    prove:
        forall x, y R, k N_pos:
            k % 2 = 0
            x^k <= y^k
            y >= 0
            =>:
                -y <= x
                x <= y
    know:
        -y <= x
        x <= y

thm even_power_bound_by_nonpositive_rhs:
    prove:
        forall x, y R, k N_pos:
            k % 2 = 0
            x^k <= y^k
            y <= 0
            =>:
                y <= x
                x <= -y
    know:
        y <= x
        x <= -y


let pi R:
    pi > 0

let euler_e R:
    euler_e > 0
        
know:
    forall a, b R_pos:
        a^2 < b^2 or a^3 < b^3 or a^4 < b^4 or a^5 < b^5
        =>:
            a < b

    forall a, b R_pos:
        a^2 <= b^2 or a^3 <= b^3 or a^4 <= b^4 or a^5 <= b^5
        =>:
            a <= b
        
thm pos_pow_strict_order_reflects:
    prove:
        forall a, b, k R_pos:
            a^k < b^k
            k >= 1
            =>:
                a < b
    know:
        a < b

thm pos_pow_order_reflects:
    prove:
        forall a, b, k R_pos:
            a^k <= b^k
            k >= 1
            =>:
                a <= b
    know:
        a <= b

know forall s set:
    s $in power_set(s)
    {} $in power_set(s)

prop increasing(s power_set(R), f set):
    $restrict_fn_in(f, fn(x s)R)
    forall x, y s:
        x < y
        =>:
            f(x) < f(y)

prop decreasing(s power_set(R), f set):
    $restrict_fn_in(f, fn(x s)R)
    forall x, y s:
        x < y
        =>:
            f(x) > f(y)

prop nondecreasing(s power_set(R), f set):
    $restrict_fn_in(f, fn(x s)R)
    forall x, y s:
        x < y
        =>:
            f(x) <= f(y)

prop nonincreasing(s power_set(R), f set):
    $restrict_fn_in(f, fn(x s)R)
    forall x, y s:
        x < y
        =>:
            f(x) >= f(y)

"#;
