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

prop archimedean_property(e R_pos):
    exist n N_pos st {1/n < e}

know:
    forall e R_pos:
        $archimedean_property(e)
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

    forall a Z, m N_pos, k N:
        k < m
        exist r Z st {a = r * m + k}
        =>:
            a % m = k

    forall a, b finite_set:
        count(union(a, b)) = count(a) + count(b) - count(intersect(a, b))

    forall a finite_set:
        count(a) = 0
        =>:
            not $is_nonempty_set(a)
            a = {}

    forall a, b N_pos:
        a % b = 0
        =>:
            b <= a
"#;
