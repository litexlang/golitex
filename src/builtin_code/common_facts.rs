pub const COMMON_FACTS: &str = r#"
know:
    forall a, b R:
        =>:
            a = 0 and b = 0
        <=>:
            a ^ 2 + b ^ 2 = 0


    forall a R:
        a >= 0
        =>:
            abs(a) = a
    
    forall a R:
        a <= 0
        =>:
            abs(a) = -a

    forall a R:
        abs(a) >= 0
        abs(a) = a or abs(a) = -a

    forall a R:
        abs(a) = 0
        =>:
            a = 0

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
"#;
