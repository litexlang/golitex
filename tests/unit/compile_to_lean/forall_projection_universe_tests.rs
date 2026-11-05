use std::collections::HashSet;

#[test]
fn returned_universals_use_only_declared_public_carrier_levels() {
    for source in [
        r#"# Establish the infimum of {2}, identify any other candidate, and extract a crossing member.
by def $is_real_lower_bound({2},2)
release thm real_greatest_lower_bound_from_definition({2},2)
inf({2}) = 2
release thm real_greatest_lower_bound_lower_bound({2},2)
by def $is_real_lower_bound({2},1)
release thm real_greatest_lower_bound_exists({2},1)
obtain lower_candidate_witness from exist u R st {$is_real_greatest_lower_bound({2},u)}
release thm real_greatest_lower_bound_unique({2},lower_candidate_witness,2)
lower_candidate_witness = 2
release thm real_greatest_lower_bound_le_member({2},lower_candidate_witness,2)
release thm real_lower_bound_le_greatest_lower_bound({2},lower_candidate_witness,1)
release thm real_greatest_lower_bound_crosses({2},lower_candidate_witness,3)
obtain lower_crossing_witness from exist x {2} st {x < 3}
lower_crossing_witness < 3
lower_crossing_witness = 2

thm extremal_member_lower_bound:
    ? forall A set, b R, x A:
        A $subset R
        $is_real_greatest_lower_bound(A,b)
        =>:
            b <= x
    release thm real_greatest_lower_bound_le_member(A,b,x)

by thm extremal_member_lower_bound({2},lower_candidate_witness,2) => lower_candidate_witness <= 2
"#,
        r#"# Establish the supremum of {2}, identify any other candidate, and extract a crossing member.
by def $is_real_upper_bound({2},2)
release thm real_least_upper_bound_from_definition({2},2)
sup({2}) = 2
release thm real_least_upper_bound_upper_bound({2},2)
by def $is_real_upper_bound({2},3)
release thm real_least_upper_bound_exists({2},3)
obtain upper_candidate_witness from exist u R st {$is_real_least_upper_bound({2},u)}
release thm real_least_upper_bound_unique({2},upper_candidate_witness,2)
upper_candidate_witness = 2
release thm real_member_le_least_upper_bound({2},upper_candidate_witness,2)
release thm real_least_upper_bound_le_upper_bound({2},upper_candidate_witness,3)
release thm real_least_upper_bound_crosses({2},upper_candidate_witness,1)
obtain upper_crossing_witness from exist x {2} st {1 < x}
1 < upper_crossing_witness
upper_crossing_witness = 2

thm extremal_member_upper_bound:
    ? forall A set, b R, x A:
        A $subset R
        $is_real_least_upper_bound(A,b)
        =>:
            x <= b
    release thm real_member_le_least_upper_bound(A,b,x)

by thm extremal_member_upper_bound({2},upper_candidate_witness,2) => 2 <= upper_candidate_witness
"#,
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "returned_universals").unwrap();
        let declared: HashSet<_> = output
            .lines()
            .filter_map(|line| line.strip_prefix("universe "))
            .flat_map(str::split_whitespace)
            .collect();
        for after in output.split("Type ").skip(1) {
            let level: String = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if level.starts_with('v') {
                assert!(
                    declared.contains(level.as_str()),
                    "undeclared carrier level {level} in returned universal"
                );
            }
        }
    }
}
