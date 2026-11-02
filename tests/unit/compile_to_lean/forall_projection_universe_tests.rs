use std::collections::HashSet;

#[test]
fn returned_universals_use_only_declared_public_carrier_levels() {
    for source in [
        include_str!("../../../lean/examples/real_infimum_certificate_laws/statement.lit"),
        include_str!("../../../lean/examples/real_supremum_certificate_laws/statement.lit"),
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
