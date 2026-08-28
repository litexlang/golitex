use super::*;

#[test]
fn fn_eq_infers_ordinary_equality() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("fn_eq_infers_ordinary_equality");

    let f: Obj = Identifier::new("f".to_string()).into();
    let g: Obj = Identifier::new("g".to_string()).into();
    let line_file = default_line_file();
    let fn_eq: AtomicFact = FnEqualFact::new(f.clone(), g.clone(), line_file.clone()).into();
    let ordinary_equality: Fact = EqualFact::new(f.clone(), g.clone(), line_file.clone()).into();

    let result = runtime
        .store_atomic_fact_without_well_defined_verified_and_infer(fn_eq)
        .expect("store fn_eq and infer ordinary equality");
    assert!(result.contains_added_fact(&ordinary_equality));
    assert!(runtime
        .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(&f, &g, line_file))
        .is_success());
}
