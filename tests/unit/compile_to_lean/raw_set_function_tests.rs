#[test]
fn captured_set_functions_replay_rays_sequences_and_fibers() {
    for source in [
        include_str!("../../../lean/examples/captured_real_rays/statement.lit"),
        include_str!("../../../lean/examples/captured_sequence_sets/statement.lit"),
        include_str!("../../../lean/examples/captured_function_fibers/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "raw_set_functions")
            .expect(source);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "raw_set_functions").unwrap()
        );
    }
}
