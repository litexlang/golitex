use super::*;

#[test]
fn statement_result_stays_pointer_sized_enough_for_recursive_composition() {
    assert!(
        std::mem::size_of::<StmtResult>() <= 32,
        "StmtResult unexpectedly grew to {} bytes; large success payloads belong behind Box",
        std::mem::size_of::<StmtResult>()
    );
    assert!(
        std::mem::size_of::<RuntimeError>() <= 32,
        "RuntimeError unexpectedly grew to {} bytes; large diagnostic payloads belong behind Box",
        std::mem::size_of::<RuntimeError>()
    );
}
