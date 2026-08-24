use super::*;

#[test]
fn allocator_is_monotonic_and_symbol_refs_compare_by_id() {
    let allocator = SymbolIdAllocator::new();
    let first = allocator.allocate().unwrap();
    let second = allocator.allocate().unwrap();
    assert_ne!(first, second);
    assert_eq!(first.value(), 0);
    assert_eq!(second.value(), 1);

    let short = SymbolRef::new(first, "x".to_string());
    let qualified = SymbolRef::new(first, "A::x".to_string());
    assert_eq!(short, qualified);
}
