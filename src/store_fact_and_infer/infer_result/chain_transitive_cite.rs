use crate::ast::names::AtomicName;

pub enum ChainTransitiveCite {
    BuiltinEquality,
    BuiltinNumericOrder,
    KnownTransitive { prop_name: AtomicName },
}
