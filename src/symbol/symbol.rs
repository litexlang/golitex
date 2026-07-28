use crate::prelude::*;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;

const BUILTIN_SYMBOL_ID_START: u64 = 1 << 62;
const ALPHA_SYMBOL_ID_START: u64 = 3 << 62;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(u64);

impl SymbolId {
    pub(crate) fn new(value: u64) -> Self {
        SymbolId(value)
    }

    pub(crate) fn value(self) -> u64 {
        self.0
    }

    pub(crate) fn substitution_key(self) -> String {
        format!("#symbol_id_{}", self.0)
    }

    pub(crate) fn from_substitution_key(key: &str) -> Option<Self> {
        key.strip_prefix("#symbol_id_")
            .and_then(|value| value.parse::<u64>().ok())
            .map(SymbolId::new)
    }
}

#[derive(Debug)]
pub struct SymbolIdAllocator {
    next: Cell<u64>,
}

impl SymbolIdAllocator {
    pub fn new() -> Self {
        SymbolIdAllocator { next: Cell::new(0) }
    }

    pub fn allocate(&self) -> Result<SymbolId, RuntimeError> {
        let current = self.next.get();
        if current >= BUILTIN_SYMBOL_ID_START {
            return Err(RuntimeError::from(UnknownRuntimeError(
                RuntimeErrorStruct::new_with_just_msg("symbol ID space exhausted".to_string()),
            )));
        }
        let next = current.checked_add(1).ok_or_else(|| {
            RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "symbol ID space exhausted".to_string(),
            )))
        })?;
        self.next.set(next);
        Ok(SymbolId::new(current))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolBinding {
    id: SymbolId,
    name: String,
    canonical_display_name: String,
}

impl SymbolBinding {
    pub(crate) fn new(id: SymbolId, name: String, canonical_display_name: String) -> Self {
        SymbolBinding {
            id,
            name,
            canonical_display_name,
        }
    }

    pub fn id(&self) -> SymbolId {
        self.id
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn canonical_display_name(&self) -> &str {
        self.canonical_display_name.as_str()
    }

    pub(crate) fn substitution_key(&self) -> String {
        self.id.substitution_key()
    }

    pub fn as_ref(&self) -> SymbolRef {
        SymbolRef::new(self.id, self.canonical_display_name.clone())
    }

    pub(crate) fn with_local_name(self, name: String) -> Self {
        SymbolBinding::new(self.id, name.clone(), name)
    }

    pub(crate) fn with_canonical_display_name(self, canonical_display_name: String) -> Self {
        SymbolBinding::new(self.id, self.name, canonical_display_name)
    }

    pub(crate) fn from_allocated_internal_name(name: String) -> Option<Self> {
        internal_symbol_id(&name).map(|id| SymbolBinding::new(id, name.clone(), name))
    }

    pub(crate) fn alpha_canonical(index: usize, name: String) -> Self {
        let offset = u64::try_from(index).expect("alpha binder index exceeds u64");
        let id = SymbolId::new(
            ALPHA_SYMBOL_ID_START
                .checked_add(offset)
                .expect("alpha binder index exhausts canonical ID space"),
        );
        SymbolBinding::new(id, name.clone(), name)
    }
}

pub fn builtin_symbol_ref(name: &str) -> Option<SymbolRef> {
    let offset: u64 = match name {
        ADD => 0,
        SUB => 1,
        MUL => 2,
        DIV => 3,
        MOD => 4,
        POW => 5,
        MATRIX_ADD => 6,
        MATRIX_SUB => 7,
        MATRIX_MUL => 8,
        MATRIX_SCALAR_MUL => 9,
        MATRIX_POW => 10,
        Q_POS => 11,
        R_POS => 12,
        Q_NEG => 13,
        Z_NEG => 14,
        R_NEG => 15,
        Q_NZ => 16,
        Z_NZ => 17,
        R_NZ => 18,
        N_POS => 19,
        N => 20,
        Q => 21,
        Z => 22,
        R => 23,
        FINITE_SET_SIZE => 24,
        FINITE_SET_MAX => 25,
        FINITE_SET_MIN => 26,
        EQUAL => 27,
        NOT_EQUAL => 28,
        LESS => 29,
        GREATER => 30,
        LESS_EQUAL => 31,
        GREATER_EQUAL => 32,
        IS_SET => 33,
        IS_NONEMPTY_SET => 34,
        IS_FINITE_SET => 35,
        IS_CART => 36,
        IS_TUPLE => 37,
        SUBSET => 38,
        SUPERSET => 39,
        PROPER_SUBSET => 40,
        PROPER_SUPERSET => 41,
        IN => 42,
        FN_EQ_IN => 43,
        FN_EQ => 44,
        INJECTIVE => 45,
        SURJECTIVE => 46,
        BIJECTIVE => 47,
        _ => return None,
    };
    Some(SymbolRef::new(
        SymbolId::new(BUILTIN_SYMBOL_ID_START + offset),
        name.to_string(),
    ))
}

impl fmt::Display for SymbolBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref().identity_spine(&self.name))
    }
}

impl AsRef<str> for SymbolBinding {
    fn as_ref(&self) -> &str {
        self.name()
    }
}

#[derive(Clone, Debug)]
pub struct SymbolRef {
    id: SymbolId,
    display_name: String,
}

impl SymbolRef {
    pub(crate) fn new(id: SymbolId, display_name: String) -> Self {
        SymbolRef { id, display_name }
    }

    pub fn id(&self) -> SymbolId {
        self.id
    }

    pub fn display_name(&self) -> &str {
        self.display_name.as_str()
    }

    pub fn is_builtin(&self, name: &str) -> bool {
        builtin_symbol_ref(name).is_some_and(|builtin| builtin.id == self.id)
    }

    pub(crate) fn substitution_key(&self) -> String {
        self.id.substitution_key()
    }

    pub(crate) fn identity_spine(&self, display_name: &str) -> String {
        format!("#{}#{}", self.id.value(), display_name)
    }

    pub(crate) fn with_display_name(self, display_name: String) -> Self {
        SymbolRef::new(self.id, display_name)
    }

    pub(crate) fn to_local_binding(&self) -> SymbolBinding {
        SymbolBinding::new(
            self.id,
            self.display_name.clone(),
            self.display_name.clone(),
        )
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for SymbolRef {}

pub trait IntoSymbolRef {
    fn into_symbol_ref(self) -> SymbolRef;
}

impl IntoSymbolRef for SymbolRef {
    fn into_symbol_ref(self) -> SymbolRef {
        self
    }
}

impl IntoSymbolRef for &SymbolBinding {
    fn into_symbol_ref(self) -> SymbolRef {
        self.as_ref()
    }
}

impl IntoSymbolRef for SymbolBinding {
    fn into_symbol_ref(self) -> SymbolRef {
        self.as_ref()
    }
}

fn internal_symbol_id(name: &str) -> Option<SymbolId> {
    name.strip_prefix("#binder_")
        .and_then(|value| value.parse::<u64>().ok())
        .map(SymbolId::new)
}

pub fn insert_symbol_substitution(
    map: &mut HashMap<String, Obj>,
    binding: &SymbolBinding,
    replacement: Obj,
) {
    map.insert(binding.substitution_key(), replacement.clone());
    map.insert(binding.name().to_string(), replacement);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolRole {
    Object,
    Predicate,
    AbstractPredicate,
    Algorithm,
    Structure,
    StructureField,
    Template,
    Theorem,
    Axiom,
    Strategy,
    Module,
    Binder,
}

impl SymbolRole {
    pub fn description(self) -> &'static str {
        match self {
            SymbolRole::Object => "object",
            SymbolRole::Predicate => "prop",
            SymbolRole::AbstractPredicate => "abstract_prop",
            SymbolRole::Algorithm => "algorithm",
            SymbolRole::Structure => "struct",
            SymbolRole::StructureField => "struct field",
            SymbolRole::Template => "template",
            SymbolRole::Theorem => "theorem",
            SymbolRole::Axiom => "axiom",
            SymbolRole::Strategy => "strategy",
            SymbolRole::Module => "module",
            SymbolRole::Binder => "local binder",
        }
    }
}

#[derive(Clone, Debug)]
pub struct SymbolDefinition {
    binding: SymbolBinding,
    role: SymbolRole,
    trust_summary: ProofTrustSummary,
}

impl SymbolDefinition {
    pub fn new(binding: SymbolBinding, role: SymbolRole) -> Self {
        SymbolDefinition {
            binding,
            role,
            trust_summary: ProofTrustSummary::new(),
        }
    }

    pub fn new_with_trust(
        binding: SymbolBinding,
        role: SymbolRole,
        trust_summary: ProofTrustSummary,
    ) -> Self {
        SymbolDefinition {
            binding,
            role,
            trust_summary,
        }
    }

    pub fn binding(&self) -> &SymbolBinding {
        &self.binding
    }

    pub fn role(&self) -> SymbolRole {
        self.role
    }

    pub fn trust_summary(&self) -> &ProofTrustSummary {
        &self.trust_summary
    }

    pub fn merge_trust_summary(&mut self, trust_summary: &ProofTrustSummary) {
        self.trust_summary.merge(trust_summary);
    }
}

#[derive(Clone)]
pub struct SymbolTable {
    definitions: HashMap<String, SymbolDefinition>,
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable {
            definitions: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&SymbolDefinition> {
        self.definitions.get(name)
    }

    pub fn get_by_id(&self, symbol_id: SymbolId) -> Option<&SymbolDefinition> {
        self.definitions
            .values()
            .find(|definition| definition.binding().id() == symbol_id)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.definitions.contains_key(name)
    }

    pub fn insert(&mut self, definition: SymbolDefinition) -> Result<(), SymbolDefinition> {
        let name = definition.binding().name().to_string();
        if self.definitions.contains_key(&name) {
            return Err(definition);
        }
        self.definitions.insert(name, definition);
        Ok(())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &SymbolDefinition)> {
        self.definitions.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&String, &mut SymbolDefinition)> {
        self.definitions.iter_mut()
    }
}

#[cfg(test)]
mod tests {
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
}
