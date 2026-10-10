use crate::prelude::*;
use std::collections::HashMap;

#[cfg(test)]
#[path = "../../tests/unit/execute/classified_exact_properties/tests.rs"]
mod classified_exact_properties_tests;

/// A resolved source fact, independent of the statement that introduced it.
/// Storage separates membership, selected views and directional equality buckets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecialProperty {
    Membership(InFact),
    Equality(EqualFact),
    /// Field names need a selected view, in addition to mathematical membership.
    DefaultStructView(InFact),
}

/// The opposite endpoint's outer constructor, not a mathematical type judgment.
/// Closed numeric expressions have a separate, content-based rewrite index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EqualToObjShape {
    AnonymousFn,
    FnSet,
    Tuple,
    Cart,
    SetBuilder,
    ListSet,
    Range,
    ClosedRange,
    SeqSet,
    FiniteSeqSet,
    PowerSet,
    Preimage,
    PreimageSet,
    FnObj,
    InstantiatedTemplateObj,
    FieldAccess,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqualitySide {
    Left,
    Right,
}

/// A direct stored equality citation. The AST remains in facts_by_id.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EqualityEndpoint {
    pub fact_id: FactId,
    pub value_side: EqualitySide,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ExactEqualityIndex {
    pub ordered: Vec<EqualityEndpoint>,
    pub by_shape: HashMap<EqualToObjShape, Vec<usize>>,
}

/// Separate buckets for one exact object key, owned by one ExecEnv scope.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ObjectSpecialProperties {
    pub memberships: Vec<InFact>,
    pub default_struct_views: Vec<InFact>,
    pub equalities: ExactEqualityIndex,
    // Preserve source priority when a reader combines membership and equality.
    order: Vec<SpecialPropertySlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SpecialPropertySlot {
    Membership(usize),
    Equality(usize),
    DefaultStructView(usize),
}

impl EqualToObjShape {
    pub fn of(object: &Obj) -> Self {
        match object {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) => Self::AnonymousFn,
            Obj::FunctionSpace(FunctionSpace::FnSet(_)) => Self::FnSet,
            Obj::ProductShape(ProductShape::Tuple(_)) => Self::Tuple,
            Obj::ProductShape(ProductShape::Cart(_)) => Self::Cart,
            Obj::SetFormer(SetFormer::SetBuilder(_)) => Self::SetBuilder,
            Obj::SetFormer(SetFormer::ListSet(_)) => Self::ListSet,
            Obj::SetFormer(SetFormer::Range(_)) => Self::Range,
            Obj::SetFormer(SetFormer::ClosedRange(_)) => Self::ClosedRange,
            Obj::SetFormer(SetFormer::SeqSet(_)) => Self::SeqSet,
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => Self::FiniteSeqSet,
            Obj::SetOperator(SetOperator::PowerSet(_)) => Self::PowerSet,
            Obj::FunctionSpace(FunctionSpace::Preimage(_)) => Self::Preimage,
            Obj::FunctionSpace(FunctionSpace::PreimageSet(_)) => Self::PreimageSet,
            Obj::FnObj(_) => Self::FnObj,
            Obj::InstantiatedTemplateObj(_) => Self::InstantiatedTemplateObj,
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_)) => {
                Self::FieldAccess
            }
            _ => Self::Other,
        }
    }
}

impl EqualityEndpoint {
    pub fn new(fact_id: FactId, value_side: EqualitySide) -> Self {
        Self {
            fact_id,
            value_side,
        }
    }

    pub fn value(&self, fact: &EqualFact) -> Obj {
        match self.value_side {
            EqualitySide::Left => fact.left.clone(),
            EqualitySide::Right => fact.right.clone(),
        }
    }
}

impl ExactEqualityIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Union buckets in source order, independent of requested shape order.
    pub fn indices_for_shapes(&self, shapes: &[EqualToObjShape]) -> Vec<usize> {
        let mut indices = Vec::new();
        for shape in shapes {
            if let Some(bucket) = self.by_shape.get(shape) {
                indices.extend(bucket.iter().copied());
            }
        }
        indices.sort_unstable();
        indices.dedup();
        indices
    }

    fn record(&mut self, endpoint: EqualityEndpoint, shape: EqualToObjShape) -> Option<usize> {
        if self
            .ordered
            .iter()
            .any(|row| row.fact_id == endpoint.fact_id)
        {
            return None;
        }
        let index = self.ordered.len();
        self.ordered.push(endpoint);
        self.by_shape.entry(shape).or_default().push(index);
        Some(index)
    }
}

impl ObjectSpecialProperties {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.order.len()
    }

    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    pub fn properties_in_order(&self, facts: &KnownFactMemory) -> Vec<SpecialProperty> {
        self.resolve_properties(facts, false)
    }

    pub fn function_signature_properties(&self, facts: &KnownFactMemory) -> Vec<SpecialProperty> {
        self.resolve_properties(facts, true)
    }

    fn resolve_properties(
        &self,
        facts: &KnownFactMemory,
        signatures_only: bool,
    ) -> Vec<SpecialProperty> {
        let signature_indices = self
            .equalities
            .indices_for_shapes(&[EqualToObjShape::AnonymousFn, EqualToObjShape::FnSet]);
        let mut properties = Vec::new();
        for slot in &self.order {
            match *slot {
                SpecialPropertySlot::Membership(index) => {
                    let fact = &self.memberships[index];
                    if !signatures_only
                        || matches!(&fact.set, Obj::FunctionSpace(FunctionSpace::FnSet(_)))
                    {
                        properties.push(SpecialProperty::Membership(fact.clone()));
                    }
                }
                SpecialPropertySlot::Equality(index) => {
                    if signatures_only && signature_indices.binary_search(&index).is_err() {
                        continue;
                    }
                    let endpoint = self.equalities.ordered[index];
                    if let Some(Fact::AtomicFact(AtomicFact::EqualFact(fact))) =
                        facts.facts_by_id.get(&endpoint.fact_id)
                    {
                        properties.push(SpecialProperty::Equality(fact.clone()));
                    }
                }
                SpecialPropertySlot::DefaultStructView(index) if !signatures_only => {
                    properties.push(SpecialProperty::DefaultStructView(
                        self.default_struct_views[index].clone(),
                    ));
                }
                SpecialPropertySlot::DefaultStructView(_) => {}
            }
        }
        properties
    }

    fn record(&mut self, key: &ObjIR, property: SpecialProperty) {
        match property {
            SpecialProperty::Membership(fact) => {
                if !self.memberships.contains(&fact) {
                    self.order
                        .push(SpecialPropertySlot::Membership(self.memberships.len()));
                    self.memberships.push(fact);
                }
            }
            SpecialProperty::DefaultStructView(fact) => {
                if !self.default_struct_views.contains(&fact) {
                    self.order.push(SpecialPropertySlot::DefaultStructView(
                        self.default_struct_views.len(),
                    ));
                    self.default_struct_views.push(fact);
                }
            }
            SpecialProperty::Equality(fact) => self.record_equality(key, &fact),
        }
    }

    fn record_equality(&mut self, key: &ObjIR, fact: &EqualFact) {
        // Left first preserves the old reader's reflexive/alpha-equal orientation.
        let value_side = if fact.left.ir() == *key {
            EqualitySide::Right
        } else if fact.right.ir() == *key {
            EqualitySide::Left
        } else {
            return;
        };
        let endpoint = EqualityEndpoint::new(fact.fact_id, value_side);
        let shape = match value_side {
            EqualitySide::Left => EqualToObjShape::of(&fact.left),
            EqualitySide::Right => EqualToObjShape::of(&fact.right),
        };
        if let Some(index) = self.equalities.record(endpoint, shape) {
            self.order.push(SpecialPropertySlot::Equality(index));
        }
    }

    #[cfg(test)]
    pub(crate) fn prepend_membership_for_test(&mut self, fact: InFact) {
        self.order
            .insert(0, SpecialPropertySlot::Membership(self.memberships.len()));
        self.memberships.push(fact);
    }
}

impl SpecialProperty {
    pub fn fact_id(&self) -> FactId {
        match self {
            Self::Membership(fact) | Self::DefaultStructView(fact) => fact.fact_id,
            Self::Equality(fact) => fact.fact_id,
        }
    }

    pub fn function_signature(&self) -> Option<FnSet> {
        match self {
            Self::Membership(fact) => match &fact.set {
                Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => Some(signature.clone()),
                _ => None,
            },
            Self::Equality(fact) => {
                for side in [&fact.left, &fact.right] {
                    match side {
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                            return Some(function.body.clone());
                        }
                        // Preserve the existing signature-alias callable contract.
                        Obj::FunctionSpace(FunctionSpace::FnSet(signature)) => {
                            return Some(signature.clone());
                        }
                        _ => {}
                    }
                }
                None
            }
            Self::DefaultStructView(_) => None,
        }
    }

    pub fn function_subject(&self) -> Option<&Obj> {
        match self {
            Self::Membership(fact)
                if matches!(&fact.set, Obj::FunctionSpace(FunctionSpace::FnSet(_))) =>
            {
                Some(&fact.element)
            }
            Self::Equality(fact) => {
                if matches!(
                    &fact.left,
                    Obj::FunctionSpace(FunctionSpace::FnSet(_) | FunctionSpace::AnonymousFn(_))
                ) {
                    Some(&fact.right)
                } else if matches!(
                    &fact.right,
                    Obj::FunctionSpace(FunctionSpace::FnSet(_) | FunctionSpace::AnonymousFn(_))
                ) {
                    Some(&fact.left)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl ExecEnv {
    pub(crate) fn index_special_property(&mut self, fact: &AtomicFact) {
        match fact {
            AtomicFact::InFact(fact) => {
                self.record_special_property(
                    fact.element.ir(),
                    SpecialProperty::Membership(fact.clone()),
                );
            }
            AtomicFact::EqualFact(fact) => {
                for key in [fact.left.ir(), fact.right.ir()] {
                    self.special_properties
                        .entry(key.clone())
                        .or_default()
                        .record_equality(&key, fact);
                }
            }
            _ => {}
        }
    }

    pub(crate) fn record_special_property(&mut self, key: ObjIR, property: SpecialProperty) {
        self.special_properties
            .entry(key.clone())
            .or_default()
            .record(&key, property);
    }
}
