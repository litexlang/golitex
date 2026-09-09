//! Canonical Environment-owned object storage.

use crate::prelude::*;
use std::collections::HashMap;

/// Object knowledge has one canonical entry per object equality key.
#[derive(Clone)]
pub struct ObjectPropertyMemory {
    pub knowledge_by_object: HashMap<ObjString, EnvironmentObjectKnowledge>,
}

impl ObjectPropertyMemory {
    pub fn new() -> Self {
        Self {
            knowledge_by_object: HashMap::new(),
        }
    }

    pub fn knowledge(&self, key: &str) -> Option<&EnvironmentObjectKnowledge> {
        self.knowledge_by_object.get(key)
    }

    pub fn knowledge_mut(&mut self, key: ObjString) -> &mut EnvironmentObjectKnowledge {
        self.knowledge_by_object.entry(key).or_default()
    }

    pub fn store_tuple_and_cart(
        &mut self,
        key: ObjString,
        tuple: Option<Tuple>,
        cart: Option<Cart>,
        line_file: LineFile,
    ) {
        let knowledge = self.knowledge_mut(key);
        let old = knowledge.tuple_equality.take();
        let merged_tuple = match (tuple, old.as_ref()) {
            (Some(new_tuple), _) => Some(new_tuple),
            (None, Some((old_tuple, _, _))) => old_tuple.clone(),
            (None, None) => None,
        };
        let merged_cart = match (cart, old.as_ref()) {
            (Some(new_cart), _) => Some(new_cart),
            (None, Some((_, old_cart, _))) => old_cart.clone(),
            (None, None) => None,
        };
        knowledge.tuple_equality = Some((merged_tuple, merged_cart, line_file));
    }

    pub fn store_cart(&mut self, key: ObjString, cart: Cart, line_file: LineFile) {
        self.knowledge_mut(key).cart_equality = Some((cart, line_file));
    }

    pub fn store_set_builder(
        &mut self,
        key: ObjString,
        set_builder: SetBuilder,
        line_file: LineFile,
    ) {
        self.knowledge_mut(key).set_builder_equality = Some((set_builder, line_file));
    }

    pub fn store_finite_sequence_list(
        &mut self,
        key: ObjString,
        list: FiniteSeqListObj,
        member_of: Option<FiniteSeqSet>,
        line_file: LineFile,
    ) {
        let knowledge = self.knowledge_mut(key);
        let old_member_of = knowledge
            .finite_sequence_list_equality
            .as_ref()
            .and_then(|(_, old_member_of, _)| old_member_of.clone());
        knowledge.finite_sequence_list_equality =
            Some((list, member_of.or(old_member_of), line_file));
    }

    pub fn store_matrix_list(
        &mut self,
        key: ObjString,
        matrix: MatrixListObj,
        member_of: Option<MatrixSet>,
        line_file: LineFile,
    ) {
        let knowledge = self.knowledge_mut(key);
        let old_member_of = knowledge
            .matrix_list_equality
            .as_ref()
            .and_then(|(_, old_member_of, _)| old_member_of.clone());
        knowledge.matrix_list_equality = Some((matrix, member_of.or(old_member_of), line_file));
    }

    pub fn store_matrix_set_membership(
        &mut self,
        key: ObjString,
        matrix_set: MatrixSet,
        line_file: LineFile,
    ) {
        self.knowledge_mut(key).matrix_set_membership = Some((matrix_set, line_file));
    }

    pub fn store_simplified_value(&mut self, key: ObjString, value: KnownObjValue) {
        self.knowledge_mut(key).simplified_value = Some(value);
    }

    pub fn function_set(&self, key: &str) -> Option<&KnownFnInfo> {
        self.knowledge(key)?.function_set.as_ref()
    }

    pub fn function_set_mut(&mut self, key: ObjString) -> &mut KnownFnInfo {
        self.knowledge_mut(key).function_set.get_or_insert_default()
    }

    pub fn merge_from(&mut self, child: Self) {
        for (key, child_knowledge) in child.knowledge_by_object {
            if let Some((tuple, cart, line_file)) = child_knowledge.tuple_equality {
                self.store_tuple_and_cart(key.clone(), tuple, cart, line_file);
            }
            let knowledge = self.knowledge_mut(key);
            if let Some(value) = child_knowledge.cart_equality {
                knowledge.cart_equality = Some(value);
            }
            if let Some((list, member_of, line_file)) =
                child_knowledge.finite_sequence_list_equality
            {
                let old_member_of = knowledge
                    .finite_sequence_list_equality
                    .as_ref()
                    .and_then(|(_, old_member_of, _)| old_member_of.clone());
                knowledge.finite_sequence_list_equality =
                    Some((list, member_of.or(old_member_of), line_file));
            }
            if let Some((matrix, member_of, line_file)) = child_knowledge.matrix_list_equality {
                let old_member_of = knowledge
                    .matrix_list_equality
                    .as_ref()
                    .and_then(|(_, old_member_of, _)| old_member_of.clone());
                knowledge.matrix_list_equality =
                    Some((matrix, member_of.or(old_member_of), line_file));
            }
            if let Some(value) = child_knowledge.matrix_set_membership {
                knowledge.matrix_set_membership = Some(value);
            }
            if let Some(value) = child_knowledge.simplified_value {
                knowledge.simplified_value = Some(value);
            }
            if let Some(value) = child_knowledge.set_builder_equality {
                knowledge.set_builder_equality = Some(value);
            }
            if let Some(child_info) = child_knowledge.function_set {
                let parent_info = knowledge.function_set.get_or_insert_default();
                let child_has_equal_to = child_info.equal_to.is_some();
                if let Some(fn_set) = child_info.fn_set {
                    // A defining RHS and its signature share exact parameter
                    // SymbolIds. A child that learned only another membership
                    // signature must not split an existing definition pair.
                    if child_has_equal_to
                        || parent_info.equal_to.is_none()
                        || parent_info.fn_set.is_none()
                    {
                        parent_info.fn_set = Some(fn_set);
                        parent_info.fn_set_membership_fact_id =
                            child_info.fn_set_membership_fact_id;
                    }
                }
                if let Some(equal_to) = child_info.equal_to {
                    parent_info.equal_to = Some(equal_to);
                }
            }
        }
    }

    pub fn tuple_equality_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.tuple_equality.is_some())
            .count()
    }

    pub fn cart_equality_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.cart_equality.is_some())
            .count()
    }

    pub fn finite_sequence_list_equality_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.finite_sequence_list_equality.is_some())
            .count()
    }

    pub fn matrix_list_equality_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.matrix_list_equality.is_some())
            .count()
    }

    pub fn simplified_value_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.simplified_value.is_some())
            .count()
    }

    pub fn set_builder_equality_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.set_builder_equality.is_some())
            .count()
    }

    pub fn function_set_count(&self) -> usize {
        self.knowledge_by_object
            .values()
            .filter(|knowledge| knowledge.function_set.is_some())
            .count()
    }

    pub fn old_summary_object_knowledge_count(&self) -> usize {
        self.tuple_equality_count()
            + self.cart_equality_count()
            + self.finite_sequence_list_equality_count()
            + self.matrix_list_equality_count()
            + self.simplified_value_count()
            + self.set_builder_equality_count()
            + self.function_set_count()
    }
}
