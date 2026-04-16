use crate::prelude::*;

impl Runtime {
    pub fn iter_environments_from_top(&self) -> impl Iterator<Item = &Environment> {
        self.environment_stack.iter().rev().map(|env| env.as_ref())
    }

    pub fn get_object_satisfy_struct(
        &self,
        obj: &IdentifierOrIdentifierWithMod,
    ) -> Option<&StructObj> {
        let key = obj.to_string();
        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_identifier_satisfy_struct.get(&key) {
                return Some(definition);
            }
        }
        None
    }

    pub fn get_object_in_fn_set(&self, obj: &Obj) -> Option<&FnSet> {
        let key = obj.to_string();

        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_objs_in_fn_sets.get(&key) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_cloned_object_in_fn_set(&self, obj: &Obj) -> Option<FnSet> {
        let key = obj.to_string();

        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_objs_in_fn_sets.get(&key) {
                return Some(definition.clone());
            }
        }

        None
    }

    pub fn cache_well_defined_obj_contains(&self, key: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if env.cache_well_defined_obj.contains_key(key) {
                return true;
            }
        }
        false
    }

    pub fn cache_known_facts_contains(&self, key: &str) -> (bool, LineFile) {
        for env in self.iter_environments_from_top() {
            if let Some(line_file) = env.cache_known_fact.get(key) {
                return (true, line_file.clone());
            }
        }
        (false, default_line_file())
    }

    pub fn get_object_equal_to_cart(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some((known_cart_obj, _)) = env.known_objs_equal_to_cart.get(name) {
                return Some(known_cart_obj.clone());
            }
            if let Some((_, Some(known_cart_obj), _)) = env.known_objs_equal_to_tuple.get(name) {
                return Some(known_cart_obj.clone());
            }
        }
        None
    }

    pub fn get_obj_equal_to_tuple(&self, name: &str) -> Option<Tuple> {
        for env in self.iter_environments_from_top() {
            if let Some((Some(known_tuple_obj), _, _)) = env.known_objs_equal_to_tuple.get(name) {
                return Some(known_tuple_obj.clone());
            }
        }
        None
    }

    pub fn get_obj_equal_to_finite_seq_list(&self, name: &str) -> Option<FiniteSeqListObj> {
        for env in self.iter_environments_from_top() {
            if let Some((known_list, _, _)) = env.known_objs_equal_to_finite_seq_list.get(name) {
                return Some(known_list.clone());
            }
        }
        None
    }

    pub fn get_finite_seq_set_for_obj_equal_to_seq_list(
        &self,
        name: &str,
    ) -> Option<FiniteSeqSet> {
        for env in self.iter_environments_from_top() {
            if let Some((_, member_of, _)) = env.known_objs_equal_to_finite_seq_list.get(name) {
                return member_of.clone();
            }
        }
        None
    }

    pub fn get_obj_equal_to_matrix_list(&self, name: &str) -> Option<MatrixListObj> {
        for env in self.iter_environments_from_top() {
            if let Some((known_matrix, _, _)) = env.known_objs_equal_to_matrix_list.get(name) {
                return Some(known_matrix.clone());
            }
        }
        None
    }

    pub fn get_matrix_set_for_obj_equal_to_matrix_list(&self, name: &str) -> Option<MatrixSet> {
        for env in self.iter_environments_from_top() {
            if let Some((_, member_of, _)) = env.known_objs_equal_to_matrix_list.get(name) {
                return member_of.clone();
            }
        }
        None
    }

    pub fn get_object_equal_to_tuple(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some(cart) = env.known_objs_equal_to_tuple.get(name) {
                return cart.1.clone();
            }
        }
        None
    }

    pub fn get_object_equal_to_normalized_decimal_number(&self, obj_str: &str) -> Option<Number> {
        for env in self.iter_environments_from_top() {
            if let Some(calculated_value) = env
                .known_objs_equal_to_normalized_decimal_number
                .get(obj_str)
            {
                return Some(calculated_value.clone());
            }
        }
        None
    }

    // TODO: PREDICATE WITH MOD NAME IS NOT IMPLEMENTED YET
    pub fn get_all_objs_equal_to_given(&self, given: &str) -> Vec<String> {
        let mut result = vec![];
        for env in self.iter_environments_from_top() {
            if let Some((_, equiv_class_members_rc)) = env.known_equality.get(given) {
                for obj in equiv_class_members_rc.iter() {
                    result.push(obj.to_string());
                }
            }
        }

        result
    }
}
