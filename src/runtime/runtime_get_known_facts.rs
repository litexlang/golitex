use crate::prelude::*;

impl Runtime {
    pub fn iter_environments_from_top(&self) -> impl Iterator<Item = &Environment> {
        self.environment_stack.iter().rev().map(|env| env.as_ref())
    }

    pub fn get_fn_set_where_fn_belongs_to(&self, obj: &Obj) -> Option<&FnSetWithParams> {
        let key = obj.to_string();

        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_obj_in_fn_set.get(&key) {
                return Some(definition);
            }
        }

        None
    }

    pub fn get_cloned_fn_set_where_fn_belongs_to(&self, obj: &Obj) -> Option<FnSetWithParams> {
        let key = obj.to_string();

        for env in self.iter_environments_from_top() {
            if let Some(definition) = env.known_obj_in_fn_set.get(&key) {
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

    pub fn cache_known_facts_contains(&self, key: &str) -> (bool, (usize, usize)) {
        for env in self.iter_environments_from_top() {
            if let Some(line_file) = env.cache_known_fact.get(key) {
                return (true, *line_file);
            }
        }
        (false, DEFAULT_LINE_FILE)
    }

    pub fn get_known_cart_obj_of_obj(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some((known_cart_obj, _)) = env.known_cart_objs.get(name) {
                return Some(known_cart_obj.clone());
            }
            if let Some((_, Some(known_cart_obj), _)) = env.known_tuple_objs.get(name) {
                return Some(known_cart_obj.clone());
            }
        }
        None
    }

    pub fn get_known_tuple_obj_of_obj(&self, name: &str) -> Option<Tuple> {
        for env in self.iter_environments_from_top() {
            if let Some((Some(known_tuple_obj), _, _)) = env.known_tuple_objs.get(name) {
                return Some(known_tuple_obj.clone());
            }
        }
        None
    }

    pub fn get_tuple_obj_is_in_what_cart(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some(cart) = env.known_tuple_objs.get(name) {
                return cart.1.clone();
            }
        }
        None
    }

    pub fn get_normalized_decimal_number_value_of_obj(&self, obj_str: &str) -> Option<Number> {
        for env in self.iter_environments_from_top() {
            if let Some(calculated_value) = env
                .known_normalized_decimal_number_value_of_obj
                .get(obj_str)
            {
                return Some(calculated_value.clone());
            }
        }
        None
    }

    // TODO: PREDICATE WITH MOD NAME IS NOT IMPLEMENTED YET
    pub fn get_all_objs_equal_to_arg(&self, given: &str) -> Vec<String> {
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
