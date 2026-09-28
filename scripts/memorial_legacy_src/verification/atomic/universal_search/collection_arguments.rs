//! List-set and quantifier-free fact arguments.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_list_set(
        &mut self,
        left_list: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ListSet(ref given) => self.match_boxed_arg_vec_then_merge(left_list, &given.list),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_quantifier_free_fact_in_known_forall(
        &mut self,
        left: &QuantifierFreeFact,
        given: &QuantifierFreeFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if !Runtime::_verify_quantifier_free_facts_the_same_type_ref(left, given)? {
            return Ok(None);
        }

        let left_args = left.get_args_from_fact_ref();
        let given_args = given.get_args_from_fact_ref();
        self.match_args_in_active_binding_scope(&left_args, &given_args)
    }
}
