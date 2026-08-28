//! Function-range and replacement arguments.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_fn_range(
        &mut self,
        left_function: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FnRange(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_function,
                    given.function.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_replacement(
        &mut self,
        left: &Replacement,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Replacement(given) => {
                if left.prop_name.to_string() != given.prop_name.to_string() {
                    return Ok(None);
                }
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left.source_set.as_ref(),
                    given.source_set.as_ref(),
                )
            }
            _ => Ok(None),
        }
    }
}
