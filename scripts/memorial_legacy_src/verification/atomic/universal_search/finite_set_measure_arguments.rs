//! Finite-set size and extrema arguments.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_finite_set_size(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSetSize(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_finite_set_max(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSetMax(given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_finite_set_min(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSetMin(given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }
}
