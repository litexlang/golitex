//! Cartesian, projection, tuple, and finite-sequence arguments.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_cart(
        &mut self,
        left_args: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cart(ref given) => self.match_boxed_arg_vec_then_merge(left_args, &given.args),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_cart_dim(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::CartDim(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_proj(
        &mut self,
        left_set: &Obj,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Proj(ref given) => self.match_arg_binary_then_merge(
                left_set,
                left_dim,
                given.set.as_ref(),
                given.dim.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_dim(
        &mut self,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::TupleDim(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_dim,
                    given.arg.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_tuple(
        &mut self,
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Tuple(ref given) => {
                self.match_boxed_arg_vec_then_merge(left_elements, &given.args)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_finite_seq_list(
        &mut self,
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSeqListObj(ref given) => {
                self.match_boxed_arg_vec_then_merge(left_elements, &given.objs)
            }
            _ => Ok(None),
        }
    }
}
