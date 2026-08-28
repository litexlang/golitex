//! Union, intersection, and set-minus argument matching.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_union(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Union(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_intersect(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Intersect(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_set_minus(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SetMinus(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_big_union(
        &mut self,
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::BigUnion(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_big_intersect(
        &mut self,
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::BigIntersect(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }
}
