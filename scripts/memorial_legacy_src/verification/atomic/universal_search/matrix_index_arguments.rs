//! Matrix, power-set, and indexed-object arguments.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_matrix_list(
        &mut self,
        left_rows: &[Vec<Box<Obj>>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixListObj(ref given) => {
                self.match_arg_matrix_rows_then_merge(left_rows, &given.rows)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_matrix_set(
        &mut self,
        left_set: &Obj,
        left_row_len: &Obj,
        left_col_len: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixSet(ref given) => self.match_arg_ternary_then_merge(
                left_set,
                left_row_len,
                left_col_len,
                given.set.as_ref(),
                given.row_len.as_ref(),
                given.col_len.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_power_set(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::PowerSet(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_obj_at_index(
        &mut self,
        left_obj: &Obj,
        left_index: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ObjAtIndex(ref given) => self.match_arg_binary_then_merge(
                left_obj,
                left_index,
                given.obj.as_ref(),
                given.index.as_ref(),
            ),
            _ => Ok(None),
        }
    }
}
