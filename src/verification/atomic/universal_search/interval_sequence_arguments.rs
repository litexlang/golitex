//! Intervals and sequence-set arguments.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_closed_range(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ClosedRange(ref given) => self.match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_interval(
        &mut self,
        left: &IntervalObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::IntervalObj(given) = given_arg else {
            return Ok(None);
        };
        if left.left_closed() != given.left_closed() || left.right_closed() != given.right_closed()
        {
            return Ok(None);
        }
        self.match_arg_binary_then_merge(left.start(), left.end(), given.start(), given.end())
    }

    pub(super) fn match_arg_when_left_is_one_side_infinity_interval(
        &mut self,
        left: &OneSideInfinityIntervalObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::OneSideInfinityIntervalObj(given) = given_arg else {
            return Ok(None);
        };
        if !left.same_kind_as(given) {
            return Ok(None);
        }
        self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left.start(), given.start())
    }

    pub(super) fn match_arg_when_left_is_finite_seq_set(
        &mut self,
        left_set: &Obj,
        left_n: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSeqSet(ref given) => self.match_arg_binary_then_merge(
                left_set,
                left_n,
                given.set.as_ref(),
                given.n.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_seq_set(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SeqSet(ref given) => self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_set,
                given.set.as_ref(),
            ),
            _ => Ok(None),
        }
    }
}
