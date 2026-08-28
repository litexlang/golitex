//! Ranges, sums, products, and reductions.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_range(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Range(ref given) => self.match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_sum(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sum(ref g) => self.match_arg_ternary_then_merge(
                left_start,
                left_end,
                left_func,
                g.start.as_ref(),
                g.end.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_finite_set_sum(
        &mut self,
        left_set: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SumOfFiniteSet(ref g) => self.match_arg_binary_then_merge(
                left_set,
                left_func,
                g.set.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_product(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Product(ref g) => self.match_arg_ternary_then_merge(
                left_start,
                left_end,
                left_func,
                g.start.as_ref(),
                g.end.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_finite_set_product(
        &mut self,
        left_set: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ProductOfFiniteSet(ref g) => self.match_arg_binary_then_merge(
                left_set,
                left_func,
                g.set.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_reduce(
        &mut self,
        left: &Reduce,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::Reduce(given) = given_arg else {
            return Ok(None);
        };
        self.match_arg_quinary_then_merge(
            left.start.as_ref(),
            left.end.as_ref(),
            left.func.as_ref(),
            left.op.as_ref(),
            left.seed.as_ref(),
            given.start.as_ref(),
            given.end.as_ref(),
            given.func.as_ref(),
            given.op.as_ref(),
            given.seed.as_ref(),
        )
    }

    pub(super) fn match_arg_when_left_is_finite_set_reduce(
        &mut self,
        left: &FiniteSetReduce,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FiniteSetReduce(given) = given_arg else {
            return Ok(None);
        };
        self.match_arg_quaternary_then_merge(
            left.set.as_ref(),
            left.func.as_ref(),
            left.op.as_ref(),
            left.seed.as_ref(),
            given.set.as_ref(),
            given.func.as_ref(),
            given.op.as_ref(),
            given.seed.as_ref(),
        )
    }
}
