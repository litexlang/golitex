//! Matrix and scalar arithmetic argument matching.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_when_left_is_matrix_add(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixAdd(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_matrix_sub(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixSub(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_matrix_mul(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixMul(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_matrix_scalar_mul(
        &mut self,
        left_scalar: &Obj,
        left_matrix: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixScalarMul(ref g) => {
                self.match_arg_binary_then_merge(left_scalar, left_matrix, &g.scalar, &g.matrix)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_matrix_pow(
        &mut self,
        left_base: &Obj,
        left_exp: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixPow(ref g) => {
                self.match_arg_binary_then_merge(left_base, left_exp, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_add(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Add(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(left_left_number) = left_left {
                    let new_given = Sub::new(given_arg.clone(), left_left_number.clone().into());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right,
                        &new_given.into(),
                    );
                } else if let Obj::Number(left_right_number) = left_right {
                    let new_given = Sub::new(given_arg.clone(), left_right_number.clone().into());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    pub(super) fn match_arg_when_left_is_sub(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sub(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(right_number) = left_right {
                    let new_given = Add::new(right_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else if let Obj::Number(left_left_number) = left_left {
                    let new_given = Sub::new(left_left_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    pub(super) fn match_arg_when_left_is_mul(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Mul(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                let neg_one: Obj = Number::new("-1".to_string()).into();
                let known_left_is_neg_one = match left_left {
                    Obj::Number(n) => {
                        let left_obj: Obj = n.clone().into();
                        "-1".to_string() == left_obj.to_string()
                    }
                    _ => false,
                };
                if known_left_is_neg_one {
                    let synthetic: Obj = Mul::new(neg_one, given_arg.clone()).into();
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right, &synthetic,
                    );
                } else {
                    if let Obj::Number(n) = left_left {
                        if n.normalized_value == "0".to_string() {
                            return Ok(None);
                        } else {
                            let synthetic: Obj =
                                Div::new(given_arg.clone(), n.clone().into()).into();
                            return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                                left_right, &synthetic,
                            );
                        }
                    } else if let Obj::Number(left_right_number) = left_right {
                        // Solving `x * c = target` by `x = target / c`
                        // requires `c != 0`. Without this guard, the true
                        // forall fact `P(x * 0)` could match an arbitrary
                        // target `P(y)` through the ill-defined term `y / 0`.
                        if left_right_number.normalized_value == "0" {
                            return Ok(None);
                        }
                        let new_given =
                            Div::new(given_arg.clone(), left_right_number.clone().into());
                        return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                            left_left,
                            &new_given.into(),
                        );
                    } else {
                        return Ok(None);
                    }
                }
            }
        }
    }

    pub(super) fn match_arg_when_left_is_div(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Div(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(left_right_number) = left_right {
                    // Inverting a division is valid only for a nonzero fixed
                    // denominator. A verified source expression is already
                    // well-defined, but keep this algebraic precondition local
                    // to the matcher as defense in depth.
                    if left_right_number.normalized_value == "0" {
                        return Ok(None);
                    }
                    let new_given = Mul::new(left_right_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    pub(super) fn match_arg_when_left_is_mod(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Mod(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_pow(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Pow(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_abs(
        &mut self,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Abs(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_arg, &g.arg)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_sqrt(
        &mut self,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sqrt(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_arg, &g.arg)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn match_arg_when_left_is_log(
        &mut self,
        left_base: &Obj,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Log(ref g) => {
                self.match_arg_binary_then_merge(left_base, left_arg, &g.base, &g.arg)
            }
            _ => Ok(None),
        }
    }
}
