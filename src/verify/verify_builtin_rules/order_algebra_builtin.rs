// Structural order on R (+, -, *, /) moved from Lit `BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES`.
// Called from `verify_order_atomic_fact_numeric_builtin_only` before the `0 <=` cone rules.
//
// Multiplication monotonicity on R: for fixed k, t |-> k*t preserves non-strict order when 0 <= k
// (a <= b => k*a <= k*b with k on the same side of both products), reverses when k <= 0 (b <= a =>
// k*a <= k*b). Strict: 0 < k and a < b => k*a < k*b; k < 0 and b < a => k*a < k*b.

use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_order_algebra_structural_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) => self.try_less_equal_algebra(f, atomic_fact),
            AtomicFact::LessFact(f) => self.try_less_algebra(f, atomic_fact),
            _ => Ok(None),
        }
    }

    fn verify_order_subgoal(&mut self, fact: AtomicFact) -> Result<StmtResult, RuntimeError> {
        let mut result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&fact)?;
        if !result.is_true() {
            result = self.verify_order_atomic_fact_numeric_builtin_only(&fact)?;
        }
        Ok(result)
    }

    fn literal_zero_obj() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    fn literal_one_obj() -> Obj {
        Obj::Number(Number::new("1".to_string()))
    }

    // k*u <= k*v from 0 <= k and u <= v; or k*u <= k*v from k <= 0 and v <= u (order reversal).
    fn try_mul_le_shared_left(
        &mut self,
        x: &Obj,
        u: &Obj,
        v: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        msg_nonneg: &str,
        msg_nonpos: &str,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let g0 = LessEqualFact::new(z.clone(), x.clone(), lf.clone()).into();
        let g_ord = LessEqualFact::new(u.clone(), v.clone(), lf.clone()).into();
        let r0 = self.verify_order_subgoal(g0)?;
        let r1 = self.verify_order_subgoal(g_ord)?;
        if r0.is_true() && r1.is_true() {
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_nonneg.to_string(),
                    vec![r0, r1],
                ),
            )));
        }
        let g_x_nonpos = LessEqualFact::new(x.clone(), z.clone(), lf.clone()).into();
        let g_rev = LessEqualFact::new(v.clone(), u.clone(), lf.clone()).into();
        let r2 = self.verify_order_subgoal(g_x_nonpos)?;
        let r3 = self.verify_order_subgoal(g_rev)?;
        if r2.is_true() && r3.is_true() {
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_nonpos.to_string(),
                    vec![r2, r3],
                ),
            )));
        }
        Ok(None)
    }

    // k*u < k*v from 0 < k and u < v; or k*u < k*v from k < 0 and v < u.
    fn try_mul_lt_shared_left(
        &mut self,
        x: &Obj,
        u: &Obj,
        v: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
        msg_pos: &str,
        msg_neg: &str,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let g_pos = LessFact::new(z.clone(), x.clone(), lf.clone()).into();
        let g_ord = LessFact::new(u.clone(), v.clone(), lf.clone()).into();
        let r0 = self.verify_order_subgoal(g_pos)?;
        let r1 = self.verify_order_subgoal(g_ord)?;
        if r0.is_true() && r1.is_true() {
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_pos.to_string(),
                    vec![r0, r1],
                ),
            )));
        }
        let g_x_neg = LessFact::new(x.clone(), z.clone(), lf.clone()).into();
        let g_rev = LessFact::new(v.clone(), u.clone(), lf.clone()).into();
        let r2 = self.verify_order_subgoal(g_x_neg)?;
        let r3 = self.verify_order_subgoal(g_rev)?;
        if r2.is_true() && r3.is_true() {
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg_neg.to_string(),
                    vec![r2, r3],
                ),
            )));
        }
        Ok(None)
    }

    // x1*x2 <= y1*y2 when 0 <= x1,x2,y1,y2 and (x1 <= y1, x2 <= y2) or (x1 <= y2, x2 <= y1).
    // Example: (m+1)*2 <= 2^m * 2 from IH and 2 <= 2, with m+1, 2, 2^m, 2 all nonnegative.
    fn try_mul_le_componentwise_nonnegative_factors(
        &mut self,
        l1: &Obj,
        l2: &Obj,
        r1: &Obj,
        r2: &Obj,
        lf: &LineFile,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z = Self::literal_zero_obj();
        let mut try_pairing = |x1: &Obj, x2: &Obj, y1: &Obj, y2: &Obj| -> Result<Option<StmtResult>, RuntimeError> {
            let subgoals: [AtomicFact; 6] = [
                LessEqualFact::new(z.clone(), x1.clone(), lf.clone()).into(),
                LessEqualFact::new(z.clone(), x2.clone(), lf.clone()).into(),
                LessEqualFact::new(z.clone(), y1.clone(), lf.clone()).into(),
                LessEqualFact::new(z.clone(), y2.clone(), lf.clone()).into(),
                LessEqualFact::new(x1.clone(), y1.clone(), lf.clone()).into(),
                LessEqualFact::new(x2.clone(), y2.clone(), lf.clone()).into(),
            ];
            let mut rec = Vec::with_capacity(6);
            for g in subgoals {
                let r = self.verify_order_subgoal(g)?;
                if !r.is_true() {
                    return Ok(None);
                }
                rec.push(r);
            }
            Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "x1 * x2 <= y1 * y2 from 0 <= factors and componentwise <=".to_string(),
                    rec,
                ),
            )))
        };
        if let Some(r) = try_pairing(l1, l2, r1, r2)? {
            return Ok(Some(r));
        }
        try_pairing(l1, l2, r2, r1)
    }

    fn try_less_equal_algebra(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lf = &f.line_file;
        let z = Self::literal_zero_obj();
        let one = Self::literal_one_obj();

        if let Obj::Add(add) = &f.right {
            let left_s = f.left.to_string();
            let b_opt = if add.left.as_ref().to_string() == left_s {
                Some(add.right.as_ref().clone())
            } else if add.right.as_ref().to_string() == left_s {
                Some(add.left.as_ref().clone())
            } else {
                None
            };
            if let Some(b) = b_opt {
                let g0 = LessEqualFact::new(z.clone(), b, lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if r0.is_true() {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a <= a + b from 0 <= b".to_string(),
                            vec![r0],
                        ),
                    )));
                }
            }
            // a <= u + v from a <= u and 0 <= v (or symmetric addends).
            let g_a_left = LessEqualFact::new(
                f.left.clone(),
                add.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g0_right = LessEqualFact::new(z.clone(), add.right.as_ref().clone(), lf.clone()).into();
            let r1 = self.verify_order_subgoal(g_a_left)?;
            let r2 = self.verify_order_subgoal(g0_right)?;
            if r1.is_true() && r2.is_true() {
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b + c from a <= b and 0 <= c".to_string(),
                        vec![r1, r2],
                    ),
                )));
            }
            let g_a_right = LessEqualFact::new(
                f.left.clone(),
                add.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g0_left = LessEqualFact::new(z.clone(), add.left.as_ref().clone(), lf.clone()).into();
            let r3 = self.verify_order_subgoal(g_a_right)?;
            let r4 = self.verify_order_subgoal(g0_left)?;
            if r3.is_true() && r4.is_true() {
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b + c from a <= b and 0 <= c".to_string(),
                        vec![r3, r4],
                    ),
                )));
            }
        }

        if let Obj::Mul(m) = &f.right {
            if m.right.to_string() == f.left.to_string() {
                let g0 = LessEqualFact::new(z.clone(), f.left.clone(), lf.clone()).into();
                let g1 = LessEqualFact::new(one, m.left.as_ref().clone(), lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if !r0.is_true() {
                    return Ok(None);
                }
                let r1 = self.verify_order_subgoal(g1)?;
                if !r1.is_true() {
                    return Ok(None);
                }
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a <= b * a from 0 <= a and 1 <= b".to_string(),
                        vec![r0, r1],
                    ),
                )));
            }
        }

        if let (Obj::Mul(ml), Obj::Mul(mr)) = (&f.left, &f.right) {
            if let Some(r) = self.try_mul_le_componentwise_nonnegative_factors(
                ml.left.as_ref(),
                ml.right.as_ref(),
                mr.left.as_ref(),
                mr.right.as_ref(),
                lf,
                atomic_fact,
            )? {
                return Ok(Some(r));
            }
            if ml.left.to_string() == mr.left.to_string() {
                if let Some(r) = self.try_mul_le_shared_left(
                    ml.left.as_ref(),
                    ml.right.as_ref(),
                    mr.right.as_ref(),
                    lf,
                    atomic_fact,
                    "k * a <= k * b from 0 <= k and a <= b",
                    "k * a <= k * b from k <= 0 and b <= a",
                )? {
                    return Ok(Some(r));
                }
            }
            if ml.right.to_string() == mr.right.to_string() {
                if let Some(r) = self.try_mul_le_shared_left(
                    ml.right.as_ref(),
                    ml.left.as_ref(),
                    mr.left.as_ref(),
                    lf,
                    atomic_fact,
                    "a * k <= b * k from 0 <= k and a <= b",
                    "a * k <= b * k from k <= 0 and b <= a",
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let (Obj::Add(al), Obj::Add(bl)) = (&f.left, &f.right) {
            let g1 = LessEqualFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2 = LessEqualFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1)?;
            if !r1.is_true() {
                return Ok(None);
            }
            let r2 = self.verify_order_subgoal(g2)?;
            if !r2.is_true() {
                return Ok(None);
            }
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "a + c <= b + d from a <= b and c <= d".to_string(),
                    vec![r1, r2],
                ),
            )));
        }

        if let (Obj::Sub(sl), Obj::Sub(sr)) = (&f.left, &f.right) {
            let g1 = LessEqualFact::new(
                sl.left.as_ref().clone(),
                sr.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2 = LessEqualFact::new(
                sr.right.as_ref().clone(),
                sl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1)?;
            if !r1.is_true() {
                return Ok(None);
            }
            let r2 = self.verify_order_subgoal(g2)?;
            if !r2.is_true() {
                return Ok(None);
            }
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "a - d <= b - c from a <= b and c <= d".to_string(),
                    vec![r1, r2],
                ),
            )));
        }

        if let (Obj::Div(dl), Obj::Div(dr)) = (&f.left, &f.right) {
            if dl.right.to_string() == dr.right.to_string() {
                let c = dl.right.as_ref();
                let g_pos = LessFact::new(z.clone(), c.clone(), lf.clone()).into();
                let g_ab = LessEqualFact::new(
                    dl.left.as_ref().clone(),
                    dr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_pos = self.verify_order_subgoal(g_pos)?;
                let r_ab = self.verify_order_subgoal(g_ab)?;
                if r_pos.is_true() && r_ab.is_true() {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a / c <= b / c from 0 < c and a <= b".to_string(),
                            vec![r_pos, r_ab],
                        ),
                    )));
                }
                let g_neg = LessFact::new(c.clone(), z.clone(), lf.clone()).into();
                let g_ab_flip = LessEqualFact::new(
                    dr.left.as_ref().clone(),
                    dl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_neg = self.verify_order_subgoal(g_neg)?;
                let r_ab2 = self.verify_order_subgoal(g_ab_flip)?;
                if r_neg.is_true() && r_ab2.is_true() {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "b / c <= a / c from c < 0 and a <= b".to_string(),
                            vec![r_neg, r_ab2],
                        ),
                    )));
                }
            }
        }

        Ok(None)
    }

    fn try_less_algebra(
        &mut self,
        f: &LessFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let lf = &f.line_file;
        let z = Self::literal_zero_obj();
        let one = Self::literal_one_obj();

        if let Obj::Add(add) = &f.right {
            let left_s = f.left.to_string();
            let b_opt = if add.left.as_ref().to_string() == left_s {
                Some(add.right.as_ref().clone())
            } else if add.right.as_ref().to_string() == left_s {
                Some(add.left.as_ref().clone())
            } else {
                None
            };
            if let Some(b) = b_opt {
                let g0 = LessFact::new(z.clone(), b, lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if r0.is_true() {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a < a + b from 0 < b".to_string(),
                            vec![r0],
                        ),
                    )));
                }
            }
        }

        if let Obj::Mul(m) = &f.right {
            if m.right.to_string() == f.left.to_string() {
                let g0 = LessFact::new(z.clone(), f.left.clone(), lf.clone()).into();
                let g1 = LessFact::new(one, m.left.as_ref().clone(), lf.clone()).into();
                let r0 = self.verify_order_subgoal(g0)?;
                if !r0.is_true() {
                    return Ok(None);
                }
                let r1 = self.verify_order_subgoal(g1)?;
                if !r1.is_true() {
                    return Ok(None);
                }
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a < b * a from 0 < a and 1 < b".to_string(),
                        vec![r0, r1],
                    ),
                )));
            }
        }

        if let (Obj::Mul(ml), Obj::Mul(mr)) = (&f.left, &f.right) {
            if ml.left.to_string() == mr.left.to_string() {
                if let Some(r) = self.try_mul_lt_shared_left(
                    ml.left.as_ref(),
                    ml.right.as_ref(),
                    mr.right.as_ref(),
                    lf,
                    atomic_fact,
                    "k * a < k * b from 0 < k and a < b",
                    "k * a < k * b from k < 0 and b < a",
                )? {
                    return Ok(Some(r));
                }
            }
            if ml.right.to_string() == mr.right.to_string() {
                if let Some(r) = self.try_mul_lt_shared_left(
                    ml.right.as_ref(),
                    ml.left.as_ref(),
                    mr.left.as_ref(),
                    lf,
                    atomic_fact,
                    "a * k < b * k from 0 < k and a < b",
                    "a * k < b * k from k < 0 and b < a",
                )? {
                    return Ok(Some(r));
                }
            }
        }

        if let (Obj::Add(al), Obj::Add(bl)) = (&f.left, &f.right) {
            let g1s = LessFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2s = LessFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r1 = self.verify_order_subgoal(g1s)?;
            let r2 = self.verify_order_subgoal(g2s)?;
            if r1.is_true() && r2.is_true() {
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a < b and c < d".to_string(),
                        vec![r1, r2],
                    ),
                )));
            }
            let g1m = LessFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2m = LessEqualFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r3 = self.verify_order_subgoal(g1m)?;
            let r4 = self.verify_order_subgoal(g2m)?;
            if r3.is_true() && r4.is_true() {
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a < b and c <= d".to_string(),
                        vec![r3, r4],
                    ),
                )));
            }
            let g1w = LessEqualFact::new(
                al.left.as_ref().clone(),
                bl.left.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let g2w = LessFact::new(
                al.right.as_ref().clone(),
                bl.right.as_ref().clone(),
                lf.clone(),
            )
            .into();
            let r5 = self.verify_order_subgoal(g1w)?;
            let r6 = self.verify_order_subgoal(g2w)?;
            if r5.is_true() && r6.is_true() {
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "a + c < b + d from a <= b and c < d".to_string(),
                        vec![r5, r6],
                    ),
                )));
            }
        }

        if let (Obj::Div(dl), Obj::Div(dr)) = (&f.left, &f.right) {
            if dl.right.to_string() == dr.right.to_string() {
                let c = dl.right.as_ref();
                let g_pos = LessFact::new(z.clone(), c.clone(), lf.clone()).into();
                let g_ab = LessFact::new(
                    dl.left.as_ref().clone(),
                    dr.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_pos = self.verify_order_subgoal(g_pos)?;
                let r_ab = self.verify_order_subgoal(g_ab)?;
                if r_pos.is_true() && r_ab.is_true() {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "a / c < b / c from 0 < c and a < b".to_string(),
                            vec![r_pos, r_ab],
                        ),
                    )));
                }
                let g_neg = LessFact::new(c.clone(), z.clone(), lf.clone()).into();
                let g_ab_flip = LessFact::new(
                    dr.left.as_ref().clone(),
                    dl.left.as_ref().clone(),
                    lf.clone(),
                )
                .into();
                let r_neg = self.verify_order_subgoal(g_neg)?;
                let r_ab2 = self.verify_order_subgoal(g_ab_flip)?;
                if r_neg.is_true() && r_ab2.is_true() {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "b / c < a / c from c < 0 and a < b".to_string(),
                            vec![r_neg, r_ab2],
                        ),
                    )));
                }
            }
        }

        Ok(None)
    }
}
