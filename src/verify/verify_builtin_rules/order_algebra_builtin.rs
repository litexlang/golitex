// Structural order on R (+, -, *, /) moved from Lit `BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES`.
// Called from `verify_order_atomic_fact_numeric_builtin_only` before the `0 <=` cone rules.

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
            if ml.left.to_string() == mr.left.to_string() {
                if let Some(r) = self.try_mul_le_shared_left(
                    ml.left.as_ref(),
                    ml.right.as_ref(),
                    mr.right.as_ref(),
                    lf,
                    atomic_fact,
                    "x * u <= x * v from 0 <= x and u <= v",
                    "x * u <= x * v from x <= 0 and v <= u",
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
                    "u * x <= v * x from 0 <= x and u <= v",
                    "u * x <= v * x from x <= 0 and v <= u",
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

        if let (Obj::Mul(ml), Obj::Mul(mr)) = (&f.left, &f.right) {
            if ml.left.to_string() == mr.left.to_string() {
                if let Some(r) = self.try_mul_lt_shared_left(
                    ml.left.as_ref(),
                    ml.right.as_ref(),
                    mr.right.as_ref(),
                    lf,
                    atomic_fact,
                    "x * u < x * v from 0 < x and u < v",
                    "x * u < x * v from x < 0 and v < u",
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
                    "u * x < v * x from 0 < x and u < v",
                    "u * x < v * x from x < 0 and v < u",
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
