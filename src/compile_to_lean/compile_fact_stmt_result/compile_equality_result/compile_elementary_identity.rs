use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_min_max::min_max_arguments;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_identities::ElementaryIdentitySearchProofByBuiltinRule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_elementary_identity(
        &self,
        fact: &EqualFact,
        proof: &ElementaryIdentitySearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use ElementaryIdentitySearchProofByBuiltinRule as P;
        match proof {
            P::MinAssociative(_) => self.compile_minmax_associative(fact, false, position),
            P::MaxAssociative(_) => self.compile_minmax_associative(fact, true, position),
            P::MinMaxSum(_) => self.compile_minmax_pair(fact, false, position),
            P::MinMaxProduct(_) => self.compile_minmax_pair(fact, true, position),
            P::MinTranslation(_) => self.compile_min_translation(fact, position),
            P::MaxNegation(_) => self.compile_max_negation(fact, position),
            P::PowerSetIntersection(_) => self.compile_power_intersection(fact, position),
            P::FloorCharacterization(p) => self.compile_rounding_bounds(
                fact,
                false,
                &p.integer,
                &p.weak_bound,
                &p.strict_bound,
                position,
            ),
            P::CeilCharacterization(p) => self.compile_rounding_bounds(
                fact,
                true,
                &p.integer,
                &p.weak_bound,
                &p.strict_bound,
                position,
            ),
            P::GcdAddArgument(_) => self.compile_gcd_argument_identity(fact, false, position),
            P::GcdNegation(_) => self.compile_gcd_argument_identity(fact, true, position),
            P::GcdPositiveScale(p) => self.compile_gcd_positive_scale(
                fact,
                [&p.first_positive, &p.second_positive, &p.factor_positive],
                position,
            ),
            P::RemainderIntegerShift(p) => {
                self.compile_remainder_integer_shift(fact, &p.multiplier_integer, position)
            }
            P::CartesianUnion(_) => self.compile_cartesian_union(fact, position),
        }
    }

    fn compile_minmax_associative(
        &self,
        fact: &EqualFact,
        maximum: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Some((ab, c)), Some((a, bc))) = (
                min_max_arguments(left, maximum),
                min_max_arguments(right, maximum),
            ) else {
                continue;
            };
            let (Some((x, y)), Some((u, v))) = (
                min_max_arguments(ab, maximum),
                min_max_arguments(bc, maximum),
            ) else {
                continue;
            };
            if x.ir() != a.ir() || y.ir() != u.ir() || c.ir() != v.ir() {
                continue;
            }
            let term = self.compile_object_reference(left, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  let _outer := {term}\n  exact (Litex.minMaxAssociativeValue {maximum} (Litex.denote _outer.val.left.val.left) (Litex.denote _outer.val.left.val.right) (Litex.denote _outer.val.right) _outer.val.left.wd.1 _outer.val.left.wd.2 _outer.wd.2){symmetric}\n)"));
        }
        Err(LeanCompileError::unsupported("MinMax/AssociativeSubject"))
    }

    fn compile_minmax_pair(
        &self,
        fact: &EqualFact,
        product: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (first, second, x, y) = match (left, right, product) {
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Add(a)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Add(b)),
                    false,
                ) => (&a.left, &a.right, &b.left, &b.right),
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
                    true,
                ) => (&a.left, &a.right, &b.left, &b.right),
                _ => continue,
            };
            for (min, max, min_first) in [(first, second, true), (second, first, false)] {
                let (Some((a, b)), Some((c, d))) =
                    (min_max_arguments(min, false), min_max_arguments(max, true))
                else {
                    continue;
                };
                if a.ir() != c.ir() || b.ir() != d.ir() {
                    continue;
                }
                let reverse_args = if a.ir() == x.ir() && b.ir() == y.ir() {
                    false
                } else if a.ir() == y.ir() && b.ir() == x.ir() {
                    true
                } else {
                    continue;
                };
                let term = self.compile_object_reference(min, position)?;
                let law = if product {
                    "minMaxProductValue"
                } else {
                    "minMaxSumValue"
                };
                let symmetric = if reversed { ".symm" } else { "" };
                return Ok(format!("(by\n  let _min := {term}\n  exact (Litex.{law} (Litex.denote _min.val.left) (Litex.denote _min.val.right) _min.wd.1 _min.wd.2 {min_first} {reverse_args}){symmetric}\n)"));
            }
        }
        Err(LeanCompileError::unsupported("MinMax/PairSubject"))
    }

    fn compile_min_translation(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Some((a, b)), Obj::ArithmeticOperator(ArithmeticOperator::Add(sum))) =
                (min_max_arguments(left, false), right)
            else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(x)),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(y)),
                Some((r, s)),
            ) = (a, b, min_max_arguments(&sum.left, false))
            else {
                continue;
            };
            if x.left.ir() != r.ir()
                || y.left.ir() != s.ir()
                || x.right.ir() != sum.right.ir()
                || y.right.ir() != sum.right.ir()
            {
                continue;
            }
            let term = self.compile_object_reference(&sum.left, position)?;
            let shift = self.compile_object_reference(&sum.right, position)?;
            let real = self.compile_real_membership_certificate(&sum.right, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  let _min := {term}\n  exact (Litex.minTranslationValue (Litex.denote _min.val.left) (Litex.denote _min.val.right) (Litex.denote {shift}) _min.wd.1 _min.wd.2 {real}){symmetric}\n)"));
        }
        Err(LeanCompileError::unsupported("MinMax/TranslationSubject"))
    }

    fn compile_max_negation(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Some((a, b)), Obj::ArithmeticOperator(ArithmeticOperator::Neg(negative))) =
                (min_max_arguments(left, true), right)
            else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)),
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(y)),
                Some((r, s)),
            ) = (a, b, min_max_arguments(&negative.arg, false))
            else {
                continue;
            };
            if x.arg.ir() != r.ir() || y.arg.ir() != s.ir() {
                continue;
            }
            let term = self.compile_object_reference(&negative.arg, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  let _min := {term}\n  exact (Litex.maxNegationValue (Litex.denote _min.val.left) (Litex.denote _min.val.right) _min.wd.1 _min.wd.2){symmetric}\n)"));
        }
        Err(LeanCompileError::unsupported("MinMax/NegationSubject"))
    }
}
