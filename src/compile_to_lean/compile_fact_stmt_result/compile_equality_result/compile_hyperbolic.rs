use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_hyperbolic::hyperbolic_argument;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_hyperbolic::HyperbolicEqualityProof;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, sub_objs, div_objs, mul_objs};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_hyperbolic_equality(
        &self,
        fact: &EqualFact,
        proof: &HyperbolicEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use HyperbolicEqualityProof::*;
        let (kind, parity, law) = match proof {
            SinhDefinition(_) => ("Sinh", false, "Real.sinh_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.neg_re"),
            CoshDefinition(_) => ("Cosh", false, "Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat, Complex.neg_re"),
            TanhDefinition(_) => ("Tanh", false, "Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div"),
            CothDefinition(_) => ("Coth", false, "Litex.nativeCoth, Complex.ofReal_div"),
            SechDefinition(_) => ("Sech", false, "Litex.nativeSech, Complex.ofReal_div, Complex.ofReal_one"),
            CschDefinition(_) => ("Csch", false, "Litex.nativeCsch, Complex.ofReal_div, Complex.ofReal_one"),
            SinhParity(_) => ("Sinh", true, "Complex.neg_re, Real.sinh_neg, Complex.ofReal_neg"),
            CoshParity(_) => ("Cosh", true, "Complex.neg_re, Real.cosh_neg"),
            TanhParity(_) => ("Tanh", true, "Complex.neg_re, Real.tanh_neg, Complex.ofReal_neg"),
            CothParity(_) => ("Coth", true, "Complex.neg_re, Litex.nativeCoth, Real.cosh_neg, Real.sinh_neg, div_neg, Complex.ofReal_neg"),
            SechParity(_) => ("Sech", true, "Complex.neg_re, Litex.nativeSech, Real.cosh_neg"),
            CschParity(_) => ("Csch", true, "Complex.neg_re, Litex.nativeCsch, Real.sinh_neg, div_neg, Complex.ofReal_neg"),
            _ => return self.compile_hyperbolic_identity(fact, proof, position),
        };
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some((actual, argument)) = hyperbolic_argument(left) else {
                continue;
            };
            if actual != kind {
                continue;
            }
            let expected = if parity {
                let Obj::ArithmeticOperator(ArithmeticOperator::Neg(negative)) = argument else {
                    continue;
                };
                let value = hyperbolic(kind, *negative.arg.clone());
                if matches!(kind, "Cosh" | "Sech") {
                    value
                } else {
                    neg(value)
                }
            } else {
                let x = argument.clone();
                match kind {
                    "Sinh" => div_objs(sub_objs(exp(x.clone()), exp(neg(x))), num(2)),
                    "Cosh" => div_objs(add_objs(exp(x.clone()), exp(neg(x))), num(2)),
                    "Tanh" => div_objs(hyperbolic("Sinh", x.clone()), hyperbolic("Cosh", x)),
                    "Coth" => div_objs(hyperbolic("Cosh", x.clone()), hyperbolic("Sinh", x)),
                    "Sech" => div_objs(num(1), hyperbolic("Cosh", x)),
                    "Csch" => div_objs(num(1), hyperbolic("Sinh", x)),
                    _ => unreachable!(),
                }
            };
            if right.ir() != expected.ir() {
                continue;
            }
            if !parity && matches!(kind, "Sinh" | "Cosh") {
                let object = self.compile_object_reference(left, position)?;
                let left_value = self.compile_normalization_value(left, position)?;
                let right_value = self.compile_normalization_value(right, position)?;
                let orientation = if fact.left.ir() == left.ir() {
                    ""
                } else {
                    ".symm"
                };
                return Ok(format!("(by\n  have _definition := Litex.{}Definition {object}\n  change {left_value} = {right_value} at _definition\n  exact _definition{orientation})", kind.to_lowercase()));
            }
            return self.compile_trig_native_identity(
                fact,
                &format!("simp only [{law}]"),
                position,
            );
        }
        Err(LeanCompileError::unsupported("Hyperbolic/EquationSubject"))
    }
}

impl LitexToLeanCompiler {
    fn compile_hyperbolic_identity(
        &self,
        fact: &EqualFact,
        proof: &HyperbolicEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
        use HyperbolicEqualityProof::*;
        // Inspect the subjects only to validate the already selected rule and
        // its arguments. This traversal never selects another proof route.
        let mut pending = vec![fact.left.clone(), fact.right.clone()];
        while let Some(subject) = pending.pop() {
            if let Some(children) = corresponding_arg_pairs(&subject, &subject) {
                pending.extend(children.into_iter().map(|(child, _)| child));
            }
            let Some((_, x)) = hyperbolic_argument(&subject) else {
                continue;
            };
            let s = hyperbolic("Sinh", x.clone());
            let c = hyperbolic("Cosh", x.clone());
            let t = hyperbolic("Tanh", x.clone());
            let ct = hyperbolic("Coth", x.clone());
            let se = hyperbolic("Sech", x.clone());
            let cs = hyperbolic("Csch", x.clone());
            let (left, right, law, guarded) = match proof {
                HyperbolicPythagorean(_) => (
                    sub_objs(square(c), square(s)),
                    num(1),
                    "hyperbolicPythagorean",
                    None,
                ),
                TanhReciprocal(_) => (mul_objs(t, c), s, "tanhReciprocal", None),
                CothReciprocal(_) => (mul_objs(ct, s), c, "cothReciprocal", Some("Coth")),
                SechReciprocal(_) => (mul_objs(se, c), num(1), "sechReciprocal", None),
                CschReciprocal(_) => (mul_objs(cs, s), num(1), "cschReciprocal", Some("Csch")),
                TanhThroughSech(_) => (t, mul_objs(s, se), "tanhThroughSech", None),
                CothThroughCsch(_) => (ct, mul_objs(c, cs), "cothThroughCsch", None),
                TanhCothProduct(_) => (mul_objs(t, ct), num(1), "tanhCothProduct", Some("Coth")),
                TanhSechSquare(_) => (
                    sub_objs(num(1), square(t)),
                    square(se),
                    "tanhSechSquare",
                    None,
                ),
                CothCschSquare(_) => (
                    sub_objs(square(ct), num(1)),
                    square(cs),
                    "cothCschSquare",
                    Some("Coth"),
                ),
                SinhDoubleAngle(_) => (
                    hyperbolic("Sinh", mul_objs(num(2), x.clone())),
                    mul_objs(mul_objs(num(2), s), c),
                    "sinhDoubleAngle",
                    None,
                ),
                CoshDoubleAngle(_) => (
                    hyperbolic("Cosh", mul_objs(num(2), x.clone())),
                    add_objs(square(c), square(s)),
                    "coshDoubleAngle",
                    None,
                ),
                ExpThroughHyperbolic(_) => {
                    (exp(x.clone()), add_objs(c, s), "expThroughHyperbolic", None)
                }
                ExpNegativeThroughHyperbolic(_) => (
                    exp(neg(x.clone())),
                    sub_objs(c, s),
                    "expNegativeThroughHyperbolic",
                    None,
                ),
                SinhAddition(_) | CoshAddition(_) => {
                    let Obj::ArithmeticOperator(ArithmeticOperator::Add(pair)) = x else {
                        continue;
                    };
                    let (a, b) = (&*pair.left, &*pair.right);
                    let sa = hyperbolic("Sinh", a.clone());
                    let ca = hyperbolic("Cosh", a.clone());
                    let sb = hyperbolic("Sinh", b.clone());
                    let cb = hyperbolic("Cosh", b.clone());
                    if matches!(proof, SinhAddition(_)) {
                        (
                            s,
                            add_objs(mul_objs(sa, cb), mul_objs(ca, sb)),
                            "sinhAddition",
                            None,
                        )
                    } else {
                        (
                            c,
                            add_objs(mul_objs(ca, cb), mul_objs(sa, sb)),
                            "coshAddition",
                            None,
                        )
                    }
                }
                _ => return Err(LeanCompileError::unsupported("Hyperbolic/EquationRule")),
            };
            let reverse = if fact.left.ir() == left.ir() && fact.right.ir() == right.ir() {
                false
            } else if fact.right.ir() == left.ir() && fact.left.ir() == right.ir() {
                true
            } else {
                continue;
            };
            if matches!(
                proof,
                ExpThroughHyperbolic(_) | ExpNegativeThroughHyperbolic(_)
            ) {
                let cosine =
                    self.compile_object_reference(&hyperbolic("Cosh", x.clone()), position)?;
                let left_value = self.compile_normalization_value(&left, position)?;
                let right_value = self.compile_normalization_value(&right, position)?;
                return Ok(format!("(by\n  have _identity := Litex.{law} ({cosine}).val.arg ({cosine}).wd\n  change {left_value} = {right_value} at _identity\n  exact _identity{})", if reverse { ".symm" } else { "" }));
            }
            let native = self.compile_numeric_observation(x, position)?;
            let (arguments, normalization) = if matches!(proof, SinhAddition(_) | CoshAddition(_)) {
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(pair)) = x else {
                    unreachable!()
                };
                (
                    format!(
                        "({}).re ({}).re",
                        self.compile_numeric_observation(&pair.left, position)?.0,
                        self.compile_numeric_observation(&pair.right, position)?.0
                    ),
                    "simpa only [Complex.add_re] using",
                )
            } else if matches!(proof, SinhDoubleAngle(_) | CoshDoubleAngle(_)) {
                (format!("({}).re", native.0), "simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; exact")
            } else {
                (format!("({}).re", native.0), "exact")
            };
            let condition = if let Some(kind) = guarded {
                let object =
                    self.compile_object_reference(&hyperbolic(kind, x.clone()), position)?;
                format!("have _argument := Litex.NativeBridge.denoteRealOfDenoteNumber ({object}).val.arg {} ({object}).wd.1 {}; have _nonzero : ({}).re ≠ 0 := fun h => ({object}).wd.2 (_argument.trans (by rw [h]; rfl)); ", native.0, native.1, native.0)
            } else {
                String::new()
            };
            return self.compile_trig_native_identity(
                fact,
                &format!(
                    "{}{condition}{normalization} (Litex.{law} {arguments}{})",
                    if reverse { "symm; " } else { "" },
                    if guarded.is_some() { " _nonzero" } else { "" }
                ),
                position,
            );
        }
        Err(LeanCompileError::unsupported("Hyperbolic/EquationSubject"))
    }
}

fn num(n: i32) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.to_string())))
}
fn square(base: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(num(2)),
    }))
}
fn neg(arg: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(arg) }))
}
fn exp(arg: Obj) -> Obj {
    Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg: Box::new(arg) }))
}
fn hyperbolic(kind: &str, arg: Obj) -> Obj {
    let arg = Box::new(arg);
    Obj::HyperbolicOperator(match kind {
        "Sinh" => HyperbolicOperator::Sinh(Sinh { arg }),
        "Cosh" => HyperbolicOperator::Cosh(Cosh { arg }),
        "Tanh" => HyperbolicOperator::Tanh(Tanh { arg }),
        "Coth" => HyperbolicOperator::Coth(Coth { arg }),
        "Sech" => HyperbolicOperator::Sech(Sech { arg }),
        "Csch" => HyperbolicOperator::Csch(Csch { arg }),
        _ => unreachable!(),
    })
}
