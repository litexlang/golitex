use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const FROM: &str =
    include_str!("../../../lean/examples/unary_derivative_builtin_from_limit/statement.lit");
const TO: &str =
    include_str!("../../../lean/examples/unary_derivative_builtin_to_limit/statement.lit");

#[test]
fn derivative_quotient_builtins_replay_both_original_directions() {
    for (source, law) in [
        (FROM, "derivativeOfQuotientGraph"),
        (TO, "derivativeQuotientGraph"),
        (
            include_str!(
                "../../../lean/examples/unary_derivative_builtin_positive_from_limit/statement.lit"
            ),
            "derivativeOfQuotientGraph",
        ),
        (
            include_str!(
                "../../../lean/examples/unary_derivative_builtin_guarded_to_limit/statement.lit"
            ),
            "derivativeQuotientGraph",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "derivative_quotient")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "derivative_quotient").unwrap()
        );
    }
}

#[test]
fn derivative_quotient_builtins_reject_changed_prerequisite_and_output_stages() {
    for source in [FROM, TO] {
        for change in ["proof", "store", "output_wd", "point_domain", "signature"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => p.dom_proofs.swap(0, 3),
                "store" => p.dom_stores.swap(0, 3),
                "output_wd" => p.conclusions_wd.clear(),
                "point_domain" => {
                    let Fact::AtomicFact(AtomicFact::InFact(m)) =
                        &mut p.builtin.as_mut().unwrap().requirements[3]
                    else {
                        panic!()
                    };
                    m.set = Obj::StandardSet(StandardSet::RPos);
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(m)) =
                        &mut p.builtin.as_mut().unwrap().requirements[0]
                    else {
                        panic!()
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(f)) = &mut m.set else {
                        panic!()
                    };
                    f.set_bound_parameters.groups[0].param_type =
                        Box::new(Obj::StandardSet(StandardSet::RPos));
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "original ordered stages, output WD and captured point domain are required",
            );
        }
    }
}

#[test]
fn derivative_quotient_builtins_reject_changed_puncture_and_difference_formula() {
    for source in [FROM, TO] {
        for change in [
            "point",
            "value",
            "approach",
            "domain",
            "codomain",
            "guard",
            "denominator",
            "numerator",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            let builtin = p.builtin.as_mut().unwrap();
            let fact = if source == FROM {
                &mut builtin.requirements[6]
            } else {
                &mut builtin.conclusions[0]
            };
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(limit)) = fact else {
                panic!()
            };
            match change {
                "point" => {
                    limit.approach = LimitApproach::AtPoint(Box::new(super::number_object("0")))
                }
                "value" => limit.value = super::number_object("0"),
                "approach" => limit.approach = LimitApproach::AtPositiveInfinity,
                _ => {
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(q)) = &mut limit.function
                    else {
                        panic!()
                    };
                    match change {
                        "domain" => {
                            q.body.set_bound_parameters.groups[0].param_type =
                                Box::new(Obj::StandardSet(StandardSet::RPos))
                        }
                        "codomain" => q.body.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
                        "guard" => q.body.dom_facts.clear(),
                        _ => {
                            let Obj::ArithmeticOperator(ArithmeticOperator::Div(d)) =
                                q.equal_to.as_mut()
                            else {
                                panic!()
                            };
                            if change == "denominator" {
                                d.right = Box::new(super::number_object("1"));
                            } else {
                                d.left = Box::new(super::number_object("0"));
                            }
                        }
                    }
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "the limit must use the actual punctured source quotient, approach and value",
            );
        }
    }
}
