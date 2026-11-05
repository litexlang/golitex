use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const UNARY: [&str; 12] = [
    r#"# Preserve at continuity under the neg formula on the complete real domain.
thm at_continuity_neg:
    ? forall f,g fn(x R) R, p R:
        $is_continuous_at(f,p)
        forall x R:
            g(x)=-f(x)
        =>:
            $is_continuous_at(g,p)
    by thm fn_continuous_at_neg(f,g,p) => $is_continuous_at(g,p)
"#,
    r#"# Preserve at continuity under the abs formula on the complete real domain.
thm at_continuity_abs:
    ? forall f,g fn(x R) R, p R:
        $is_continuous_at(f,p)
        forall x R:
            g(x)=abs(f(x))
        =>:
            $is_continuous_at(g,p)
    by thm fn_continuous_at_abs(f,g,p) => $is_continuous_at(g,p)
"#,
    r#"# Preserve at continuity under the scale formula on the complete real domain.
thm at_continuity_scale:
    ? forall f,g fn(x R) R, p R, c R:
        $is_continuous_at(f,p)
        forall x R:
            g(x)=c*f(x)
        =>:
            $is_continuous_at(g,p)
    by thm fn_continuous_at_scale(f,g,p,c) => $is_continuous_at(g,p)
"#,
    r#"# Preserve at continuity under the power formula on the complete real domain.
thm at_continuity_power:
    ? forall f,g fn(x R) R, p R, n N:
        $is_continuous_at(f,p)
        forall x R:
            g(x)=f(x)^n
        =>:
            $is_continuous_at(g,p)
    by thm fn_continuous_at_power(f,g,p,n) => $is_continuous_at(g,p)
"#,
    r#"# Preserve left continuity under the neg formula on the complete real domain.
thm left_continuity_neg:
    ? forall f,g fn(x R) R, p R:
        $is_continuous_left(f,p)
        forall x R:
            g(x)=-f(x)
        =>:
            $is_continuous_left(g,p)
    by thm fn_continuous_left_neg(f,g,p) => $is_continuous_left(g,p)
"#,
    r#"# Preserve left continuity under the abs formula on the complete real domain.
thm left_continuity_abs:
    ? forall f,g fn(x R) R, p R:
        $is_continuous_left(f,p)
        forall x R:
            g(x)=abs(f(x))
        =>:
            $is_continuous_left(g,p)
    by thm fn_continuous_left_abs(f,g,p) => $is_continuous_left(g,p)
"#,
    r#"# Preserve left continuity under the scale formula on the complete real domain.
thm left_continuity_scale:
    ? forall f,g fn(x R) R, p R, c R:
        $is_continuous_left(f,p)
        forall x R:
            g(x)=c*f(x)
        =>:
            $is_continuous_left(g,p)
    by thm fn_continuous_left_scale(f,g,p,c) => $is_continuous_left(g,p)
"#,
    r#"# Preserve left continuity under the power formula on the complete real domain.
thm left_continuity_power:
    ? forall f,g fn(x R) R, p R, n N:
        $is_continuous_left(f,p)
        forall x R:
            g(x)=f(x)^n
        =>:
            $is_continuous_left(g,p)
    by thm fn_continuous_left_power(f,g,p,n) => $is_continuous_left(g,p)
"#,
    r#"# Preserve right continuity under the neg formula on the complete real domain.
thm right_continuity_neg:
    ? forall f,g fn(x R) R, p R:
        $is_continuous_right(f,p)
        forall x R:
            g(x)=-f(x)
        =>:
            $is_continuous_right(g,p)
    by thm fn_continuous_right_neg(f,g,p) => $is_continuous_right(g,p)
"#,
    r#"# Preserve right continuity under the abs formula on the complete real domain.
thm right_continuity_abs:
    ? forall f,g fn(x R) R, p R:
        $is_continuous_right(f,p)
        forall x R:
            g(x)=abs(f(x))
        =>:
            $is_continuous_right(g,p)
    by thm fn_continuous_right_abs(f,g,p) => $is_continuous_right(g,p)
"#,
    r#"# Preserve right continuity under the scale formula on the complete real domain.
thm right_continuity_scale:
    ? forall f,g fn(x R) R, p R, c R:
        $is_continuous_right(f,p)
        forall x R:
            g(x)=c*f(x)
        =>:
            $is_continuous_right(g,p)
    by thm fn_continuous_right_scale(f,g,p,c) => $is_continuous_right(g,p)
"#,
    r#"# Preserve right continuity under the power formula on the complete real domain.
thm right_continuity_power:
    ? forall f,g fn(x R) R, p R, n N:
        $is_continuous_right(f,p)
        forall x R:
            g(x)=f(x)^n
        =>:
            $is_continuous_right(g,p)
    by thm fn_continuous_right_power(f,g,p,n) => $is_continuous_right(g,p)
"#,
];
const BINARY: [&str; 12] = [
    r#"# Preserve at continuity under the add formula on the complete real domain.
thm at_continuity_add:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_continuous_at(g,p)
        forall x R:
            h(x)=f(x)+g(x)
        =>:
            $is_continuous_at(h,p)
    by thm fn_continuous_at_add(f,g,h,p) => $is_continuous_at(h,p)
"#,
    r#"# Preserve at continuity under the subtract formula on the complete real domain.
thm at_continuity_subtract:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_continuous_at(g,p)
        forall x R:
            h(x)=f(x)-g(x)
        =>:
            $is_continuous_at(h,p)
    by thm fn_continuous_at_subtract(f,g,h,p) => $is_continuous_at(h,p)
"#,
    r#"# Preserve at continuity under the multiply formula on the complete real domain.
thm at_continuity_multiply:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_continuous_at(g,p)
        forall x R:
            h(x)=f(x)*g(x)
        =>:
            $is_continuous_at(h,p)
    by thm fn_continuous_at_multiply(f,g,h,p) => $is_continuous_at(h,p)
"#,
    r#"# Preserve at continuity under the divide formula on the complete real domain.
thm at_continuity_divide:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_continuous_at(g,p)
        forall x R:
            g(x)!=0
        forall x R:
            h(x)=f(x)/g(x)
        =>:
            $is_continuous_at(h,p)
    by thm fn_continuous_at_divide(f,g,h,p) => $is_continuous_at(h,p)
"#,
    r#"# Preserve left continuity under the add formula on the complete real domain.
thm left_continuity_add:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_continuous_left(g,p)
        forall x R:
            h(x)=f(x)+g(x)
        =>:
            $is_continuous_left(h,p)
    by thm fn_continuous_left_add(f,g,h,p) => $is_continuous_left(h,p)
"#,
    r#"# Preserve left continuity under the subtract formula on the complete real domain.
thm left_continuity_subtract:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_continuous_left(g,p)
        forall x R:
            h(x)=f(x)-g(x)
        =>:
            $is_continuous_left(h,p)
    by thm fn_continuous_left_subtract(f,g,h,p) => $is_continuous_left(h,p)
"#,
    r#"# Preserve left continuity under the multiply formula on the complete real domain.
thm left_continuity_multiply:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_continuous_left(g,p)
        forall x R:
            h(x)=f(x)*g(x)
        =>:
            $is_continuous_left(h,p)
    by thm fn_continuous_left_multiply(f,g,h,p) => $is_continuous_left(h,p)
"#,
    r#"# Preserve left continuity under the divide formula on the complete real domain.
thm left_continuity_divide:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_continuous_left(g,p)
        forall x R:
            g(x)!=0
        forall x R:
            h(x)=f(x)/g(x)
        =>:
            $is_continuous_left(h,p)
    by thm fn_continuous_left_divide(f,g,h,p) => $is_continuous_left(h,p)
"#,
    r#"# Preserve right continuity under the add formula on the complete real domain.
thm right_continuity_add:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_right(f,p)
        $is_continuous_right(g,p)
        forall x R:
            h(x)=f(x)+g(x)
        =>:
            $is_continuous_right(h,p)
    by thm fn_continuous_right_add(f,g,h,p) => $is_continuous_right(h,p)
"#,
    r#"# Preserve right continuity under the subtract formula on the complete real domain.
thm right_continuity_subtract:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_right(f,p)
        $is_continuous_right(g,p)
        forall x R:
            h(x)=f(x)-g(x)
        =>:
            $is_continuous_right(h,p)
    by thm fn_continuous_right_subtract(f,g,h,p) => $is_continuous_right(h,p)
"#,
    r#"# Preserve right continuity under the multiply formula on the complete real domain.
thm right_continuity_multiply:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_right(f,p)
        $is_continuous_right(g,p)
        forall x R:
            h(x)=f(x)*g(x)
        =>:
            $is_continuous_right(h,p)
    by thm fn_continuous_right_multiply(f,g,h,p) => $is_continuous_right(h,p)
"#,
    r#"# Preserve right continuity under the divide formula on the complete real domain.
thm right_continuity_divide:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_right(f,p)
        $is_continuous_right(g,p)
        forall x R:
            g(x)!=0
        forall x R:
            h(x)=f(x)/g(x)
        =>:
            $is_continuous_right(h,p)
    by thm fn_continuous_right_divide(f,g,h,p) => $is_continuous_right(h,p)
"#,
];
const COMPOSE: [&str; 4] = [
    r#"# Compose at continuity of the inner function with two-sided continuity of the outer function.
thm at_continuity_compose:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_at(f,p)
        $is_continuous_at(g,f(p))
        forall x R:
            h(x)=g(f(x))
        =>:
            $is_continuous_at(h,p)
    by thm fn_continuous_at_compose(f,g,h,p) => $is_continuous_at(h,p)
"#,
    r#"# Compose left continuity of the inner function with two-sided continuity of the outer function.
thm left_continuity_compose:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_left(f,p)
        $is_continuous_at(g,f(p))
        forall x R:
            h(x)=g(f(x))
        =>:
            $is_continuous_left(h,p)
    by thm fn_continuous_left_compose(f,g,h,p) => $is_continuous_left(h,p)
"#,
    r#"# Compose right continuity of the inner function with two-sided continuity of the outer function.
thm right_continuity_compose:
    ? forall f,g,h fn(x R) R, p R:
        $is_continuous_right(f,p)
        $is_continuous_at(g,f(p))
        forall x R:
            h(x)=g(f(x))
        =>:
            $is_continuous_right(h,p)
    by thm fn_continuous_right_compose(f,g,h,p) => $is_continuous_right(h,p)
"#,
    r#"# Compose functions whose input and intermediate value must remain positive.
thm continuity_compose_positive_domain:
    ? forall f fn(x R+) R+, g,h fn(x R+) R, p R+:
        $is_continuous_at(f,p)
        $is_continuous_at(g,f(p))
        forall x R+:
            h(x)=g(f(x))
        =>:
            $is_continuous_at(h,p)
    by thm fn_continuous_at_compose(f,g,h,p) => $is_continuous_at(h,p)
"#,
];
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
        &mut p.proof_steps[0]
    else {
        panic!("builtin invocation")
    };
    p
}
#[test]
fn unary_continuity_rejects_missing_invocation_evidence() {
    for source in &UNARY[..4] {
        for mutation in 0..3 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.dom_stores.clear(),
                _ => p.conclusions_wd.clear(),
            }
            c.compile_run(&run, "missing_unary_continuity_evidence")
                .expect_err("all original premises/stores/WD");
        }
    }
}
#[test]
fn unary_continuity_rejects_changed_domain_formula_or_side() {
    for source in UNARY {
        for mutation in 0..3 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match mutation {
                0 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(f)) = &mut b.requirements[7] else {
                        panic!("subset")
                    };
                    f.right = Obj::StandardSet(StandardSet::C);
                }
                1 => {
                    let Fact::ForallFact(f) = b.requirements.last_mut().unwrap() else {
                        panic!("formula")
                    };
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut f.then_facts[0]
                    else {
                        panic!("equality")
                    };
                    eq.right = b.arguments[0].clone();
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) =
                        &mut b.conclusions[0]
                    else {
                        panic!("continuity")
                    };
                    f.side = if f.side == RealApproachSide::Both {
                        RealApproachSide::Left
                    } else {
                        RealApproachSide::Both
                    };
                }
            }
            c.compile_run(&run, "changed_unary_continuity")
                .expect_err("original domains, formula and side");
        }
    }
}
#[test]
fn unary_continuity_rejects_a_changed_scalar_or_natural_exponent_domain() {
    for source in [UNARY[2], UNARY[3]] {
        let (mut run, c) = super::execute(source);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[10] else {
            panic!("operation parameter")
        };
        f.set = Obj::StandardSet(StandardSet::Z);
        c.compile_run(&run, "changed_continuity_parameter")
            .expect_err("real scalar / natural exponent");
    }
}
#[test]
fn binary_continuity_rejects_missing_stages_and_changed_domain_or_formula() {
    for source in &BINARY[..4] {
        for mutation in 0..5 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.dom_stores.clear(),
                2 => p.conclusions_wd.clear(),
                3 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(f)) =
                        &mut p.builtin.as_mut().unwrap().requirements[13]
                    else {
                        panic!("second domain inclusion")
                    };
                    f.right = Obj::StandardSet(StandardSet::C);
                }
                _ => {
                    let b = p.builtin.as_mut().unwrap();
                    let Fact::ForallFact(all) = b.requirements.last_mut().unwrap() else {
                        panic!("formula")
                    };
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut all.then_facts[0]
                    else {
                        panic!("equality")
                    };
                    eq.right = b.arguments[0].clone();
                }
            }
            c.compile_run(&run, "changed_binary_continuity")
                .expect_err("original stages, both domains and exact formula");
        }
    }
}
#[test]
fn quotient_continuity_requires_the_original_nonzero_point_call() {
    for source in [BINARY[3], BINARY[7], BINARY[11]] {
        let (mut run, c) = super::execute(source);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut b.requirements[15] else {
            panic!("point nonzero")
        };
        f.left = b.arguments[1].clone();
        c.compile_run(&run, "changed_continuity_denominator")
            .expect_err("the original denominator call at the point");
    }
}
#[test]
fn quotient_continuity_also_replays_the_formula_objects_nonzero_wd() {
    use crate::execute::execute_fact_stmt::verify_forall_fact::{
        VerifyForallFactProof, VerifyForallFactResult,
    };
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        ArithmeticOperatorObjWellDefinedProofByDef, DetailedObjWellDefinedProof,
        ObjWellDefinedProofByDef,
    };
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    let (mut run, c) = super::execute(BINARY[3]);
    let VerifyFactResult::ForallFact(all) = invocation(&mut run).dom_proofs.last_mut().unwrap()
    else {
        panic!("formula forall")
    };
    let VerifyForallFactResult::Success(proof) = all.as_mut() else {
        panic!("successful formula")
    };
    let wd = match proof {
        VerifyForallFactProof::ByKnownForallFact(p) => {
            let FactWellDefinedProof::Equality(wd) =
                &mut p.well_defined.as_detailed_mut().unwrap().then[0]
            else {
                panic!("formula equality")
            };
            &mut wd.as_detailed_mut().unwrap().right
        }
        VerifyForallFactProof::ByLocalIntroduction(p) => {
            &mut super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .right
        }
        _ => panic!("nonempty real domain"),
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
            ),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("original division constructor")
    };
    assert!(p.requirement_fact_verified.pop().is_some());
    c.compile_run(&run, "missing_formula_division_wd")
        .expect_err("formula WD remains required in addition to point nonzero");
}
#[test]
fn composition_continuity_rejects_missing_mapping_or_changed_outer_point_side() {
    for source in &COMPOSE[..3] {
        for mutation in 0..5 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                0 => {
                    p.dom_proofs.remove(14);
                }
                1 => p.dom_stores.clear(),
                2 => p.conclusions_wd.clear(),
                3 => {
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) =
                        &mut p.builtin.as_mut().unwrap().requirements[13]
                    else {
                        panic!("outer continuity")
                    };
                    f.side = RealApproachSide::Left;
                }
                _ => {
                    let b = p.builtin.as_mut().unwrap();
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) =
                        &mut b.requirements[13]
                    else {
                        panic!("outer continuity")
                    };
                    f.point = b.arguments[3].clone();
                }
            }
            c.compile_run(&run, "changed_composition_continuity")
                .expect_err("mapping and outer continuity at the actual inner value");
        }
    }
}
#[test]
fn composition_continuity_rejects_a_different_mapping_carrier_or_formula() {
    for mutation in 0..2 {
        let (mut run, c) = super::execute(COMPOSE[3]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::ForallFact(all) = &mut b.requirements[14] else {
                panic!("mapping")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f)) =
                &mut all.then_facts[0]
            else {
                panic!("mapped value")
            };
            f.set = Obj::StandardSet(StandardSet::C);
        } else {
            let Fact::ForallFact(all) = &mut b.requirements[15] else {
                panic!("formula")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) =
                &mut all.then_facts[0]
            else {
                panic!("composition equation")
            };
            f.right = b.arguments[0].clone();
        }
        c.compile_run(&run, "changed_composition_mapping")
            .expect_err("original mapping carrier and nested call formula");
    }
}
