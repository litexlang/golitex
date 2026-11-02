use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::prelude::*;

const CASES: [(&str, &str); 6] = [
    (
        include_str!("../../../lean/examples/logarithm_product_base/statement.lit"),
        "logarithmProductBaseValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_quotient_base/statement.lit"),
        "logarithmQuotientBaseValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_reciprocal/statement.lit"),
        "logarithmReciprocalValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_change_base/statement.lit"),
        "logarithmChangeBaseValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_argument_power/statement.lit"),
        "logarithmArgumentPowerValue",
    ),
    (
        include_str!("../../../lean/examples/logarithm_base_power/statement.lit"),
        "logarithmBasePowerValue",
    ),
];
fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn rule(proof: &mut VerifyEqualitySuccess) -> &mut EqualitySearchProofByBuiltinRule {
    let EqualFactSearchedProof::ByBuiltinRule(p) = &mut proof.searched_proof else {
        panic!("original selected log algebra leaf")
    };
    p
}
fn kind(p: &EqualitySearchProofByBuiltinRule) -> usize {
    use EqualitySearchProofByBuiltinRule as R;
    match p {
        R::LogProduct(_) => 0,
        R::LogQuotient(_) => 1,
        R::LogReciprocal(_) => 2,
        R::LogChangeOfBase(_) => 3,
        R::LogArgPower(_) => 4,
        R::LogBasePower(_) => 5,
        _ => panic!("selected log algebra variant"),
    }
}
fn base(p: &mut EqualitySearchProofByBuiltinRule) -> &mut LogAlgebraBaseProof {
    use EqualitySearchProofByBuiltinRule as R;
    match p {
        R::LogProduct(p) => &mut p.base_proof,
        R::LogQuotient(p) => &mut p.base_proof,
        R::LogReciprocal(p) => &mut p.base_proof,
        R::LogChangeOfBase(p) => &mut p.base_proof,
        R::LogArgPower(p) => &mut p.base_proof,
        R::LogBasePower(p) => &mut p.base_proof,
        _ => panic!(),
    }
}
fn positive(p: &mut EqualitySearchProofByBuiltinRule) -> &mut VerifyFactResult {
    use EqualitySearchProofByBuiltinRule as R;
    match p {
        R::LogProduct(p) => &mut p.left_argument_positive_proof,
        R::LogQuotient(p) => &mut p.numerator_positive_proof,
        R::LogReciprocal(p) => &mut p.argument_positive_proof,
        R::LogChangeOfBase(p) => &mut p.argument_positive_proof,
        R::LogArgPower(p) => &mut p.argument_positive_proof,
        R::LogBasePower(p) => &mut p.argument_positive_proof,
        _ => panic!(),
    }
}

#[test]
fn all_six_log_algebra_rules_replay_the_selected_guards_and_exact_shapes() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(kind(rule(equality(&mut run))), index);
        let output = compiler
            .compile_run(&run, "log_algebra")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, compiler.compile_run(&run, "log_algebra").unwrap());
    }
}

#[test]
fn log_algebra_preserves_reversed_equalities_and_all_legal_base_guards() {
    for (source, law) in CASES {
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let (left, right) = last.trim().split_once('=').unwrap();
        let reversed = format!("{prefix}\n        {right}={left}\n");
        for source in [
            reversed,
            source.replace("b!=1", "1<b"),
            source.replace("b!=1", "b<1"),
        ] {
            let (run, compiler) = super::execute(&source);
            let output = compiler
                .compile_run(&run, "log_algebra_profiles")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
            assert!(output.contains(&format!("Litex.{law}")));
        }
    }
}

#[test]
fn log_algebra_rejects_changed_positive_base_and_parent_wd_evidence() {
    for (source, _) in CASES {
        for change in ["positive", "base", "wd"] {
            let (mut run, compiler) = super::execute(source);
            let p = equality(&mut run);
            if change == "wd" {
                let p = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut p.left, &mut p.right);
            } else {
                let p = rule(p);
                if change == "positive" {
                    let child = super::atomic_proof_mut(positive(p));
                    let AtomicFact::LessFact(f) = &mut child.fact else {
                        panic!("original positive child")
                    };
                    f.right = Obj::Literal(Literal::Number(Number::new("7".into())));
                } else {
                    let LogAlgebraBaseProof::PositiveNonunit(p) = base(p) else {
                        panic!("original positive nonunit guard")
                    };
                    let AtomicFact::NotEqualFact(f) =
                        &mut super::atomic_proof_mut(&mut p.nonunit_proof).fact
                    else {
                        panic!()
                    };
                    f.right = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
            }
            compiler.compile_run(&run,change).expect_err("the original legal base, positive operand and parent constructor evidence are mandatory");
        }
    }
}

#[test]
fn ordered_log_algebra_children_cannot_be_exchanged() {
    for index in [0, 1, 3, 5] {
        let (mut run, compiler) = super::execute(CASES[index].0);
        use EqualitySearchProofByBuiltinRule as R;
        match rule(equality(&mut run)) {
            R::LogProduct(p) => std::mem::swap(
                &mut p.left_argument_positive_proof,
                &mut p.right_argument_positive_proof,
            ),
            R::LogQuotient(p) => std::mem::swap(
                &mut p.numerator_positive_proof,
                &mut p.denominator_positive_proof,
            ),
            R::LogChangeOfBase(p) => std::mem::swap(&mut p.base_proof, &mut p.chosen_base_proof),
            R::LogBasePower(p) => std::mem::swap(&mut p.exponent_real, &mut p.exponent_nonzero),
            _ => panic!(),
        }
        compiler
            .compile_run(&run, "swapped_log_children")
            .expect_err("each original child belongs to its exact ordered stage and subject");
    }
}

#[test]
fn log_domains_and_supported_power_representation_remain_explicit() {
    for source in [
        "forall b,x,y R+:\n    log(b,x*y)=log(b,x)+log(b,y)\n",
        "forall b R+,x,y R:\n    b!=1\n    =>:\n        log(b,x*y)=log(b,x)+log(b,y)\n",
        "forall b,x R+,n Z:\n    b!=1\n    =>:\n        log(b^n,x)=log(b,x)/n\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        assert!(
            !Runtime::new(command)
                .run_litex_code(source)
                .unwrap()
                .success
        );
    }
    let source = "forall b,x R+,r R:\n    b!=1\n    =>:\n        log(b,x^r)=r*log(b,x)\n";
    let (run, compiler) = super::execute(source);
    let error = compiler
        .compile_run(&run, "unsupported_real_power")
        .expect_err(
        "the current explicit model only represents supported natural/integer power certificates",
    );
    assert_eq!(error.route, "WD/Pow/Domain");
}
