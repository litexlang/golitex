use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule as OrderRule;

#[test]
fn rounding_examples_replay_values_domains_bounds_and_function_calls() {
    for source in [
        include_str!("../../../lean/examples/rounding_integers/statement.lit"),
        include_str!("../../../lean/examples/rounding_bounds/statement.lit"),
        include_str!("../../../lean/examples/shifted_rounding_function/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "rounding").unwrap();
        assert!(output.contains("Litex.rounding"));
        assert_eq!(output, compiler.compile_run(&run, "rounding").unwrap());
    }
}

#[test]
fn rounding_integer_rules_preserve_each_selected_family_and_equality_orientation() {
    for expression in ["floor(n)", "ceil(n)", "floor(ceil(n))", "ceil(floor(n))"] {
        for reversed in [false, true] {
            let equality = if reversed {
                format!("n = {expression}")
            } else {
                format!("{expression} = n")
            };
            let (run, compiler) = super::execute(&format!("forall n Z:\n    {equality}\n"));
            let output = compiler.compile_run(&run, "integer_rounding").unwrap();
            assert!(output.contains("Litex.roundingOfInteger"));
        }
    }
}

#[test]
fn rounding_integer_rule_rejects_missing_and_noninteger_premises() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute("forall n Z:\n    floor(n) = n\n");
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::FloorOfInteger(proof),
        ) = &mut p.searched_proof
        else {
            panic!("original floor identity")
        };
        if missing {
            proof.proof_of_requirement_facts.clear();
        } else {
            let requirement = super::atomic_proof_mut(&mut proof.proof_of_requirement_facts[0]);
            let AtomicFact::InFact(member) = &mut requirement.fact else {
                panic!("integer premise")
            };
            member.set = Obj::StandardSet(StandardSet::R);
        }
        assert_eq!(
            compiler.compile_run(&run, "bad_integer").unwrap_err().route,
            if missing {
                "Rounding/IntegerRequirement"
            } else {
                "Rounding/IntegerCarrier"
            }
        );
    }
}

#[test]
fn rounding_monotonicity_rejects_reversed_argument_order() {
    for operation in ["floor", "ceil"] {
        let (mut run, compiler) = super::execute(&format!(
            "forall x, y R:\n    x <= y\n    =>:\n        {operation}(x) <= {operation}(y)\n"
        ));
        let universal = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
        ) = &mut p.searched_proof
        else {
            panic!("rounding order")
        };
        let premise = match rule {
            OrderRule::FloorMonotone(p) => &mut p.argument_order,
            OrderRule::CeilMonotone(p) => &mut p.argument_order,
            _ => panic!("selected monotonicity"),
        };
        let AtomicFact::LessEqualFact(order) = &mut super::atomic_proof_mut(premise).fact else {
            panic!("argument order")
        };
        std::mem::swap(&mut order.left, &mut order.right);
        assert_eq!(
            compiler
                .compile_run(&run, "bad_monotone")
                .unwrap_err()
                .route,
            "Rounding/OrderPremise"
        );
    }
}

#[test]
fn rounding_bound_rejects_the_other_constructor_rule() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::rounding_definition_bounds::CeilUpperBoundProof;
    let (mut run, compiler) = super::execute("forall x R:\n    floor(x) <= x\n");
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    p.searched_proof = AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(OrderRule::CeilUpperBound(
            CeilUpperBoundProof::new(),
        )),
    );
    assert_eq!(
        compiler.compile_run(&run, "bad_bound").unwrap_err().route,
        "Rounding/BoundArgument"
    );
}

#[test]
fn rounding_wd_rejects_missing_domain_and_reuses_original_children() {
    for operation in ["floor", "ceil"] {
        let (mut run, compiler) = super::execute(&format!("have x R\n$is_set({operation}(x))\n"));
        let fact = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[1]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::ArithmeticOperator(p),
            ..
        } = &mut fact.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("rounding WD")
        };
        match p {
            ArithmeticOperatorObjWellDefinedProofByDef::Floor(p) => {
                p.requirement_fact_verified.clear()
            }
            ArithmeticOperatorObjWellDefinedProofByDef::Ceil(p) => {
                p.requirement_fact_verified.clear()
            }
            _ => panic!("original rounding constructor"),
        }
        assert_eq!(
            compiler
                .compile_run(&run, "missing_rounding_wd")
                .unwrap_err()
                .route,
            "WD/RoundingStages"
        );
        let (run, compiler) = super::execute(&format!(
            "have x R\n$is_set({operation}(x) + 1)\n$is_set({operation}(x))\n"
        ));
        let output = compiler.compile_run(&run, "rounding_reuse").unwrap();
        assert_eq!(
            output.matches(&format!("Litex.{operation} ")).count(),
            1,
            "{output}"
        );
    }
}

#[test]
fn rounding_does_not_accept_complex_only_domains_or_false_bounds() {
    for source in [
        "have x C\n$is_set(floor(x))\n",
        "floor(-3 / 2) = -1\n",
        "ceil(-3 / 2) = -2\n",
        "forall x R:\n    x <= floor(x)\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "false_rounding")
            .is_err());
    }
}
