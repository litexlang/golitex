use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const GCD: &str = include_str!("../../../lean/examples/gcd_prime_rule/statement.lit");
const PRODUCT: &str = include_str!("../../../lean/examples/prime_product_rule/statement.lit");
const POWER: &str = include_str!("../../../lean/examples/prime_power_rule/statement.lit");
const DIVISOR: &str = include_str!("../../../lean/examples/prime_divisor_rule/statement.lit");
const CONCRETE: &str = include_str!("../../../lean/examples/number_theory_concrete/statement.lit");

#[test]
fn prime_theorems_replay_all_four_generic_contracts_and_concrete_calls() {
    for (source, law) in [
        (GCD, "gcdWithPrimeValue"),
        (PRODUCT, "primeDividesProductValue"),
        (POWER, "primeDividesPowerValue"),
        (DIVISOR, "primeDivisorWitness"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "prime_theorem")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, compiler.compile_run(&run, "prime_theorem").unwrap());
    }
    let (run, compiler) = super::execute(CONCRETE);
    let output = compiler
        .compile_run(&run, "prime_concrete")
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(output.contains("variable [_setSemantics : Litex.SetSemantics M]"));
    for law in [
        "gcdWithPrimeValue",
        "primeDividesProductValue",
        "primeDividesPowerValue",
        "primeDivisorWitness",
    ] {
        assert!(output.contains(law));
    }
    let mixed = format!(
        "{CONCRETE}\n{}",
        include_str!("../../../lean/examples/bijective_unique_preimages/statement.lit")
    );
    let (run, compiler) = super::execute(&mixed);
    let output = compiler.compile_run(&run, "prime_function_parent").unwrap();
    assert!(output.contains("variable [_functionSemantics : Litex.FunctionSemantics M]"));
    assert!(!output.contains("variable [_setSemantics"));
}

#[test]
fn prime_theorems_require_original_premises_stores_and_conclusion_wd() {
    for source in [GCD, PRODUCT, POWER, DIVISOR] {
        for change in ["proof", "order", "store", "wd", "arguments", "future"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "order" => p.dom_proofs.swap(0, 1),
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "arguments" => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                "future" => {
                    let id = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof
                    else {
                        panic!()
                    };
                    cite.cite_fact_id = id;
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, change)
                .expect_err("original ordered theorem evidence and stores");
        }
    }
}

#[test]
fn prime_theorems_reject_changed_prime_dividend_exponent_and_witness_contracts() {
    for source in [GCD, PRODUCT, POWER, DIVISOR] {
        for change in ["premise", "conclusion"] {
            let (mut run, compiler) = super::execute(source);
            let builtin = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "premise" {
                if source == DIVISOR {
                    let Fact::AtomicFact(AtomicFact::LessEqualFact(p)) =
                        &mut builtin.requirements[1]
                    else {
                        panic!()
                    };
                    p.left = Obj::Literal(Literal::Number(Number::new("1".into())));
                } else {
                    let index = if source == GCD { 2 } else { 3 };
                    let Fact::AtomicFact(AtomicFact::PrimeFact(p)) =
                        &mut builtin.requirements[index]
                    else {
                        panic!()
                    };
                    p.value = builtin.arguments[0].clone();
                }
            } else {
                match &mut builtin.conclusions[0] {
                    Fact::OrFact(p) => p.facts.swap(0, 1),
                    Fact::AtomicFact(AtomicFact::DvdFact(p)) => {
                        p.right = builtin.arguments[0].clone()
                    }
                    Fact::ExistFact(p) => {
                        p.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX)
                    }
                    _ => panic!(),
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("the exact selected prime theorem schema");
        }
    }
}

#[test]
fn prime_divisor_and_divisibility_do_not_accept_missing_prime_or_lower_bound() {
    for source in [
        "release thm prime_divisor(1)\n",
        "release thm gcd_with_prime_is_one_or_prime(14,4)\n",
        "release thm prime_divides_product(6,10,4)\n",
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
}
