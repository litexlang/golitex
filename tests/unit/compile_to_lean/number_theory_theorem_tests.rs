use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const GCD: &str = r#"thm checked_gcd_prime_rule:
    ? forall a Z,p N+:
        $prime(p)
        =>:
            gcd(a,p)=1 or gcd(a,p)=p
    release thm gcd_with_prime_is_one_or_prime(a,p)
"#;
const PRODUCT: &str = r#"thm checked_prime_product_rule:
    ? forall a,b Z,p N+:
        $prime(p)
        $dvd(a*b,p)
        =>:
            $dvd(a,p) or $dvd(b,p)
    release thm prime_divides_product(a,b,p)
"#;
const POWER: &str = r#"thm checked_prime_power_rule:
    ? forall a Z,k,p N+:
        $prime(p)
        $dvd(a^k,p)
        =>:
            $dvd(a,p)
    release thm prime_divides_power(a,k,p)
"#;
const DIVISOR: &str = r#"thm checked_prime_divisor_rule:
    ? forall m N+:
        2<=m
        =>:
            exist p N+ st {$prime(p),m%p=0}
    release thm prime_divisor(m)
"#;

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
