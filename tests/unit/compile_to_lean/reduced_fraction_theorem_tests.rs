use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const SOURCE: &str = r#"thm checked_rational_reduced_fraction:
    ? forall x Q:
        exist! p Z,d N+ st {x=p/d,gcd(p,d)=1}
    release thm rational_has_unique_reduced_fraction(x)
"#;

#[test]
fn reduced_fraction_keeps_original_requirement_store_wd_and_prior_citation() {
    for change in ["proof", "store", "wd", "future", "argument"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = invocation(&mut run);
        match change {
            "proof" => p.dom_proofs.clear(),
            "store" => p.dom_stores.clear(),
            "wd" => p.conclusions_wd.clear(),
            "argument" => p.builtin.as_mut().unwrap().arguments.clear(),
            "future" => {
                let id = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof
                else {
                    panic!("original rational membership citation")
                };
                cite.cite_fact_id = id;
            }
            _ => unreachable!(),
        }
        compiler.compile_run(&run,change).expect_err("original rational requirement, publication, unique WD and argument identity are mandatory");
    }
}

#[test]
fn reduced_fraction_rejects_changed_uniqueness_binders_reduction_and_ratio() {
    for change in [
        "plain_exist",
        "carrier",
        "binder",
        "body_order",
        "ratio",
        "gcd",
        "one",
        "rational",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change == "rational" {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[0] else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::ExistUniqueFact(f) = &mut b.conclusions[0] else {
                panic!("unique original conclusion")
            };
            match change {
                "plain_exist" => b.conclusions[0] = Fact::ExistFact(f.clone()),
                "carrier" => {
                    f.typed_parameters.groups[1].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::Z))
                }
                "binder" => {
                    f.typed_parameters.groups[1].params[0].id =
                        f.typed_parameters.groups[0].params[0].id
                }
                "body_order" => f.facts.swap(0, 1),
                "ratio" => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(e)) = &mut f.facts[0]
                    else {
                        panic!()
                    };
                    let Obj::ArithmeticOperator(ArithmeticOperator::Div(d)) = &mut e.right else {
                        panic!()
                    };
                    std::mem::swap(&mut d.left, &mut d.right);
                }
                "gcd" => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(e)) = &mut f.facts[1]
                    else {
                        panic!()
                    };
                    let Obj::IntegerOperator(IntegerOperator::Gcd(g)) = &mut e.left else {
                        panic!()
                    };
                    std::mem::swap(&mut g.left, &mut g.right);
                }
                "one" => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(e)) = &mut f.facts[1]
                    else {
                        panic!()
                    };
                    e.right = Obj::Literal(Literal::Number(Number::new("2".into())));
                }
                _ => unreachable!(),
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "retain unique positive-denominator normalized fraction schema in original order",
        );
    }
}

#[test]
fn reduced_fraction_does_not_accept_arbitrary_real_or_complex_input() {
    for source in [
        "release thm rational_has_unique_reduced_fraction(i)\n",
        "forall x R:\n    exist! p Z,d N+ st {x=p/d,gcd(p,d)=1}\n",
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
