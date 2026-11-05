use super::rounding_bounds_tests::equality;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_identities::ElementaryIdentitySearchProofByBuiltinRule as Rule;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IntegerOperatorObjWellDefinedProofByDef as IntegerWd;
use crate::prelude::*;

const ADD: &str = r#"thm checked_gcd_add_argument:
    ? forall a Z,b N+:
        gcd(a+b,b)=gcd(a,b)
    gcd(a+b,b)=gcd(a,b)
"#;
const NEG: &str = r#"thm checked_gcd_negation:
    ? forall a Z,b N+:
        gcd(-a,b)=gcd(a,b)
    gcd(-a,b)=gcd(a,b)
"#;
const SCALE: &str = r#"thm checked_gcd_positive_scale:
    ? forall a,b,k N+:
        gcd(k*a,k*b)=k*gcd(a,b)
    gcd(k*a,k*b)=k*gcd(a,b)
"#;
const MOD: &str = r#"thm checked_remainder_shift:
    ? forall a,k Z,m N+:
        (a+k*m)%m=a%m
    (a+k*m)%m=a%m
"#;
const CART: &str = r#"thm checked_cartesian_union:
    ? forall S,T,U set:
        cart(S,union(T,U))=union(cart(S,T),cart(S,U))
    cart(S,union(T,U))=union(cart(S,T),cart(S,U))
"#;

fn rule(run: &mut RunLitexCodeResult) -> &mut Rule {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ElementaryIdentity(p),
    ) = &mut equality(run).searched_proof
    else {
        panic!("original selected elementary rule")
    };
    p
}

#[test]
fn integer_and_cartesian_identities_replay_all_five_original_variants() {
    for (source, law) in [
        (ADD, "gcdAddArgumentValue"),
        (NEG, "gcdNegationValue"),
        (SCALE, "gcdPositiveScaleValue"),
        (MOD, "remainderIntegerShiftValue"),
        (CART, "cartesianUnionValue"),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert!(matches!(
            rule(&mut run),
            Rule::GcdAddArgument(_)
                | Rule::GcdNegation(_)
                | Rule::GcdPositiveScale(_)
                | Rule::RemainderIntegerShift(_)
                | Rule::CartesianUnion(_)
        ));
        let output = compiler
            .compile_run(&run, "integer_cartesian")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "integer_cartesian").unwrap()
        );
    }
    for source in [
        "forall a Z,b N+:\n    gcd(b+a,b)=gcd(a,b)\n",
        "forall a Z,b N+:\n    gcd(a,b)=gcd(a+b,b)\n",
        "forall a Z,b N+:\n    gcd(a,b)=gcd(-a,b)\n",
        "forall a,b,k N+:\n    k*gcd(a,b)=gcd(k*a,k*b)\n",
        "forall a,k Z,m N+:\n    a%m=(a+k*m)%m\n",
        "forall S,T,U set:\n    union(cart(S,T),cart(S,U))=cart(S,union(T,U))\n",
        "forall T,U set:\n    cart({},union(T,U))=union(cart({},T),cart({},U))\n",
        "forall S,U set:\n    cart(S,union({},U))=union(cart(S,{}),cart(S,U))\n",
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "orientation_empty")
            .unwrap_or_else(|e| panic!("{e}"));
    }
}

#[test]
fn positive_scale_and_remainder_require_original_ordered_membership_children() {
    for change in ["order", "subject", "future"] {
        let (mut run, compiler) = super::execute(SCALE);
        let id = equality(&mut run).fact.fact_id;
        let Rule::GcdPositiveScale(p) = rule(&mut run) else {
            panic!()
        };
        match change {
            "order" => std::mem::swap(&mut p.first_positive, &mut p.factor_positive),
            "subject" => {
                let AtomicFact::InFact(f) =
                    &mut super::atomic_proof_mut(&mut p.first_positive).fact
                else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::N);
            }
            "future" => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut super::atomic_proof_mut(&mut p.first_positive).searched_proof
                else {
                    panic!()
                };
                cite.cite_fact_id = id;
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("original a,b,k positive memberships in source order");
    }
    let (mut run, compiler) = super::execute(MOD);
    let Rule::RemainderIntegerShift(p) = rule(&mut run) else {
        panic!()
    };
    let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(&mut p.multiplier_integer).fact else {
        panic!()
    };
    f.set = Obj::StandardSet(StandardSet::R);
    compiler
        .compile_run(&run, "multiplier")
        .expect_err("original integer multiplier");
}

#[test]
fn integer_identities_retain_original_gcd_and_modulus_wd_guards() {
    for source in [ADD, NEG, SCALE, MOD] {
        let (mut run, compiler) = super::execute(source);
        let wd = &mut equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left;
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IntegerOperator(p),
            ..
        } = wd.as_detailed_mut().unwrap()
        else {
            panic!("original integer constructor WD")
        };
        match p {
            IntegerWd::Gcd(p) => {
                p.requirement_fact_verified.pop();
            }
            IntegerWd::Mod(p) => {
                p.requirement_fact_verified.pop();
            }
            _ => panic!(),
        }
        compiler
            .compile_run(&run, "missing_guard")
            .expect_err("native identity cannot bypass original WD");
    }
}

#[test]
fn elementary_integer_and_cartesian_certificates_cannot_change_operations_or_factors() {
    for (source, target) in [(ADD, NEG), (ADD, CART), (CART, ADD)] {
        let (mut original, _) = super::execute(source);
        let (mut run, compiler) = super::execute(target);
        std::mem::swap(
            &mut equality(&mut original).searched_proof,
            &mut equality(&mut run).searched_proof,
        );
        compiler
            .compile_run(&run, "wrong_operation")
            .expect_err("exact selected operation and factors");
    }
    for source in [
        "forall a Z,b N+:\n    gcd(-a,b)=-gcd(a,b)\n",
        "forall S,T,U set:\n    cart(S,union(T,U))=union(cart(S,T),cart(T,U))\n",
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
