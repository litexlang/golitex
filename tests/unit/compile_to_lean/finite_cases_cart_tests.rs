use crate::compile_to_lean::LitexToLeanCompiler;
use crate::prelude::*;

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("run");
    assert!(
        result.success && result.session_error.is_none(),
        "must verify: {source}"
    );
    (result, LitexToLeanCompiler::new(runtime))
}

const CLOSED: &str = "forall row 1...3:\n    row=1 or row=2 or row=3\n";
const HALF_OPEN: &str = "forall row range(1,4):\n    3=row or row=1 or 2=row or row=0 or row=2\n";
const CASES: &str = "have fn three_row_cases(row 1...3) R by cases:\n    case row=1: 10\n    case row=2: 20\n    case row=3: 30\nthree_row_cases(2)=20\n";
const CART: &str = "forall S set:\n    cart_n(S,3)=cart(S,S,S)\n    cart(S,S,S)=cart_n(S,3)\n    cart_n(S,1)=cart(S)\n    cart_n(S,0)=cart()\ncart(R,R,R) $subset cart_n(R,3)\ncart_n(R,3) $subset cart(R,R,R)\n";

#[test]
fn finite_cases_cart_focused_replay() {
    for (name, source) in [
        ("cartesian_membership_transport", "forall p cart(R,R,R):\n    p $in cart_n(R,3)\nforall p cart_n(R,3):\n    p $in cart(R,R,R)\n"),
        ("closed_integer_cover", CLOSED),
        ("half_open_integer_cover", HALF_OPEN),
        ("integer_case_function", CASES),
        ("homogeneous_cartesian_carriers", CART),
        (
            "integer_cover_alias",
            "have I set = 1...3\nforall row I:\n    row=1 or row=2 or row=3\n",
        ),
        (
            "known_cartesian_factors",
            "have S set = R\nhave n N = 3\ncart(S,R,S)=cart_n(R,n)\n",
        ),
        (
            "negative_integer_cover",
            "forall row closed_range(-1,1):\n    row=-1 or row=0 or row=1\n",
        ),
    ] {
        let (run, compiler) = checked(source);
        let output = compiler
            .compile_run(&run, name)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        if let Some(dir) = std::env::var_os("LITEX_FINITE_CASES_CART_LEAN_OUTPUT") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}.lean")),
                output,
            )
            .unwrap();
        }
    }
}

#[test]
fn finite_cases_cart_rejection_boundaries_keep_context() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    });
    assert!(rt.run_litex_code("have anchor R = 2").unwrap().success);
    for source in [
        "forall row 1...3:\n    row=1 or row=3",
        "forall row 1...3:\n    row=1 or row=2",
        "forall row range(1,4):\n    row=2 or row=3",
        "forall x 1...3, y 1...3:\n    x=1 or y=2 or x=3",
        "forall x cc(1,3):\n    x=1 or x=2 or x=3",
        "forall x Z:\n    x=1 or x=2 or x=3",
        "forall x 1...1025:\n    x=1 or x=1025",
        "cart_n(R,2)=cart(R,R,R)",
        "cart_n(R,3)=cart(R,R,C)",
        "cart_n(R,3)=cart(cart(R,R),R)",
        "cart_n(R,1)=R",
        "cart(R,R,C) $subset cart_n(R,3)",
        "$has_partial_derivative_at(fn(q cart(R,R,R): q(1)>0) R {q(1)},(-1,0,0),3,1,1)",
        "have fn incomplete(row 1...3) R by cases:\n    case row=1: 10\n    case row=3: 30",
        "have fn overlap(row 1...3) R by cases:\n    case row=1: 10\n    case row=2: 20\n    case row=3: 30\n    case row=3: 40",
    ] {
        let run=rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "must reject without stopping: {source}");
        assert!(rt.run_litex_code("anchor+1=3").unwrap().success);
    }
}

fn disjunction(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut run.statement_results[0]
    else {
        panic!("fact")
    };
    let VerifyFactResult::ForallFact(result) = &mut fact.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        result.as_mut()
    else {
        panic!("local forall")
    };
    let VerifyFactResult::OrFact(result) = &mut proof.proved_then_facts[0].verify_result else {
        panic!("Or")
    };
    let VerifyOrFactResult::Success(proof) = result.as_mut() else {
        panic!("success")
    };
    proof
}

#[test]
fn finite_cases_cart_replay_rejects_corrupt_cover_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = checked(CLOSED);
        let proof = disjunction(&mut run);
        let OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::ClosedIntegerRangeEqualityCover(p),
        ) = &mut proof.searched_proof
        else {
            panic!("selected range rule")
        };
        match mutation {
            0 => p.branch_indices.swap(0, 1),
            1 => {
                p.subject = Obj::Literal(Literal::Number(Number {
                    normalized_value: "1".into(),
                }))
            }
            2 => p.interval = Obj::StandardSet(StandardSet::Z),
            3 => p.carrier_equal.path.push((
                Obj::StandardSet(StandardSet::R),
                Obj::StandardSet(StandardSet::Z),
                FactId::new(999999),
            )),
            4 => {
                let VerifyFactResult::AtomicExceptEquality(result) = &mut p.membership else {
                    panic!("member")
                };
                let VerifyAtomicExceptEqualityFactResult::Success(member) = result.as_mut() else {
                    panic!("member success")
                };
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut member.searched_proof
                else {
                    panic!("member citation")
                };
                cite.cite_fact_id = FactId::new(999999);
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "corrupt_cover").is_err());
    }
}

#[test]
fn finite_cases_cart_multivariable_domain_consumer() {
    let (run, _) = checked("forall p cart(R,R,R):\n    $has_partial_derivative_at(fn(q cart(R,R,R)) R {q(1)},p,3,1,1)\n");
    assert!(run.success);
}

#[test]
fn finite_cases_cart_replay_rejects_corrupt_cartesian_evidence() {
    for mutation in 0..4 {
        let (mut run, compiler) = checked("cart(R,R,R)=cart_n(R,3)\n");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut run.statement_results[0]
        else {
            panic!("fact")
        };
        let VerifyFactResult::Equality(result) = &mut fact.verify_result else {
            panic!("equal")
        };
        let VerifyEqualityResult::Success(proof) = result.as_mut() else {
            panic!("success")
        };
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::HomogeneousCartesianEqualsFiniteSequence(p),
        ) = &mut proof.searched_proof
        else {
            panic!("cart rule")
        };
        match mutation {
            0 => p.dimension = 2,
            1 => {
                p.factor_equalities.pop();
            }
            2 | 3 => {
                let Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) = &mut proof.fact.right
                else {
                    panic!("sequence")
                };
                if mutation == 2 {
                    sequence.set = Box::new(Obj::StandardSet(StandardSet::C));
                } else {
                    sequence.n = Box::new(Obj::Literal(Literal::Number(Number {
                        normalized_value: "2".into(),
                    })));
                }
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "corrupt_cartesian").is_err());
    }
}
