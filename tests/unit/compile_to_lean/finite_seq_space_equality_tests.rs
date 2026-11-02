use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::prelude::*;
const CLOSED: &str = "finite_seq(R,3)=fn(replay34_i closed_range(1,3)) R\n";
const SYMBOLIC: &str = "forall replay34_A set,replay34_n N:\n    finite_seq(replay34_A,replay34_n)=fn(replay34_k closed_range(1,replay34_n)) replay34_A\n";
const POSITIVE: &str = "finite_seq(R,3)=fn(replay34_j N+:replay34_j<=3) R\n";
const HALF: &str = "finite_seq(R,3)=fn(replay34_hi range(1,4)) R\n";
const ZERO: &str = "finite_seq(R,0)=fn(replay34_e {}) R\n";
const ALL: &[&str] = &[
"finite_seq(R,3)=fn(replay34_i closed_range(1,3)) R\n",
"forall replay34_A set,replay34_n N:\n    finite_seq(replay34_A,replay34_n)=fn(replay34_k closed_range(1,replay34_n)) replay34_A\n",
"finite_seq(R,3)=fn(replay34_j N+:replay34_j<=3) R\n",
"forall replay34_PA set,replay34_pn N:\n    finite_seq(replay34_PA,replay34_pn)=fn(replay34_pk N+:replay34_pk<=replay34_pn) replay34_PA\n",
"finite_seq(R,0)=fn(replay34_e {}) R\n",
"finite_seq(R,0)=fn(replay34_zp N+:replay34_zp<=0) R\n",
"finite_seq(R,3)=fn(replay34_hi range(1,4)) R\n",
"forall replay34_rA set,replay34_rn N:\n    fn(replay34_ri closed_range(1,replay34_rn)) replay34_rA=finite_seq(replay34_rA,replay34_rn)\n",
"finite_seq({},3)=fn(replay34_ci closed_range(1,3)) {}\n",
"forall replay34_ret_A set,replay34_h fn(replay34_t R) N,replay34_a R:\n    replay34_h(replay34_a) $in N\n    finite_seq(replay34_ret_A,replay34_h(replay34_a))=fn(replay34_ri closed_range(1,replay34_h(replay34_a))) replay34_ret_A\n",
"let replay34_FS=fn(replay34_sv R) R\nfinite_seq(replay34_FS,2)=fn(replay34_si closed_range(1,2)) replay34_FS\n",
"forall replay34_NA set,replay34_NN N:\n    finite_seq(replay34_NA,replay34_NN)=fn(replay34_NK closed_range(1,replay34_NN)) replay34_NA\nfinite_seq(fn(replay34_nv R) R,2)=fn(replay34_ng closed_range(1,2)) fn(replay34_nv R) R\n"
];

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!("original fact")
    };
    let result = match &mut p.verify_result {
        VerifyFactResult::ForallFact(p) => {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!("original local forall")
            };
            &mut p.proved_then_facts.last_mut().unwrap().verify_result
        }
        p => p,
    };
    super::equality_proof_mut(result)
}
fn signature(run: &mut RunLitexCodeResult) -> &mut FnSet {
    let Obj::FunctionSpace(FunctionSpace::FnSet(p)) = &mut equality(run).fact.right else {
        panic!()
    };
    p
}
fn natural(run: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    let p = equality(run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(p)),
        ..
    } = p
    else {
        panic!("original finite sequence construction")
    };
    &mut p.requirement_fact_verified[1]
}
fn reject(run: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, label: &str) {
    assert!(
        super::compile_run(run, c, label).is_err(),
        "changed original evidence accepted: {label}"
    );
}
#[test]
fn seqspace_replays_all_original_spellings_orientations_and_nested_reuse() {
    for source in &ALL[..ALL.len() - 1] {
        let (run, c) = super::execute(source);
        let out = super::compile_run(&run, &c, "finite_spaces").unwrap();
        assert_eq!(out, super::compile_run(&run, &c, "finite_spaces").unwrap());
    }
    // The original general-theorem constructor match is covered by batch35.
    let (run, c) = super::execute(ALL.last().unwrap());
    super::compile_run(&run, &c, "nested_general_replay").unwrap();
}
#[test]
fn seqspace_keeps_canonical_complete_domain_validator_strict() {
    for source in [POSITIVE, HALF] {
        let (mut run, c) = super::execute(source);
        super::compile_run(&run, &c, "noncanonical_equality_only").unwrap();
        let fact = &equality(&mut run).fact;
        let (
            Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
        ) = (&fact.left, &fact.right)
        else {
            panic!()
        };
        assert!(
            crate::compile_to_lean::LitexToLeanCompiler::validate_finite_seq_signature(
                sequence, signature
            )
            .is_err()
        );
    }
}
#[test]
fn seqspace_rejects_a_different_output_set() {
    let (mut run, c) = super::execute(CLOSED);
    signature(&mut run).ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &c, "output");
}
#[test]
fn seqspace_needs_exactly_one_parameter_group_and_one_binder() {
    for change in ["group", "binder"] {
        let (mut run, c) = super::execute(CLOSED);
        let p = signature(&mut run);
        if change == "group" {
            p.set_bound_parameters
                .groups
                .push(p.set_bound_parameters.groups[0].clone());
        } else {
            let parameter = p.set_bound_parameters.groups[0].params[0].clone();
            p.set_bound_parameters.groups[0].params.push(parameter);
        }
        reject(&run, &c, change);
    }
}
#[test]
fn seqspace_positive_guard_keeps_original_binder_length_and_operator() {
    for change in ["binder", "length", "operator"] {
        let (mut run, c) = super::execute(POSITIVE);
        let p = signature(&mut run);
        let QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut p.dom_facts[0]
        else {
            panic!()
        };
        if change == "binder" {
            f.left = Obj::Literal(Literal::Number(Number::new("0".into())));
        } else if change == "length" {
            f.right = Obj::Literal(Literal::Number(Number::new("4".into())));
        } else {
            std::mem::swap(&mut f.left, &mut f.right);
        }
        reject(&run, &c, change);
    }
}
#[test]
fn seqspace_positive_guard_cannot_be_dropped_or_duplicated() {
    for drop in [false, true] {
        let (mut run, c) = super::execute(POSITIVE);
        let p = signature(&mut run);
        if drop {
            p.dom_facts.clear();
        } else {
            p.dom_facts.push(p.dom_facts[0].clone());
        }
        reject(&run, &c, "positive_guard_count");
    }
}
#[test]
fn seqspace_closed_form_keeps_original_one_based_endpoints() {
    for start in [false, true] {
        let (mut run, c) = super::execute(CLOSED);
        let Obj::SetFormer(SetFormer::ClosedRange(r)) =
            signature(&mut run).set_bound_parameters.groups[0]
                .param_type
                .as_mut()
        else {
            panic!()
        };
        if start {
            r.start = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        } else {
            r.end = Box::new(Obj::Literal(Literal::Number(Number::new("4".into()))));
        }
        reject(&run, &c, "closed_bounds");
    }
}
#[test]
fn seqspace_half_open_form_keeps_successor_endpoints() {
    let (mut run, c) = super::execute(HALF);
    let Obj::SetFormer(SetFormer::Range(r)) = signature(&mut run).set_bound_parameters.groups[0]
        .param_type
        .as_mut()
    else {
        panic!()
    };
    r.end = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
    reject(&run, &c, "half_open_stop");
}
#[test]
fn seqspace_empty_input_rule_keeps_literal_zero_length() {
    let (mut run, c) = super::execute(ZERO);
    let Obj::SetFormer(SetFormer::FiniteSeqSet(s)) = &mut equality(&mut run).fact.left else {
        panic!()
    };
    s.n = Box::new(Obj::Literal(Literal::Number(Number::new("1".into()))));
    reject(&run, &c, "zero_length");
}
#[test]
fn seqspace_empty_input_rule_keeps_actual_empty_carrier() {
    let (mut run, c) = super::execute(ZERO);
    signature(&mut run).set_bound_parameters.groups[0].param_type =
        Box::new(Obj::StandardSet(StandardSet::NPos));
    reject(&run, &c, "empty_carrier");
}
#[test]
fn seqspace_selected_empty_and_one_based_rules_cannot_be_swapped() {
    let (mut first, c) = super::execute(CLOSED);
    let (mut second, d) = super::execute(ZERO);
    std::mem::swap(
        &mut equality(&mut first).searched_proof,
        &mut equality(&mut second).searched_proof,
    );
    reject(&first, &c, "wrong_selected_empty_rule");
    reject(&second, &d, "wrong_selected_one_based_rule");
}
#[test]
fn seqspace_requires_both_original_endpoint_wd() {
    let (mut run, c) = super::execute(CLOSED);
    let p = equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut p.left, &mut p.right);
    reject(&run, &c, "endpoint_wd");
}
#[test]
fn seqspace_original_natural_requirement_cannot_be_replaced_by_integer_membership() {
    let (mut run, c) = super::execute(SYMBOLIC);
    let p = super::atomic_proof_mut(natural(&mut run));
    let AtomicFact::InFact(f) = &mut p.fact else {
        panic!()
    };
    f.set = Obj::StandardSet(StandardSet::Z);
    reject(&run, &c, "length_carrier");
}
#[test]
fn seqspace_original_natural_requirement_needs_exact_prior_citation() {
    for future in [false, true] {
        let (mut run, c) = super::execute(SYMBOLIC);
        let id = equality(&mut run).fact.fact_id;
        let p = super::atomic_proof_mut(natural(&mut run));
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut p.searched_proof
        else {
            panic!()
        };
        cite.cite_fact_id = if future { id } else { FactId::new(9_034_001) };
        reject(&run, &c, "length_citation");
    }
}
#[test]
fn seqspace_original_finite_sequence_constructor_needs_all_requirement_stages() {
    let (mut run, c) = super::execute(CLOSED);
    let p = equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(p)),
        ..
    } = p
    else {
        panic!()
    };
    p.requirement_fact_verified.pop();
    reject(&run, &c, "constructor_stages");
}
#[test]
fn seqspace_cannot_borrow_a_sibling_quantifiers_private_length_citation() {
    let first="forall private_n N:\n    finite_seq(R,private_n)=fn(private_k closed_range(1,private_n)) R\n";
    let (mut run, c) = super::execute(&format!("{first}\n{SYMBOLIC}"));
    super::compile_run(&run, &c, "separate_length_scopes").unwrap();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let first = super::equality_proof_mut(&mut first.proved_then_facts[0].verify_result);
    let p = first
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(p)),
        ..
    } = p
    else {
        panic!()
    };
    let p = super::atomic_proof_mut(&mut p.requirement_fact_verified[1]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &p.searched_proof else {
        panic!()
    };
    let foreign = cite.cite_fact_id;
    let p = super::atomic_proof_mut(natural(&mut run));
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut p.searched_proof
    else {
        panic!()
    };
    assert_ne!(foreign, cite.cite_fact_id);
    cite.cite_fact_id = foreign;
    reject(&run, &c, "sibling_length");
}
#[test]
fn seqspace_does_not_weaken_natural_length_or_one_based_domains() {
    for source in [
        "finite_seq(R,-1)=fn(k closed_range(1,-1)) R\n",
        "finite_seq(R,3)=fn(k closed_range(0,3)) R\n",
        "finite_seq(R,1)=fn(k {}) R\n",
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
                .unwrap();
        let mut rt =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!rt.run_litex_code(source).unwrap().success);
    }
}
