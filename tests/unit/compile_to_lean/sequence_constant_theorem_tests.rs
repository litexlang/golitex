use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;
const GENERIC: &str =
    include_str!("../../../lean/examples/constant_sequence_limit_theorem/statement.lit");
const SELECTED: &str =
    include_str!("../../../lean/examples/constant_sequence_limit_selected/statement.lit");
#[test]
fn sequence_constant_replays_the_original_constant_equation_for_generic_and_anonymous_sequences() {
    for source in [GENERIC, SELECTED] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "constant").unwrap();
        assert!(output.contains("Litex.sequenceLimitConstant"));
        assert_eq!(output, compiler.compile_run(&run, "constant").unwrap());
    }
    let (mut run, _) = super::execute(GENERIC);
    assert_eq!(
        invocation(&mut run).builtin.as_ref().unwrap().theorem,
        BuiltinTheoremId::SequenceLimitConstant
    );
}
#[test]
fn sequence_constant_preserves_all_three_premise_ids_stores_and_conclusion_wd() {
    for change in [
        "args",
        "proof",
        "proof_order",
        "store",
        "store_order",
        "wd",
        "conclusion",
        "types",
    ] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run);
        match change {
            "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "proof" => p.dom_proofs.pop().map(|_| ()).unwrap(),
            "proof_order" => p.dom_proofs.swap(0, 1),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 1),
            "wd" => p.conclusions_wd.clear(),
            "conclusion" => p.builtin.as_mut().unwrap().conclusions.clear(),
            _ => std::mem::swap(&mut p.type_proofs, &mut p.dom_proofs),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("original sequence,real value,universal stages must match");
    }
}
#[test]
fn sequence_constant_keeps_positive_indices_unguarded_equations_and_the_original_limit() {
    for change in [
        "value_domain",
        "sequence_domain",
        "index_domain",
        "guard",
        "clause",
        "orientation",
        "conclusion",
    ] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        match change {
            "value_domain" | "sequence_domain" => {
                let index = usize::from(change == "value_domain");
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[index] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::RPos);
            }
            "conclusion" => {
                let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) = &mut p.conclusions[0]
                else {
                    panic!()
                };
                f.value = super::number_object("0");
            }
            _ => {
                let guard = p.requirements[1].clone();
                let Fact::ForallFact(f) = &mut p.requirements[2] else {
                    panic!()
                };
                match change {
                    "index_domain" => {
                        f.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::N))
                    }
                    "guard" => {
                        let Fact::AtomicFact(guard) = guard else {
                            panic!()
                        };
                        f.dom_facts.push(Fact::AtomicFact(guard));
                    }
                    "clause" => f.then_facts.clear(),
                    "orientation" => {
                        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                            &mut f.then_facts[0]
                        else {
                            panic!()
                        };
                        std::mem::swap(&mut eq.left, &mut eq.right);
                    }
                    _ => panic!(),
                }
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("constant limit uses the exact positive-index pointwise equation");
    }
}
#[test]
fn sequence_constant_cannot_use_its_future_limit_as_its_original_real_value_premise() {
    let (mut run, compiler) = super::execute(GENERIC);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[1]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("no forward citation can manufacture a real value premise");
}
