use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

const GENERIC: &str =
    include_str!("../../../lean/examples/inner_product_positive_theorem/statement.lit");
const SELECTED: &str =
    include_str!("../../../lean/examples/inner_product_positive_selected/statement.lit");
const EMPTY: &str =
    include_str!("../../../lean/examples/inner_product_positive_empty/statement.lit");

#[test]
fn inner_positive_replays_real_membership_both_projections_and_empty_dimension() {
    for source in [GENERIC, SELECTED, EMPTY] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "inner_positive").unwrap();
        assert!(output.contains("Litex.finiteInnerProductSelfPositive"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "inner_positive").unwrap()
        );
    }
    let (mut run, _) = super::execute(GENERIC);
    assert_eq!(
        invocation(&mut run).builtin.as_ref().unwrap().theorem,
        BuiltinTheoremId::InnerProductPositive
    );
}

#[test]
fn inner_positive_requires_original_dimension_vector_proofs_stores_and_all_three_wds() {
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
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(0, 1),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 1),
            "wd" => {
                p.conclusions_wd.pop();
            }
            "conclusion" => {
                p.builtin.as_mut().unwrap().conclusions.pop();
            }
            _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("preserve the complete original heterogeneous builtin pipeline");
    }
}

#[test]
fn inner_positive_keeps_self_inner_vector_dimension_and_complex_carrier() {
    for change in ["dimension", "vector", "self", "carrier"] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if change == "carrier" {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[1] else {
                panic!()
            };
            let Obj::SetFormer(SetFormer::FiniteSeqSet(s)) = &mut f.set else {
                panic!()
            };
            s.set = Box::new(Obj::StandardSet(StandardSet::R));
        } else {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.conclusions[0] else {
                panic!()
            };
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = &mut f.element else {
                panic!()
            };
            let other = Box::new(Obj::StandardSet(StandardSet::R));
            match change {
                "dimension" => inner.dimension = other,
                "vector" => inner.left = other,
                _ => inner.right = other,
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("self positivity cannot certify another inner product or vector carrier");
    }
}

#[test]
fn inner_positive_retains_real_imaginary_projections_zero_and_original_constructor_wd() {
    for change in ["real", "imaginary", "zero", "wd"] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run);
        if change == "wd" {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            wd.as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .clear();
        } else if change == "real" {
            let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[1]
            else {
                panic!()
            };
            f.right = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[2]
            else {
                panic!()
            };
            if change == "imaginary" {
                f.left = Obj::StandardSet(StandardSet::R);
            } else {
                f.right = super::number_object("1");
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("each original projection, endpoint and formation must match");
    }
}

#[test]
fn inner_positive_cannot_cite_its_future_real_conclusion_as_an_original_dimension_premise() {
    let (mut run, compiler) = super::execute(GENERIC);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("dimension membership precedes the self-inner conclusions");
}
