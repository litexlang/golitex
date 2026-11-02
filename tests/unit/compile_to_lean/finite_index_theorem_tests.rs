use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCE: &str =
    include_str!("../../../lean/examples/finite_set_bijective_index/statement.lit");
const CONCRETE: &str =
    include_str!("../../../lean/examples/finite_set_bijective_index_concrete/statement.lit");
#[test]
fn finite_index_replays_generic_empty_and_concrete_original_bt_calls() {
    for source in [SOURCE, CONCRETE] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "finite_index")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains("Litex.finiteSetBijectiveIndexWitness"));
        assert!(output.contains("variable [_functionSemantics : Litex.FunctionSemantics M]"));
        assert!(!output.contains("variable [_setSemantics"));
        assert_eq!(output, compiler.compile_run(&run, "finite_index").unwrap());
    }
}
#[test]
fn finite_index_keeps_original_finiteness_proof_store_wd_and_prior_scope() {
    for change in ["proof", "store", "wd", "argument", "future"] {
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
                    panic!("original finiteness citation")
                };
                cite.cite_fact_id = id;
            }
            _ => unreachable!(),
        }
        compiler.compile_run(&run, change).expect_err(
            "finite indexing needs the exact original finite-set proof and publication scope",
        );
    }
}
#[test]
fn finite_index_rejects_changed_binder_length_domain_carrier_and_bijection() {
    for change in [
        "unique",
        "seq_carrier",
        "length",
        "cardinality_subject",
        "start",
        "finish",
        "codomain",
        "function",
        "body_count",
        "capture",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::ExistFact(f) = &mut b.conclusions[0] else {
            panic!("plain existential")
        };
        let ParamType::Obj(Obj::SetFormer(SetFormer::FiniteSeqSet(seq))) =
            &mut f.typed_parameters.groups[0].param_type
        else {
            panic!("finite sequence witness domain")
        };
        match change {
            "seq_carrier" => seq.set = Box::new(Obj::StandardSet(StandardSet::R)),
            "length" => seq.n = Box::new(Obj::Literal(Literal::Number(Number::new("0".into())))),
            "cardinality_subject" => {
                let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = seq.n.as_mut() else {
                    panic!()
                };
                size.set = Box::new(Obj::StandardSet(StandardSet::R));
            }
            "capture" => {
                let Obj::Identifier(IdentifierObj::Plain { id, .. }) = seq.set.as_ref() else {
                    panic!("original outer argument")
                };
                f.typed_parameters.groups[0].params[0].id = *id;
            }
            "body_count" => f.facts.clear(),
            "unique" => b.conclusions[0] = Fact::ExistUniqueFact(f.clone()),
            _ => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::BijectiveFact(body)) =
                    &mut f.facts[0]
                else {
                    panic!("original bijection")
                };
                if change == "codomain" {
                    body.codomain = Obj::StandardSet(StandardSet::R)
                } else if change == "function" {
                    body.function = Obj::Literal(Literal::Number(Number::new("7".into())))
                } else {
                    let Obj::SetFormer(SetFormer::ClosedRange(range)) = &mut body.domain else {
                        panic!()
                    };
                    let bad = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
                    if change == "start" {
                        range.start = bad
                    } else {
                        range.end = bad
                    }
                }
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "the original one-based cardinality-length complete bijection schema must be unchanged",
        );
    }
}
