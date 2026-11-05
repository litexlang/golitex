use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const NATURAL: &str = r#"thm checked_natural_upper_bound:
    ? forall x R:
        exist n N+ st {x<n}
    release thm real_archimedean_natural_upper_bound(x)
"#;
const RATIONAL: &str = r#"thm checked_rational_density:
    ? forall a,b R:
        a<b
        =>:
            exist q Q st {a<q and q<b}
    release thm rational_between_reals(a,b)
"#;

pub(super) fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
        panic!("forall body");
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(call),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original builtin invocation");
    };
    call
}

#[test]
fn dense_order_requires_original_ordered_premises_and_stores() {
    for source in [NATURAL, RATIONAL] {
        for change in [
            "proof",
            "store",
            "conclusion_wd",
            "requirement_subject",
            "future_citation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "conclusion_wd" => {
                    call.conclusions_wd.clear();
                }
                "requirement_subject" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut call.builtin.as_mut().unwrap().requirements[0]
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
                "future_citation" => {
                    let id = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
                    let child = super::atomic_proof_mut(&mut call.dom_proofs[0]);
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut child.searched_proof
                    else {
                        panic!("real premise citation")
                    };
                    cite.cite_fact_id = id;
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, change)
                .expect_err("retain original preceding checked premises");
        }
    }
    let (mut run, compiler) = super::execute(RATIONAL);
    invocation(&mut run).dom_proofs.swap(0, 1);
    compiler
        .compile_run(&run, "reordered")
        .expect_err("ordered domain proofs");
}

#[test]
fn dense_order_rejects_changed_witness_carrier_identity_bounds_and_arity() {
    for source in [NATURAL, RATIONAL] {
        for change in [
            "carrier",
            "binder",
            "bound",
            "body_count",
            "witness_count",
            "arguments",
        ] {
            let (mut run, compiler) = super::execute(source);
            let builtin = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "arguments" {
                builtin.arguments.pop();
            } else {
                let Fact::ExistFact(exists) = &mut builtin.conclusions[0] else {
                    panic!()
                };
                match change {
                    "carrier" => {
                        exists.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::C))
                    }
                    "binder" => {
                        exists.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX)
                    }
                    "bound" => {
                        let atom = match &mut exists.facts[0] {
                            QuantifierFreeFact::AtomicFact(atom) => atom,
                            QuantifierFreeFact::AndFact(bounds) => &mut bounds.facts[0],
                            _ => panic!("native ordered bounds"),
                        };
                        let AtomicFact::LessFact(f) = atom else {
                            panic!("strict bound");
                        };
                        f.right = builtin.arguments[0].clone();
                    }
                    "body_count" => {
                        exists.facts.pop();
                    }
                    "witness_count" => {
                        exists.typed_parameters.groups[0].params.clear();
                    }
                    _ => unreachable!(),
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("the exact selected existential contract is mandatory");
        }
    }
}
