use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const SOURCE: &str = r#"# Invoke the explicit epsilon-definition theorem for a at real function limit.
thm explicit_at_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < abs(x-x0) and abs(x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_at(f,x0,L)
    by thm fn_limit_at_from_epsilon(f,x0,L) => $has_limit_at(f,x0,L)
"#;

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
        &mut p.proof_steps[0]
    else {
        panic!("explicit epsilon theorem")
    };
    p
}

#[test]
fn function_limit_from_epsilon_rejects_missing_or_reordered_clause_proofs() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = invocation(&mut run);
        if missing {
            p.dom_proofs.pop();
        } else {
            p.dom_proofs.swap(5, 6);
        }
        compiler
            .compile_run(&run, "bad_epsilon_proofs")
            .expect_err("both ordered source clauses required");
    }
}

#[test]
fn function_limit_from_epsilon_rejects_wrong_accumulation_and_preimage() {
    for accumulation in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if accumulation {
            let Fact::ForallFact(f) = &mut p.requirements[5] else {
                panic!("radius")
            };
            f.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        } else {
            let Fact::ForallFact(f) = &mut p.requirements[6] else {
                panic!("epsilon")
            };
            let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
                panic!("delta")
            };
            let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s)) = &mut e.facts[0] else {
                panic!("control")
            };
            let Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) = &mut s.right else {
                panic!("preimage")
            };
            p.function = Box::new(Obj::StandardSet(StandardSet::R));
        }
        compiler
            .compile_run(&run, "changed_epsilon_subject")
            .expect_err("the exact domain, direction and function are required");
    }
}
