use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::prelude::*;

#[test]
fn disjunctive_set_formation_requires_every_original_ordered_branch() {
    for change in 0..2 {
        let (mut run, compiler) =
            super::execute("have EitherZeroOne set = {x R: x = 0 or x = 1}\n");
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let Some(DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(p)),
            ..
        }) = p.equal_to_well_defined[0]
            .as_detailed_success_mut()
            .unwrap()
        else {
            panic!()
        };
        let FactWellDefinedProof::OrFact(wd) = &mut p.assumed_facts[0].well_defined else {
            panic!()
        };
        let branches = &mut wd.as_detailed_mut().unwrap().branches;
        if change == 0 {
            branches.pop();
        } else {
            branches.reverse();
        }
        compiler
            .compile_run(&run, "changed_disjunctive_set")
            .expect_err("missing or reordered source WD cannot certify this predicate");
    }
}
