use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{
    ExecDefTemplateStmtResult, ExecWitnessExistFactStmtResult, ExecWitnessStmtResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Choose a nonempty set through a template, then choose one of its members.
template<S set>:
    have chosen_nonempty nonempty_set

$is_nonempty_set(\chosen_nonempty<R>)

have a \chosen_nonempty<R>

a $in \chosen_nonempty<R>
"#,
    r#"# A finite-set template supplies the WD of cardinality inside a captured formula.
template<S set>:
    have chosen_finite finite_set

$is_finite_set(\chosen_finite<R>)

finite_set_size(\chosen_finite<R>) $in N

have fn chosen_size(t R) N = finite_set_size(\chosen_finite<{t}>)

chosen_size(2) = finite_set_size(\chosen_finite<{2}>)
"#,
    r#"# Introduce an arbitrary nonempty set and its member, and an arbitrary finite set.
have A nonempty_set, x A

x $in A

$is_set(A)

have F finite_set

finite_set_size(F) $in N
"#,
    r#"# Preserve nonempty and finite predicates for aliases and parameterized copies.
have NonemptyAlias nonempty_set = R

$is_nonempty_set(NonemptyAlias)

have FiniteAlias finite_set = {1, 2}

$is_finite_set(FiniteAlias)

FiniteAlias = {1, 2}

template<T finite_set>:
    have copied_finite finite_set = T

\copied_finite<{1, 2}> = {1, 2}

template<T nonempty_set>:
    have copied_nonempty nonempty_set = T

\copied_nonempty<R> = R
"#,
    r#"# Construct a finite set and an inhabited set with a member inside named proofs.
thm finite_kind_witness:
    ? exist finite_witness finite_set st {$is_finite_set(finite_witness)}
    have local_finite finite_set
    witness exist finite_witness finite_set st {$is_finite_set(finite_witness)} from local_finite

thm nonempty_kind_witness:
    ? exist nonempty_witness nonempty_set, chosen_member nonempty_witness st {chosen_member $in nonempty_witness}
    have local_nonempty nonempty_set, local_member local_nonempty
    witness exist nonempty_witness nonempty_set, chosen_member nonempty_witness st {chosen_member $in nonempty_witness} from local_nonempty, local_member
"#,
];

fn have(statement: &mut ExecStmtResult) -> &mut ExecHaveObjInNonemptySetStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult::Success(
            p,
        )),
    )) = statement
    else {
        panic!("ordinary have")
    };
    p
}

fn template_have(run: &mut RunLitexCodeResult) -> &mut ExecHaveObjInNonemptySetStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    have(p.body.as_mut())
}

#[test]
fn set_kind_have_requires_exact_kind_stages_and_parameter_stores() {
    for source in &SOURCES[..2] {
        for mutation in 0..5 {
            let (mut run, compiler) = super::execute(source);
            let p = template_have(&mut run);
            match mutation {
                0 => p.groups[0].param_type_well_defined = ParamTypeWellDefinedProof::Set,
                1 => p.groups[0].nonempty_check = ParamTypeFactCheckResult::Set,
                2 => p.groups[0].defined_params.stored_fact_ids.clear(),
                3 => p.groups[0].defined_params.store_and_infer_results.clear(),
                4 => p.groups.clear(),
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "bad_kind")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn set_kind_aliases_require_original_rhs_formation_checks_and_stores() {
    for index in [0, 2] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(SOURCES[3]);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
            )) = &mut run.statement_results[index]
            else {
                panic!()
            };
            match mutation {
                0 => p.type_preflight.param_type_well_defined[0] = ParamTypeWellDefinedProof::Set,
                1 => p.membership_checks.clear(),
                2 => p.equal_to_well_defined.clear(),
                3 => p.store_and_infer_result.store_and_infer_results.swap(0, 1),
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "bad_alias")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn set_kind_existential_formation_requires_its_own_kind_and_stores() {
    for source in [
        "witness exist finite_witness finite_set st {$is_finite_set(finite_witness)} from {}",
        "witness exist nonempty_witness nonempty_set st {$is_nonempty_set(nonempty_witness)} from R",
    ] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(source);
            compiler.compile_run(&run, "baseline").unwrap();
            let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
                ExecWitnessExistFactStmtResult::Success(p))) = &mut run.statement_results[0] else { panic!() };
            let FactWellDefinedProof::ExistFact(p) = &mut p.ambient.exist_fact_well_defined else { panic!() };
            let p = p.as_detailed_mut().unwrap();
            match mutation {
                0 => p.introduced_params.param_type_well_defined[0] = ParamTypeWellDefinedProof::Set,
                1 => p.introduced_params.defined_params.stored_fact_ids.clear(),
                2 => p.assumed_body_facts.clear(),
                _ => unreachable!(),
            }
            compiler.compile_run(&run, "bad_existential").expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn set_kind_context_preserves_properties_and_generic_host_parameters() {
    let (mut run, compiler) = super::execute(SOURCES[2]);
    let (id, fact) = {
        let p = have(&mut run.statement_results[0]);
        (
            p.statement.param_def.groups[0].params[0].id,
            p.groups[0].defined_params.store_and_infer_results[0].primary_fact_id(),
        )
    };
    let position = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    let header = compiler.context_header(&position).unwrap();
    assert!(header.contains(&format!(
        "h_{} : Litex.IsNonempty _value_i{}",
        fact.value(),
        id.value()
    )));
    assert!(header.contains(&format!("_Host_i{} : Type", id.value())));
    assert!(header.contains("Litex.IsFiniteSet"));
    let before = SourcePosition {
        before: 0,
        ..position
    };
    let after = SourcePosition {
        before: 1,
        ..position
    };
    assert!(before.visible_fact(fact, &compiler.runtime).is_err());
    assert!(after.visible_fact(fact, &compiler.runtime).is_ok());
}

#[test]
fn local_set_kind_witness_does_not_export_its_parameter_fact() {
    let (mut run, compiler) = super::execute(SOURCES[4]);
    let p = super::named_theorem_mut(&mut run.statement_results[0]);
    let ExecDefThmBodyProof::NonForall(body) = &mut p.body else {
        panic!()
    };
    let id = have(&mut body.proof_steps[0]).groups[0]
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let outer = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(outer.visible_fact(id, &compiler.runtime).is_err());
}
