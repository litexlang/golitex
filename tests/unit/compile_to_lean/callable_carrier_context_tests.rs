use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionSetMembershipStrategySingleStep;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{InFactSearchProofByBuiltinRule, PositiveIntegerInNPosBuiltinRuleProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSetStatObjWellDefinedProofByDef;

const WIDEN: &str = include_str!("../../../lean/examples/sequence_carrier_widening/statement.lit");
const POSITIVE: &str =
    include_str!("../../../lean/examples/positive_integer_refinement/statement.lit");
const EXTREMA: &str =
    include_str!("../../../lean/examples/finite_extrema_carrier_alias/statement.lit");

fn sequence_strategy(run: &mut RunLitexCodeResult) -> &mut FunctionSetMembershipStrategySingleStep {
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSetMembership(p),
    ) = &mut atom.searched_proof
    else {
        panic!("selected function-set membership")
    };
    p
}

fn positive_integer(run: &mut RunLitexCodeResult) -> &mut PositiveIntegerInNPosBuiltinRuleProof {
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::PositiveIntegerInNPos(p),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("selected positive integer introduction")
    };
    p
}

fn nonempty_rewrite(
    run: &mut RunLitexCodeResult,
) -> &mut AtomicExceptEqualityFactSearchProofByBuiltinRewrite {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut run.statement_results[1]
    else {
        panic!("maximum alias declaration")
    };
    let VerifyObjWellDefinedResult::Success(wd) = &mut p.value_well_defined else {
        panic!("constructor WD")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FiniteSetStat(
                FiniteSetStatObjWellDefinedProofByDef::FiniteSetMax(p),
            ),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("maximum WD")
    };
    let atom = super::atomic_proof_mut(&mut p.requirement_fact_verified[1]);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(p) = &mut atom.searched_proof
    else {
        panic!("recorded nonempty alias rewrite")
    };
    p
}

#[test]
fn callable_carriers_replay_original_numeric_and_set_wd() {
    for source in [
        WIDEN,
        POSITIVE,
        EXTREMA,
        include_str!("../../../lean/examples/constant_sequence_carrier_alias/statement.lit"),
        include_str!("../../../lean/examples/constant_sequence_generic_carrier/statement.lit"),
        include_str!("../../../lean/examples/positive_integer_sequence_index/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "callable_carriers").unwrap();
        assert_eq!(
            lean,
            compiler.compile_run(&run, "callable_carriers").unwrap()
        );
    }
}

#[test]
fn sequence_membership_retains_index_domain_codomain_and_pointwise_return() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(WIDEN);
        compiler.compile_run(&run, "original_sequence").unwrap();
        let p = sequence_strategy(&mut run);
        match mutation {
            0 => {
                p.domain.target.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            1 => p.domain.target.ret_set = Box::new(Obj::StandardSet(StandardSet::Z)),
            2 => p.proof_of_requirement_facts.clear(),
            3 => p.requirement_facts.clear(),
            _ => unreachable!(),
        }
        compiler.compile_run(&run, "changed_sequence").expect_err(
            "the complete original sequence signature and pointwise proof are required",
        );
    }
}

#[test]
fn positive_integer_introduction_retains_both_exact_original_premises() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(POSITIVE);
        compiler.compile_run(&run, "original_positive").unwrap();
        let p = positive_integer(&mut run);
        match mutation {
            0 | 1 => {
                let atom = super::atomic_proof_mut(&mut p.integer_proof);
                let AtomicFact::InFact(f) = &mut atom.fact else {
                    panic!("integer fact")
                };
                if mutation == 0 {
                    f.set = Obj::StandardSet(StandardSet::R);
                } else {
                    f.element = super::number_object("1");
                }
            }
            2 => {
                let atom = super::atomic_proof_mut(&mut p.positive_proof);
                let AtomicFact::GreaterFact(f) = &mut atom.fact else {
                    panic!("strict positivity")
                };
                f.right = super::number_object("1");
            }
            3 => std::mem::swap(&mut p.integer_proof, &mut p.positive_proof),
            4 => {
                let atom = super::atomic_proof_mut(&mut p.positive_proof);
                let AtomicFact::GreaterFact(f) = &atom.fact else {
                    panic!("strict positivity")
                };
                atom.fact = AtomicFact::GreaterEqualFact(GreaterEqualFact {
                    fact_id: f.fact_id,
                    left: f.left.clone(),
                    right: f.right.clone(),
                    line_file: f.line_file.clone(),
                });
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_positive")
            .expect_err("integer membership and strict positivity of the same object are required");
    }
}

#[test]
fn nonempty_alias_rewrite_retains_its_citations_and_residual() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(EXTREMA);
        compiler.compile_run(&run, "original_extrema").unwrap();
        let rewrite = nonempty_rewrite(&mut run);
        if mutation < 3 {
            let ids = super::atomic_rewrite_cites_mut(rewrite);
            match mutation {
                0 => ids.clear(),
                1 => ids[0] = FactId::new(u64::MAX),
                _ => ids.push(ids[0]),
            }
        } else {
            let AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(p) =
                rewrite
            else {
                panic!("known carrier substitution")
            };
            let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) = &mut p.rewritten_fact else {
                panic!("nonempty residual")
            };
            f.set = Obj::StandardSet(StandardSet::R);
        }
        compiler
            .compile_run(&run, "changed_nonempty")
            .expect_err("exact ordered equality citations and original residual must remain");
    }
}

#[test]
fn nonempty_alias_transport_preserves_negation() {
    let (mut run, compiler) = super::execute(
        "have empty_family_alias set = {}\nnot $is_nonempty_set(empty_family_alias)\n",
    );
    super::atomic_rewrite_mut(&mut run.statement_results[1]);
    let lean = compiler.compile_run(&run, "empty_alias").unwrap();
    assert!(lean.contains("_known_citation"));
    assert_eq!(lean, compiler.compile_run(&run, "empty_alias").unwrap());
}

#[test]
fn callable_carriers_do_not_erase_positive_index_or_nonempty_requirements() {
    for source in [
        "forall a seq(R):\n    a(0) $in R\n",
        "forall z Z:\n    z >= 0\n    =>:\n        z $in N+\n",
        "have empty_family set = {}\nlet invalid_intersection = family_intersect(empty_family)\n",
    ] {
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_carrier")
            .expect_err("original WD must hold");
    }
}
