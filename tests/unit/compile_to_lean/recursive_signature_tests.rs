use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult};
use crate::prelude::*;

const BOUNDED: &str = r#"# Tracer: recursive lower bounds cannot descend with the arguments.
# Before (incorrectly accepted in strict mode):
# have fn empty_value(n Z) {} by induc n from n - 1:
#     case n = n: empty_value(n - 1)
# empty_value(0) $in {}
# Now the declaration fails: (n - 1) - 1 >= n - 1 is not provable.
# Executable negative regression: induction_lower_bound_cannot_descend_with_recursive_arguments.
#
# Now: a parameter-dependent lower bound preserved by recursion is accepted.
have fn bounded(n, b Z: n >= b) Z by induc n from b:
    case n - 1 < b: 0
    case n - 1 >= b: bounded(n - 1, b)

bounded(1, 0) = bounded(0, 0) = 0

# Boundary: recursive calls must decrease the integer measure, stay in-domain,
# and preserve or increase the lower bound. Arbitrary descending bounds fail.
# Evidence: target/release/litex -lang en -strict -f examples/stmt_nodes/definition/induction_lower_bound.lit
# Tests: cargo test --release --lib induction_lower_bound
"#;
const FIB: &str = "have fn fib(n Z: n >= 0) R by induc n from 0:\n    case n < 2: 1\n    case n >= 2: fib(n - 2) + fib(n - 1)\n";
const INCREASING: &str = "have fn increasing(n, b Z: n >= b) Z by induc n from b:\n    case n - 1 < b: 0\n    case n - 1 >= b:\n        case n - 1 < b + 1: 0\n        case n - 1 >= b + 1: increasing(n - 1, b + 1)\n";

#[test]
fn integer_recursive_declarations_emit_the_original_graph_and_equations() {
    for source in [BOUNDED, FIB] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "integer_recursion")
            .expect(source);
        assert!(lean.contains("Litex.recursiveFn _data"));
        assert!(lean.contains("Litex.recursiveFn_equation"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "integer_recursion").unwrap()
        );
    }
}

#[test]
fn integer_recursive_declarations_reject_changed_formation_and_case_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(BOUNDED);
        let p = recursive(&mut run);
        match mutation {
            0 => p.case_checks.cases.swap(0, 1),
            1 => p.case_checks.disjoint[0].j = 0,
            2 => p.store_and_infer_result.case_defining_fact_ids.reverse(),
            3 => p.statement.measure = super::number_object("0"),
            4 => {
                let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } =
                    &mut p.case_checks.cases[1].body
                else {
                    panic!()
                };
                let Some(DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                    ..
                }) = well_defined.as_detailed_success_mut().unwrap()
                else {
                    panic!()
                };
                call.requirement_fact_verified.pop();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_recursion")
            .expect_err("changed source evidence");
    }
}

#[test]
fn recursive_decrement_requires_the_original_positive_closed_certificate() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
        AtomicExceptEqualityFactSearchProofByBuiltinRule as Rule,
        less::LessFactSearchProofByBuiltinRule as LessRule,
    };
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute("forall x R:\n    x - 2 < x\n");
        compiler.compile_run(&run, "positive_decrement").unwrap();
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(Rule::LessFact(
            LessRule::SubtractPositiveClosedLess(proof),
        )) = &mut atomic.searched_proof
        else {
            panic!("selected positive closed decrement")
        };
        match mutation {
            0 => proof.normalized_subtrahend = "3".into(),
            1 => proof.subtrahend = super::number_object("0"),
            2 => proof.minuend = super::number_object("2"),
            _ => unreachable!(),
        }
        assert_eq!(
            compiler
                .compile_run(&run, "changed_decrement")
                .unwrap_err()
                .route,
            "SubtractPositiveClosedLess/Certificate"
        );
    }
}

fn recursive(run: &mut RunLitexCodeResult) -> &mut ExecHaveFnByInducStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(proof),
    )) = &mut run.statement_results[0]
    else {
        panic!("recursive declaration")
    };
    proof
}

#[test]
fn recursive_signature_retains_integer_measure_and_all_domain_guards() {
    for (source, guards, arity) in [(BOUNDED, 4, 2), (FIB, 3, 1), (INCREASING, 4, 2)] {
        let (mut run, compiler) = super::execute(source);
        let proof = recursive(&mut run);
        let position = SourcePosition::new(None, SourceOwner::RecursiveFunction(proof), 7);
        let signature = compiler
            .recursive_restricted_signature(proof, &position)
            .unwrap();
        assert_eq!(signature.dom_facts.len(), guards);
        assert_eq!(
            signature
                .set_bound_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum::<usize>(),
            arity
        );
        let object = Obj::FunctionSpace(FunctionSpace::FnSet(signature));
        assert!(compiler
            .compile_recursive_signature_reference(&object, &position)
            .unwrap()
            .is_some());
    }
}

#[test]
fn recursive_signature_rejects_mismatched_header_and_stored_self() {
    for mutation in 0..9 {
        let (mut run, compiler) = super::execute(BOUNDED);
        let proof = recursive(&mut run);
        match mutation {
            0 => proof.statement.lower_bound = super::number_object("0"),
            1 => proof.statement.measure = proof.statement.lower_bound.clone(),
            2 => proof.statement.fn_set_clause.dom_facts.clear(),
            3 => proof.statement.fn_set_clause.ret_set = Obj::StandardSet(StandardSet::R),
            4 => {
                proof.statement.fn_set_clause.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            5 => {
                proof.statement.fn_set_clause.set_bound_parameters.groups[0]
                    .params
                    .pop();
            }
            6 => proof.statement.fn_set_clause.set_bound_parameters.groups[0]
                .params
                .swap(0, 1),
            7 => proof.statement.name.id = IdentifierId::new(u64::MAX),
            8 => {
                let StoreFactResult::AtomicFact(stored) =
                    &mut proof.restricted_self_membership.store
                else {
                    panic!("self membership")
                };
                let AtomicFact::InFact(member) = &mut stored.fact else {
                    panic!()
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut member.set else {
                    panic!()
                };
                signature.dom_facts.pop();
            }
            _ => unreachable!(),
        }
        let position = SourcePosition::new(None, SourceOwner::RecursiveFunction(proof), 7);
        compiler
            .recursive_restricted_signature(proof, &position)
            .expect_err(&format!("altered evidence {mutation}"));
    }
}

#[test]
fn recursive_self_signature_is_visible_only_after_its_original_store() {
    let (mut run, compiler) = super::execute(BOUNDED);
    let proof = recursive(&mut run);
    let before = SourcePosition::new(None, SourceOwner::RecursiveFunction(proof), 6);
    let after = SourcePosition {
        before: 7,
        ..before
    };
    let signature = compiler
        .recursive_restricted_signature(proof, &after)
        .unwrap();
    let object = Obj::FunctionSpace(FunctionSpace::FnSet(signature));
    assert!(compiler
        .compile_recursive_signature_reference(&object, &before)
        .unwrap()
        .is_none());
    assert!(compiler
        .compile_recursive_signature_reference(&object, &after)
        .unwrap()
        .is_some());
}

const NATURAL_NESTED: &str = "have fn natural_nested(n N) N by induc n from 0:\n    case n = 0: 0\n    case n > 0:\n        case n < 2: 1\n        case n >= 2: natural_nested(n - 1) + 1\n";

const NESTED_COUNT: &str = "have fn nested_count(n Z: n >= 0) Z by induc n from 0:\n    case n < 1: 0\n    case n >= 1:\n        case n < 2: 1\n        case n >= 2:\n            case n < 3: 2\n            case n >= 3: nested_count(n - 1) + 1\n";

#[test]
fn nested_recursive_cases_emit_original_leaf_equations_and_selected_paths() {
    for source in [
        format!("{INCREASING}\nincreasing(4, 0) = increasing(3, 1) = increasing(2, 2) = 0\n"),
        format!("{NATURAL_NESTED}\nnatural_nested(1) = 1\nnatural_nested(2) = natural_nested(1) + 1 = 2\n"),
        format!("{NESTED_COUNT}\nnested_count(2) = 2\nnested_count(3) = nested_count(2) + 1 = 3\nnested_count(4) = nested_count(3) + 1 = 4\n"),
    ] {
        let (run, compiler) = super::execute(&source);
        let generated = compiler.compile_run(&run, "nested_recursion").expect(&source);
        assert!(generated.contains("Litex.recursiveFn_equation"));
        assert_eq!(generated, compiler.compile_run(&run,"nested_recursion").unwrap());
    }
}

#[test]
fn nested_recursive_cases_reject_changed_child_evidence_and_leaf_stores() {
    use crate::execute::InducCaseBodySuccess;
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(INCREASING);
        let p = recursive(&mut run);
        let InducCaseBodySuccess::NestedCases(nested) = &mut p.case_checks.cases[1].body else {
            panic!()
        };
        match mutation {
            0 => nested.cases.swap(0, 1),
            1 => nested.disjoint[0].i = 1,
            2 => nested.disjoint.clear(),
            3 => {
                let (mut donor, _) = super::execute(INCREASING);
                std::mem::swap(
                    &mut nested.coverage,
                    &mut recursive(&mut donor).case_checks.coverage,
                );
            }
            4 => p.store_and_infer_result.case_defining_fact_ids.swap(1, 2),
            5 => {
                let InducCaseBodySuccess::EqualTo { well_defined, .. } = &mut nested.cases[1].body
                else {
                    panic!()
                };
                let Some(DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                    ..
                }) = well_defined.as_detailed_success_mut().unwrap()
                else {
                    panic!()
                };
                call.requirement_fact_verified.pop();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_nested_recursion")
            .expect_err("changed source evidence");
    }
}

#[test]
fn nested_recursive_unfold_requires_every_selected_guard_in_original_order() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition,
    };
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(&format!(
            "{INCREASING}\nincreasing(4, 0) = increasing(3, 1)\n"
        ));
        compiler.compile_run(&run, "nested_unfold").unwrap();
        let fact = super::fact_statement_mut(&mut run.statement_results[1]);
        let equal = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::HaveFnByInduc(proof),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("selected recursive unfolding")
        };
        assert_eq!(proof.selected_case_path.len(), 2);
        match mutation {
            0 => {
                proof.selected_case_path.pop();
            }
            1 => proof.selected_case_path.swap(0, 1),
            2 => proof.selected_case_path[1].case_index = 0,
            3 => proof.expanded_body = super::number_object("42"),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_nested_unfold")
            .expect_err("changed selected path");
    }
}

#[test]
fn nested_recursive_coverage_wd_stays_inside_its_original_parent_branch() {
    use crate::ast::stmt::HaveFnByInducCaseBody;
    let (mut run, compiler) = super::execute(INCREASING);
    let p = recursive(&mut run);
    let HaveFnByInducCaseBody::NestedCases(cases) = &p.statement.cases[1].body else {
        panic!()
    };
    let AndChainAtomicFact::AtomicFact(AtomicFact::LessFact(guard)) = &cases[0].case_fact else {
        panic!()
    };
    let object = &guard.right;
    let root = SourcePosition::new(None, SourceOwner::RecursiveFunction(p), 8);
    let before = SourcePosition::new(
        Some(&root),
        SourceOwner::RecursiveCase(&p.case_checks.cases[1]),
        1,
    );
    let after = SourcePosition {
        before: 2,
        ..before
    };
    let sibling = SourcePosition::new(
        Some(&root),
        SourceOwner::RecursiveCase(&p.case_checks.cases[0]),
        usize::MAX,
    );
    for (site, expected) in [
        (&root, false),
        (&before, false),
        (&sibling, false),
        (&after, true),
    ] {
        let found = site
            .with_visible_wd(object, &mut |wd, site| compiler.compile_wd(wd, site))
            .unwrap();
        assert_eq!(found.is_some(), expected);
    }
}
const TEMPLATE_NESTED: &str = r#"# Count from a captured real seed using nested recursive cases.
template<start R>:
    have fn seeded_count(n Z: n >= 0) R by induc n from 0:
        case n < 1: start
        case n >= 1:
            case n < 2: start + 1
            case n >= 2: seeded_count(n - 1) + 1

\seeded_count<3>(1) = 4

\seeded_count<3>(2) = \seeded_count<3>(1) + 1 = 5
"#;

fn recursive_template(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::ExecDefTemplateStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        crate::execute::ExecDefTemplateStmtResult::Success(proof),
    )) = &mut run.statement_results[0]
    else {
        panic!("recursive template")
    };
    proof
}

#[test]
fn recursive_template_publications_reject_changed_captures_and_equation_sources() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(TEMPLATE_NESTED);
        let p = recursive_template(&mut run);
        match mutation {
            0 => p.definition_facts.pop().map(|_| ()).unwrap(),
            1 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            2 => {
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                    ExecHaveFnByInducStmtResult::Success(body),
                )) = p.body.as_mut()
                else {
                    panic!()
                };
                body.store_and_infer_result.case_defining_fact_ids.reverse();
            }
            3 => {
                let StoreFactResult::ForallFact(stored) =
                    &mut p.definition_facts[1].store_and_infer.store
                else {
                    panic!()
                };
                stored.fact.typed_parameters.groups.clear();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_template_publication")
            .expect_err("changed original template evidence");
    }
}

#[test]
fn recursive_template_unfold_requires_the_complete_original_selected_path() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_template::result::EqualitySearchProofByTemplateObjectDefinition,
    };
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(TEMPLATE_NESTED);
        let fact = super::fact_statement_mut(&mut run.statement_results[1]);
        let equality = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(p),
            ),
        ) = &mut equality.searched_proof
        else {
            panic!("selected recursive template unfolding")
        };
        assert_eq!(p.selected_case_path.len(), 2);
        match mutation {
            0 => {
                p.selected_case_path.pop();
            }
            1 => p.selected_case_path[1].case_index = usize::MAX,
            2 => p.selected_case_path.reverse(),
            3 => p.expanded_body = super::number_object("99"),
            4 => {
                super::equality_proof_mut(&mut p.residual_equal).fact.right =
                    super::number_object("99")
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_template_path")
            .expect_err("changed original selected path");
    }
}

const TEMPLATE_SET_SEED: &str = r#"# Repeat an arbitrary set member using integer recursion and reuse the published equations.
template<A set, seed A>:
    have fn seeded_generic(n Z: n >= 0) A by induc n from 0:
        case n < 1: seed
        case n >= 1: seeded_generic(n - 1)

\seeded_generic<R, 3>(0) = 3

\seeded_generic<R, 3>(1) = \seeded_generic<R, 3>(0) = 3

forall A set, seed A:
    \seeded_generic<A, seed>(0) = seed
    \seeded_generic<A, seed>(1) = \seeded_generic<A, seed>(0) = seed
"#;

#[test]
fn recursive_set_template_replays_a_published_equation_through_known_forall() {
    let (mut run, compiler) = super::execute(TEMPLATE_SET_SEED);
    let template = recursive_template(&mut run);
    let published = template
        .definition_facts
        .iter()
        .map(|p| p.store_and_infer.primary_fact_id())
        .collect::<Vec<_>>();
    let fact = super::fact_statement_mut(&mut run.statement_results[2]);
    let VerifyFactResult::ChainFact(chain) = &fact.verify_result else {
        panic!("source equality chain")
    };
    let crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult::Success(chain) =
        chain.as_ref()
    else {
        panic!()
    };
    let VerifyFactResult::Equality(equality) = &chain.adjacent[0] else {
        panic!()
    };
    let VerifyEqualityResult::Success(equality) = equality.as_ref() else {
        panic!()
    };
    let EqualFactSearchedProof::ByKnownForallFact(proof) = &equality.searched_proof else {
        panic!("original known-forall route")
    };
    assert!(published.contains(&proof.detailed_ref().cite.fact_id));
    compiler
        .compile_run(&run, "original_recursive_citation")
        .unwrap();
}

#[test]
fn recursive_completed_calls_still_require_the_original_decrease_evidence() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(TEMPLATE_SET_SEED);
        let template = recursive_template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(body),
        )) = template.body.as_mut()
        else {
            panic!()
        };
        let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } =
            &mut body.case_checks.cases[1].body
        else {
            panic!()
        };
        let Some(DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        }) = well_defined.as_detailed_success_mut().unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => {
                call.requirement_fact_verified.pop();
            }
            1 => call.requirement_fact_verified.swap(0, 1),
            2 => {
                let Some(FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. }) =
                    &mut call.domain_fn_set
                else {
                    panic!()
                };
                *fact_id = FactId::new(u64::MAX);
            }
            3 => {
                let Some(FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }) =
                    &mut call.domain_fn_set
                else {
                    panic!()
                };
                fn_set.dom_facts.reverse();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "changed_recursive_call")
            .expect_err(
                "full-graph reconstruction cannot discard or alter restricted-call evidence",
            );
    }
}

#[test]
fn recursive_call_evidence_cannot_escape_its_selected_case() {
    let (mut run, compiler) = super::execute(TEMPLATE_SET_SEED);
    // Borrow the actual declaration after mutation-capable helpers have returned.
    let template = recursive_template(&mut run);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(body),
    )) = template.body.as_ref()
    else {
        panic!()
    };
    let head = template
        .statement
        .template_arg_def
        .ordered_param_ids()
        .len();
    let header = SourcePosition::new(None, SourceOwner::Template(template), head);
    let recursion = SourcePosition::new(Some(&header), SourceOwner::RecursiveFunction(body), 8);
    let case = &body.case_checks.cases[1];
    let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } = &case.body else {
        panic!()
    };
    let VerifyObjWellDefinedResult::Success(wd) = well_defined else {
        panic!()
    };
    let visible = SourcePosition::new(Some(&recursion), SourceOwner::RecursiveCase(case), 1);
    compiler
        .compile_recursive_call_arguments(wd.obj(), body, wd, &visible)
        .unwrap();
    let pending = SourcePosition {
        before: 0,
        ..visible
    };
    assert!(compiler
        .compile_recursive_call_arguments(wd.obj(), body, wd, &pending)
        .is_err());
    let sibling = SourcePosition::new(
        Some(&recursion),
        SourceOwner::RecursiveCase(&body.case_checks.cases[0]),
        1,
    );
    assert!(compiler
        .compile_recursive_call_arguments(wd.obj(), body, wd, &sibling)
        .is_err());
}

const INTEGER_COUNT: &str = r#"# Count integer steps above a variable lower bound, starting from a captured real seed.
template<seed R>:
    have fn seeded_bounded(n, b Z: n >= b) R by induc n from b:
        case n = b: seed
        case n > b: seeded_bounded(n - 1, b) + 1

\seeded_bounded<7>(0, 0) = 7

\seeded_bounded<7>(1, 0) = \seeded_bounded<7>(0, 0) + 1 = 8
"#;

#[test]
fn integer_recursive_count_retains_the_selected_discrete_order_rule() {
    use crate::compile_to_lean::source_position::visit_complete_wd;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute(INTEGER_COUNT);
    let template = recursive_template(&mut run);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(body),
    )) = template.body.as_ref()
    else {
        panic!()
    };
    let header = SourcePosition::new(None, SourceOwner::Template(template), 1);
    let recursion = SourcePosition::new(Some(&header), SourceOwner::RecursiveFunction(body), 8);
    let case = &body.case_checks.cases[1];
    let case_scope = SourcePosition::new(Some(&recursion), SourceOwner::RecursiveCase(case), 1);
    let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } = &case.body else {
        panic!()
    };
    let VerifyObjWellDefinedResult::Success(wd) = well_defined else {
        panic!()
    };
    let selected = visit_complete_wd(wd, &case_scope, &mut |_, _| Ok(None), &mut |checked, _| {
        let VerifyFactResult::AtomicExceptEquality(result) = checked else {
            return Ok(None);
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = result.as_ref() else {
            return Ok(None);
        };
        let p = if let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(dual),
        ) = &p.searched_proof
        {
            let VerifyFactResult::AtomicExceptEquality(child) = &dual.proof_of_alternate_fact
            else {
                panic!()
            };
            let VerifyAtomicExceptEqualityFactResult::Success(child) = child.as_ref() else {
                panic!()
            };
            child
        } else {
            p
        };
        if let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorGap(gap),
            ),
        ) = &p.searched_proof
        {
            Ok(Some((p.fact.ir(), gap.strict_order.fact.ir())))
        } else {
            Ok(None)
        }
    })
    .unwrap()
    .expect("actual integer-gap rule in recursive call WD");
    eprintln!("selected integer gap: {selected:?}");
    compiler
        .compile_run(&run, "integer_recursive_count")
        .unwrap();
}

#[test]
fn integer_gap_replays_both_alignments_and_exact_citations() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
    const SOURCE: &str = r#"# Integers separated by a strict inequality differ by at least one.
forall a, b Z: a < b => a + 1 <= b
forall a, b Z: a < b => a <= b - 1
forall a, b Z: 1 + a < b => a + 2 <= b
forall a Z: 4 < a => 5 <= a
forall a Z: a < 0 => a <= -1
"#;
    let (mut run, compiler) = super::execute(SOURCE);
    for (index, result) in run.statement_results.iter_mut().enumerate() {
        let forall = super::forall_proof_mut(result);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
        ) = &atomic.searched_proof
        else {
            panic!("selected integer rule")
        };
        let selected = match rule {
            LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorLe(_) => "successor",
            LessEqualFactSearchProofByBuiltinRule::IntegerPredecessorLe(_) => "predecessor",
            LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorGap(_) => "gap",
            LessEqualFactSearchProofByBuiltinRule::NumericLowerBoundFromStrictPredecessorLe(_) => {
                "numeric"
            }
            LessEqualFactSearchProofByBuiltinRule::IntegerAdjacencyLe(_) => "adjacency",
            _ => panic!("another integer route"),
        };
        assert_eq!(
            selected,
            ["successor", "predecessor", "gap", "numeric", "adjacency"][index]
        );
    }
    let lean = compiler.compile_run(&run, "integer_gap").unwrap();
    assert!(lean.contains("Litex.integerGapLe"));
    assert!(lean.contains("Or.inl ⟨by ring!, by ring!⟩"));
    let (other, other_compiler) = super::execute(
        r#"# The original greater-than premise is transposed without a new search.
forall gap_left, gap_right Z:
    gap_right > gap_left
    =>:
        gap_left <= gap_right - 1
"#,
    );
    let other_lean = other_compiler
        .compile_run(&other, "predecessor_gap")
        .unwrap();
    assert!(other_lean.contains("Or.inr ⟨by ring!, by ring!⟩"));
    assert_eq!(lean, compiler.compile_run(&run, "integer_gap").unwrap());
}

#[test]
fn integer_gap_rejects_changed_integer_subjects_and_strict_order() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute("forall a, b Z: b > a => a <= b - 1\n");
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let future_id = atomic.fact.fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorGap(gap),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!()
        };
        match mutation {
            0 | 1 => {
                let member = super::atomic_proof_mut(if mutation == 0 {
                    &mut gap.left_integer
                } else {
                    &mut gap.right_integer
                });
                let AtomicFact::InFact(member) = &mut member.fact else {
                    panic!()
                };
                member.set = Obj::StandardSet(StandardSet::R);
            }
            2 => std::mem::swap(&mut gap.left_integer, &mut gap.right_integer),
            3 => {
                let AtomicFact::GreaterFact(order) = &mut gap.strict_order.fact else {
                    panic!()
                };
                std::mem::swap(&mut order.left, &mut order.right);
            }
            4 => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    gap.strict_order.searched_proof.as_mut()
                else {
                    panic!()
                };
                cite.cite_fact_id = future_id;
            }
            5 => {
                let AtomicFact::LessEqualFact(goal) = &mut atomic.fact else {
                    panic!()
                };
                goal.left = super::number_object("0");
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "forged_gap")
            .expect_err("exact integer-gap premises");
    }
}

#[test]
fn integer_gap_replays_guarded_cancellation_from_original_formation() {
    let (run, compiler) = super::execute(
        "forall a, b Z, c R:\n    c != 0\n    a < b\n    =>:\n        a * c / c + 1 <= b\n",
    );
    let lean = compiler.compile_run(&run, "guarded_gap").unwrap();
    assert!(lean.contains("Litex.integerGapLe"));
    assert!(lean.contains("litex_normalize_rational"));
    assert!(lean.contains("nativeNonzeroOfDenote"));
}
