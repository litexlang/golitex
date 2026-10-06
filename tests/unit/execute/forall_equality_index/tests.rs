use super::*;
use crate::ast::fact::{AtomicFact, DirectForallConclusionLocation, Fact};
use crate::ast::obj::{Add, ArithmeticOperator, FnObj, FnObjHead, IdentifierObj, Literal, Number};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    EqualFactSearchedProof, EqualFactSearchedProofByEquivalenceClass,
    ForallConclusionArgMatchProof, StrictEqualArgProof, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::{ExecFactStmtResult, VerifyFactResult};
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn unchanged_positive_and_negative_runtime_controls() {
    let cases = [
        (
            r#"forall f fn(x R) R:
    forall t R:
        f(t) = t
    =>:
        f(2) = 2
"#,
            true,
        ),
        (
            r#"forall f fn(x R) R:
    forall t R:
        f(t) = t
    =>:
        f(2) = 3
"#,
            false,
        ),
        (
            r#"forall f fn(x R) R, a R:
    forall h fn(x R) R, t R:
        h(t) = t
    =>:
        f(a) = a
"#,
            true,
        ),
        (
            r#"forall f, g fn(x R) R, a R:
    f(0) = g(0)
    forall y R:
        y + f(0) = y
    =>:
        a + g(0) = a
"#,
            true,
        ),
        (
            r#"forall f fn(x R) fn(y R) R, a, b R:
    forall h fn(y R) R, t R:
        h(t) = t
    =>:
        f(a)(b) = b
"#,
            true,
        ),
        (
            r#"claim:
    ? forall f, g fn(x R) R, a R:
        f(0) = g(0)
        forall y R:
            y + f(0) = y
        =>:
            a + g(0) = a
    a + g(0) = a + f(0)
    a + f(0) = a
"#,
            true,
        ),
        (
            r#"forall f, g fn(x R) R:
    forall t R:
        f(t) = t
    =>:
        g(2) = 2
"#,
            false,
        ),
        (
            r#"forall f, g fn(x R) R:
    f = g
    forall t R:
        f(t) = t
    =>:
        g(2) = 2
"#,
            true,
        ),
        (
            r#"forall f fn(x, y R) R, a, b R:
    forall t R:
        f(t, t) = t
    =>:
        f(a, b) = a
"#,
            false,
        ),
        (
            r#"forall f fn(x, y R) R, a, b R:
    a = b
    forall t R:
        f(t, t) = t
    =>:
        f(a, b) = a
"#,
            true,
        ),
        (
            r#"forall f fn(x R) R:
    forall t N:
        f(t) = t
    =>:
        f(2.5) = 2.5
"#,
            false,
        ),
        (
            r#"forall f fn(x, y R) R, a R:
    forall t R:
        f(1+1, t) = t
    =>:
        f(2, a) = a
"#,
            true,
        ),
        (
            r#"forall f fn(x, y R) R, h fn(x R) R, a, b, c R:
    a = b
    forall t R:
        f(h(a), t) = t
    =>:
        f(h(b), c) = c
"#,
            true,
        ),
        (
            r#"forall f fn(x, y R) R, h fn(x R) R, a, b, c R:
    a = b
    forall t R:
        f(h(h(a)), t) = t
    =>:
        f(h(h(b)), c) = c
"#,
            true,
        ),
    ];
    for (source, expected) in cases {
        let mut rt = runtime();
        let result = rt.run_litex_code(source).unwrap();
        assert!(
            result.session_error.is_none(),
            "{source}: {:?}",
            result.session_error
        );
        assert_eq!(result.success, expected, "{source}");
    }
}

#[test]
fn primary_tracer_keeps_real_forall_and_rigid_path_evidence() {
    let mut rt = runtime();
    let result = rt
        .run_litex_code(include_str!(
            "../../../../examples/proof_nodes/equal/by_known_forall/rigid_application_alias.lit"
        ))
        .unwrap();
    assert!(result.success && result.session_error.is_none());
    let detail =
        crate::json_output::project_stmt_detailed(&result.statement_results[0], &rt).stringify();
    assert!(detail.contains("by_known_forall"), "{detail}");
    assert!(detail.contains("cite_fact_id"), "{detail}");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &result.statement_results[0]
    else {
        panic!("fact result");
    };
    let VerifyFactResult::ForallFact(forall) = &fact.verify_result else {
        panic!("forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_ref()
    else {
        panic!("forall scope");
    };
    let VerifyFactResult::Equality(equal) = &forall.proved_then_facts[0].verify_result else {
        panic!("then equality");
    };
    let VerifyEqualityResult::Success(equal) = equal.as_ref() else {
        panic!("verified equality");
    };
    let EqualFactSearchedProof::ByKnownForallFact(proof) = &equal.searched_proof else {
        panic!("real source theorem");
    };
    assert!(forall
        .local_env
        .facts
        .facts_by_id
        .contains_key(&proof.cite.fact_id));
    assert_eq!(
        proof
            .instantiation_requirements
            .param_type_requirements
            .len(),
        1
    );
    let ForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        &proof.arg_match_proofs[0]
    else {
        panic!("addition transport");
    };
    let ForallConclusionArgMatchProof::NonParamEqual { equal, .. } = &child_matches[1] else {
        panic!("rigid value transport");
    };
    let StrictEqualArgProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &equal.equal_proof
    else {
        panic!("Direct existing path, without peer search");
    };
    assert_eq!(path.path.len(), 1);
    assert!(forall
        .local_env
        .facts
        .facts_by_id
        .contains_key(&path.path[0].2));
    let source = "forall f, g fn(x R) R, a R:\n    forall y R:\n        y + f(0) = y\n    =>:\n        a + g(0) = a";
    let mut rt = runtime();
    assert!(!rt.run_litex_code(source).unwrap().success);
}

#[test]
fn index_lifetime_follows_commit_failed_claim_and_sketch() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("sketch:\n    forall x R:\n        x = x")
            .unwrap()
            .success
    );
    assert!(rt
        .top_exec_env()
        .facts
        .known_forall_conclusions
        .by_equal
        .is_empty());
    let failed = rt
        .run_litex_code("claim:\n    ? 0=1\n    forall x R:\n        x=x")
        .unwrap();
    assert!(!failed.success && failed.session_error.is_none());
    assert!(rt
        .top_exec_env()
        .facts
        .known_forall_conclusions
        .by_equal
        .is_empty());
    assert!(rt.run_litex_code("forall x R:\n    x=x=x").unwrap().success);
    let index = &rt.top_exec_env().facts.known_forall_conclusions.by_equal;
    assert_eq!(
        index.len(),
        2,
        "both committed chain edges must survive merge"
    );
    for i in 0..index.len() {
        let cite = index.cite(i);
        assert!(matches!(
            cite.location,
            ForallConclusionLocation::ChainFactComponent(_)
        ));
        assert!(matches!(
            rt.fact_by_id_in_stack(cite.fact_id),
            Some(Fact::ForallFact(_))
        ));
    }
    let mut child = index.clone();
    child.merge_from(index);
    assert_eq!(
        child.len(),
        2,
        "derived entries deduplicate by exact source cite"
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

// Metadata-only scaling controls: no unproved source is used as a runtime proof.
#[test]
fn nested_constructor_and_both_endpoint_index_prune_10000_patterns() {
    let x = IdentifierId::new(1);
    for count in [100, 1000, 10000] {
        let record_started = std::time::Instant::now();
        let mut index = ForallEqualityIndex::new();
        for i in 0..count {
            let left = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(application(IdentifierId::new(i as u64 + 10), object(x))),
                right: Box::new(number(0)),
            }));
            let eq = EqualFact {
                fact_id: FactId::new(i as u64 + 1),
                left,
                right: object(x),
                line_file: None,
            };
            index.record(&eq, &[x], cite(eq.fact_id));
        }
        let record_elapsed = record_started.elapsed();
        let wanted = count / 2;
        let goal = EqualFact {
            fact_id: FactId::new(20001),
            left: Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(application(
                    IdentifierId::new(wanted as u64 + 10),
                    number(2),
                )),
                right: Box::new(number(0)),
            })),
            right: number(2),
            line_file: None,
        };
        let query_started = std::time::Instant::now();
        let selected = index.candidates(&goal, &mut EqualityIndexQuery::new(Vec::new()));
        println!(
            "fixed sources={count} candidates={} index_nodes={} record_us={} query_us={}",
            selected.len(),
            index.nodes.len(),
            record_elapsed.as_micros(),
            query_started.elapsed().as_micros()
        );
        assert_eq!(
            selected.len(),
            1,
            "nested fixed heads at population {count}"
        );
        assert_eq!(selected[0].fact_id, FactId::new(wanted as u64 + 1));

        let mut right_index = ForallEqualityIndex::new();
        for i in 0..count {
            let eq = EqualFact {
                fact_id: FactId::new(i as u64 + 1),
                left: application(IdentifierId::new(2), object(x)),
                right: number(i),
                line_file: None,
            };
            right_index.record(&eq, &[x], cite(eq.fact_id));
        }
        let goal = EqualFact {
            fact_id: FactId::new(20001),
            left: application(IdentifierId::new(2), number(7)),
            right: number(wanted),
            line_file: None,
        };
        assert_eq!(
            right_index
                .candidates(&goal, &mut EqualityIndexQuery::new(Vec::new()))
                .len(),
            1,
            "right endpoint at population {count}"
        );
    }
}

#[test]
fn retrieval_is_conservative_against_real_argument_matcher() {
    let mut rt = runtime();
    let source = "have fn f(x, y R) R = y\nhave fn h(x R) R = x\nforall t R:\n    f(1+1,t)=t\nforall t R:\n    f(sqrt(8)/2,t)=t\nforall t R:\n    f(h(h(2)),t)=t\nforall t R:\n    f(t,t)=t+0\nforall t R:\n    f(t+1,t)=t\nforall a R:\n    fn(z R) R {a}=fn(z R) R {a}\n";
    let result = rt.run_litex_code(source).unwrap();
    assert!(result.success && result.session_error.is_none());
    for goal_source in [
        "f(2,7)=7",
        "f(sqrt(2),7)=7",
        "f(h(h(2)),7)=7",
        "f(9,7)=7",
        "f(1,1)=1",
        "f(1+1,1)=1",
        "fn(q R) R {0}=fn(q R) R {0}",
    ] {
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(goal_source, rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let crate::ast::stmt::Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(goal))) =
            &statements[0]
        else {
            panic!("equality");
        };
        let selected =
            rt.visible_forall_atomic_conclusion_candidates(&AtomicFact::EqualFact(goal.clone()));
        let cites: Vec<_> = rt
            .execution_environments_stack
            .iter()
            .rev()
            .flat_map(|env| {
                let index = &env.facts.known_forall_conclusions.by_equal;
                (0..index.len())
                    .map(|i| index.cite(i).clone())
                    .collect::<Vec<_>>()
            })
            .collect();
        for cite in cites {
            let Some(Fact::ForallFact(forall)) = rt.fact_by_id_in_stack(cite.fact_id).cloned()
            else {
                panic!("real forall");
            };
            let Some(AtomicFact::EqualFact(pattern)) =
                crate::exec_env::atomic_at_forall_location(&forall, &cite.location)
            else {
                continue;
            };
            let matches = rt
                .match_forall_conclusion_args_to_subst(
                    &[&pattern.left, &pattern.right],
                    &[&goal.left, &goal.right],
                    &forall.typed_parameters.ordered_param_ids(),
                )
                .unwrap()
                .is_some();
            if matches {
                assert!(
                    selected.contains(&cite),
                    "index missed {goal_source}: {:?}",
                    cite.location
                );
            }
        }
    }
}

#[test]
fn bound_expression_and_numeric_structure_are_not_filtered_out() {
    for (conclusion, goal, expected) in [
        ("f(t)=t+1", "f(1)=2", true),
        ("f(t)=t+1", "f(1)=3", false),
        ("f(t)=t+1", "2=f(1)", true),
        ("f(t+1)=t", "f(1+1)=1", true),
        ("f(t+1)=t", "f(2)=1", false),
    ] {
        let source = format!(
            "forall f fn(x R) R:\n    forall t R:\n        {conclusion}\n    =>:\n        {goal}\n"
        );
        let mut rt = runtime();
        let result = rt.run_litex_code(&source).unwrap();
        assert!(result.session_error.is_none(), "{source}");
        assert_eq!(result.success, expected, "{source}");
    }
    // Shared suffix peeling rejects at the different inner arity, then the
    // already-bound full application can cite an existing Direct equality.
    let source = "forall f fn(x, y R) fn(z R) R, g fn(x R) fn(z R) R:\n    f(1,2)(0)=g(1)(0)\n    forall t R:\n        t=f(t,2)(0)\n    =>:\n        1=g(1)(0)\n";
    let mut rt = runtime();
    assert!(rt.run_litex_code(source).unwrap().success);
    // Argument visitation order differs between nested indexing and the
    // legacy flattened certificate: the outer argument binds t first.
    let source = "forall f fn(x R) fn(y R) R:\n    forall t R:\n        f(t+1)(t)=t\n    =>:\n        f(2)(1)=1\n";
    let mut rt = runtime();
    assert!(rt.run_litex_code(source).unwrap().success);
}

#[test]
fn unrelated_binder_aliases_do_not_supply_direct_forall_matches() {
    let mut rt = runtime();
    let result = rt.run_litex_code("have fn f(x R) R=x\nhave fn g(y R) R=y\nf=fn(x R) R {x}\ng=fn(y R) R {y}\nforall t R:\n    f(t)=t\n").unwrap();
    assert!(result.success && result.session_error.is_none());
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("g(2)=2", rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    let crate::ast::stmt::Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(goal))) =
        &statements[0]
    else {
        panic!("equality");
    };
    let selected =
        rt.visible_forall_atomic_conclusion_candidates(&AtomicFact::EqualFact(goal.clone()));
    let index = &rt.top_exec_env().facts.known_forall_conclusions.by_equal;
    let cite = index.cite(index.len() - 1).clone();
    let Some(Fact::ForallFact(forall)) = rt.fact_by_id_in_stack(cite.fact_id).cloned() else {
        panic!("real source");
    };
    let Some(AtomicFact::EqualFact(pattern)) =
        crate::exec_env::atomic_at_forall_location(&forall, &cite.location)
    else {
        panic!("then");
    };
    assert!(rt
        .match_forall_conclusion_args_to_subst(
            &[&pattern.left, &pattern.right],
            &[&goal.left, &goal.right],
            &forall.typed_parameters.ordered_param_ids()
        )
        .unwrap()
        .is_none());
    assert!(
        !selected.contains(&cite),
        "candidate discovery must not alpha-anchor unrelated stored classes"
    );
}

#[test]
fn truly_generic_parameters_remain_candidates_at_10000_sources() {
    let x = IdentifierId::new(1);
    let y = IdentifierId::new(2);
    for count in [100, 1000, 10000] {
        let start = std::time::Instant::now();
        let mut index = ForallEqualityIndex::new();
        for i in 0..count {
            let equal = EqualFact {
                fact_id: FactId::new(i + 1),
                left: object(x),
                right: object(y),
                line_file: None,
            };
            index.record(&equal, &[x, y], cite(equal.fact_id));
        }
        let recorded = start.elapsed();
        let goal = EqualFact {
            fact_id: FactId::new(count + 1),
            left: number(2),
            right: number(3),
            line_file: None,
        };
        let start = std::time::Instant::now();
        let selected = index.candidates(&goal, &mut EqualityIndexQuery::new(Vec::new()));
        assert_eq!(selected.len(), count as usize);
        println!(
            "generic sources={count} candidates={} index_nodes={} record_us={} query_us={}",
            selected.len(),
            index.nodes.len(),
            recorded.as_micros(),
            start.elapsed().as_micros()
        );
    }
}

fn object(id: IdentifierId) -> Obj {
    Obj::Identifier(IdentifierObj::plain(id, format!("v{}", id.value())))
}
fn number(value: usize) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: value.to_string(),
    }))
}
fn application(head: IdentifierId, argument: Obj) -> Obj {
    Obj::FnObj(FnObj {
        head: Box::new(FnObjHead::Identifier(IdentifierObj::plain(
            head,
            format!("v{}", head.value()),
        ))),
        body: vec![vec![Box::new(argument)]],
    })
}
fn cite(fact_id: FactId) -> ForallConclusionCite {
    ForallConclusionCite {
        fact_id,
        location: ForallConclusionLocation::DirectThenFact(DirectForallConclusionLocation {
            then_fact_index: 0,
        }),
    }
}

#[test]
fn direct_numeric_keys_do_not_drop_large_or_radical_equalities() {
    for (left, right) in [
        ("1+1", "2"),
        ("2/4", "0.5"),
        ("sqrt(8)/2", "sqrt(2)"),
        ("i+i", "2*i"),
        (
            "99999999999999999999999999999999999999999999999999+1",
            "100000000000000000000000000000000000000000000000000",
        ),
        ("floor(2.5)", "2"),
        ("gcd(18,12)", "6"),
    ] {
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(&format!("{left}={right}"), rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let crate::ast::stmt::Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(equal))) =
            &statements[0]
        else {
            panic!("numeric equality");
        };
        assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::calculate_closed_atomic_fact::calculate_closed_atomic_fact(&equal.clone().into()).is_some(), "Direct calculation {left}={right}");
        let mut index = ForallEqualityIndex::new();
        let source = EqualFact {
            fact_id: FactId::new(1),
            left: equal.left.clone(),
            right: number(0),
            line_file: None,
        };
        index.record(&source, &[], cite(source.fact_id));
        let goal = EqualFact {
            fact_id: FactId::new(2),
            left: equal.right.clone(),
            right: number(0),
            line_file: None,
        };
        assert_eq!(
            index
                .candidates(&goal, &mut EqualityIndexQuery::new(Vec::new()))
                .len(),
            1,
            "compatible numeric keys {left}={right}"
        );
    }
}

#[test]
fn owner_qualified_heads_and_recording_roles_stay_distinct() {
    let x = IdentifierId::new(1);
    let mut index = ForallEqualityIndex::new();
    for owner in [2, 3] {
        let left = Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(
                IdentifierObj::with_mod_and_export_file_id(owner, 0, "f".into()),
            )),
            body: vec![vec![Box::new(object(x))]],
        });
        let equal = EqualFact {
            fact_id: FactId::new(owner as u64),
            left,
            right: object(x),
            line_file: None,
        };
        index.record(&equal, &[x], cite(equal.fact_id));
    }
    let goal = EqualFact {
        fact_id: FactId::new(20),
        left: Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(
                IdentifierObj::with_mod_and_export_file_id(2, 0, "f".into()),
            )),
            body: vec![vec![Box::new(number(7))]],
        }),
        right: number(7),
        line_file: None,
    };
    let selected = index.candidates(&goal, &mut EqualityIndexQuery::new(Vec::new()));
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].fact_id, FactId::new(2));
    assert!(index.entries[0]
        .tokens
        .iter()
        .any(|token| matches!(token, Token::Parameter)));
    let rigid = EqualFact {
        fact_id: FactId::new(21),
        left: application(IdentifierId::new(9), number(0)),
        right: object(x),
        line_file: None,
    };
    index.record(&rigid, &[x], cite(rigid.fact_id));
    assert!(index.entries[2]
        .tokens
        .iter()
        .any(|token| matches!(token, Token::RigidNode(_, _))));
}
