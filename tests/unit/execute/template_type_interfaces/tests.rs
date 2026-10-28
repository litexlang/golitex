use crate::prelude::*;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
fn run(rt: &mut Runtime, code: &str, expected: bool) -> RunLitexCodeResult {
    let result = rt.run_litex_code(code).unwrap();
    assert_eq!(
        result.success, expected,
        "{}: {:?}",
        code, result.session_error
    );
    assert!(
        result.session_error.is_none(),
        "{}: {:?}",
        code,
        result.session_error
    );
    result
}
fn fact(rt: &mut Runtime, code: &str) -> Fact {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    match statements.remove(0) {
        Stmt::Fact(f) => f,
        _ => panic!("fact"),
    }
}

#[test]
fn template_type_interfaces_maps_construct() {
    run(&mut runtime(), "template<A,B nonempty_set>:\n    have maps set = fn(x A) B\nhave value \\maps<R,Z> = fn(x R) Z {0}\n", true);
}

#[test]
fn template_type_interfaces_pairs_construct() {
    run(
        &mut runtime(),
        "template<S set>:\n    have pairs set = cart(S,S)\nhave value \\pairs<R> = (1,2)\n",
        true,
    );
}

#[test]
fn template_type_interfaces_vectors_construct() {
    run(&mut runtime(), "template<S set,n N>:\n    have vectors set = finite_seq(S,n)\nhave value \\vectors<R,2> = (1,2)\n", true);
}

#[test]
fn template_type_interfaces_subsets_construct() {
    run(
        &mut runtime(),
        "template<S set>:\n    have subsets set = power_set(S)\nhave value \\subsets<R> = {1,2}\n",
        true,
    );
}

#[test]
fn template_type_interfaces_above_construct() {
    run(
        &mut runtime(),
        "template<a R>:\n    have above set = {x R:x>a}\nhave value \\above<0> = 1\n",
        true,
    );
}

#[test]
fn template_type_interfaces_singleton_construct() {
    run(
        &mut runtime(),
        "template<n N>:\n    have singleton set = {n}\nhave value \\singleton<1> = 1\n",
        true,
    );
}

#[test]
fn template_type_interfaces_segment_construct() {
    run(&mut runtime(), "template<a,b Z>:\n    have segment set = closed_range(a,b)\nhave value \\segment<1,3> = 2\n", true);
}

#[test]
fn template_type_interfaces_generic_first() {
    run(&mut runtime(), "template<S set>:\n    have pairs set = cart(S,S)\ntemplate<S set>:\n    have fn first(p \\pairs<S>) S = p(1)\n\\first<R>((1,2)) = 1\n", true);
}

#[test]
fn template_type_interfaces_generic_apply() {
    run(&mut runtime(), "template<A,B nonempty_set>:\n    have maps set = fn(x A) B\ntemplate<A,B nonempty_set>:\n    have fn apply(f \\maps<A,B>,x A) B = f(x)\n\\apply<R,R>(fn(x R) R {x+1},2) = 3\n", true);
}

#[test]
fn template_type_interfaces_vectors_consumer() {
    run(&mut runtime(), "template<S set,n N>:\n    have vectors set = finite_seq(S,n)\nhave fn second(v \\vectors<R,2>) R = v(2)\nsecond((1,2)) = 2\n", true);
}

#[test]
fn template_type_interfaces_pairs_binder() {
    run(&mut runtime(), "template<S set>:\n    have pairs set = cart(S,S)\nforall S set,p \\pairs<S>:\n    p(1) $in S\n", true);
}

#[test]
fn template_type_interfaces_subsets_binder() {
    run(&mut runtime(), "template<S set>:\n    have subsets set = power_set(S)\nforall U \\subsets<R>:\n    U $subset R\n", true);
}

#[test]
fn template_type_interfaces_segment_binder() {
    run(&mut runtime(), "template<a,b Z>:\n    have segment set = closed_range(a,b)\nforall a,b Z,x \\segment<a,b>:\n    x>=a\n    x<=b\n", true);
}

#[test]
fn template_type_interfaces_make_return() {
    run(&mut runtime(), "template<A,B nonempty_set>:\n    have maps set = fn(x A) B\nhave fn make(a R) \\maps<R,R> = fn(x R) R {x+a}\nmake(2)(3) = 5\n", true);
}

#[test]
fn template_type_interfaces_nested() {
    run(&mut runtime(), "template<S set>:\n    have pairs set = cart(S,S)\ntemplate<T set>:\n    have wrapped set = \\pairs<T>\nhave p \\wrapped<R> = (1,2)\nforall q \\wrapped<R>:\n    q(2) $in R\n", true);
}

#[test]
fn template_type_interfaces_bad_pair() {
    run(
        &mut runtime(),
        "template<S set>:\n    have pairs set = cart(S,S)\nhave p \\pairs<R> = (1,i)\n",
        false,
    );
}

#[test]
fn template_type_interfaces_bad_domain() {
    run(&mut runtime(), "template<A,B nonempty_set>:\n    have maps set = fn(x A) B\nhave f \\maps<R,Z> = fn(x N) Z {0}\n", false);
}

#[test]
fn template_type_interfaces_bad_filter() {
    run(
        &mut runtime(),
        "template<a R>:\n    have above set = {x R:x>a}\nhave x \\above<0> = -1\n",
        false,
    );
}

#[test]
fn template_type_interfaces_bad_guard() {
    run(&mut runtime(), "template<S set: $is_nonempty_set(S)>:\n    have pairs set = cart(S,S)\nhave p \\pairs<{}> = (1,2)\n", false);
}

#[test]
fn template_type_interfaces_native_search_permissions_and_read_only_conversion() {
    use VerifyStateLevel::*;
    let mut rt = runtime();
    run(
        &mut rt,
        "template<A,B nonempty_set>:\n    have maps set = fn(x A) B\n",
        true,
    );
    let native = fact(&mut rt, "fn(x R) R {x} $in fn(x R) R");
    let wrapped = fact(&mut rt, "fn(x R) R {x} $in \\maps<R,R>");
    let bad = fact(&mut rt, "fn(x N) R {x} $in \\maps<R,R>");
    for level in [
        Direct,
        KnownSpecialProperty,
        BuiltinRule,
        Strategy,
        DefinitionAndForall,
    ] {
        let state = VerifyState::new(level);
        let count = rt.top_exec_env().facts.facts_by_id.len();
        let mut search = |f: &Fact| {
            let Fact::AtomicFact(f) = f else {
                panic!("atomic")
            };
            rt.search_atomic_except_equality_fact_proof(f, state)
                .unwrap()
                .is_some()
        };
        assert_eq!(search(&native), search(&wrapped), "{level:?}");
        assert!(!search(&bad), "{level:?}");
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
    }
}

#[test]
fn template_type_interfaces_preserve_alias_boundaries_and_rollback() {
    let mut rt = runtime();
    run(
        &mut rt,
        "template<S set>:\n    have pairs set = cart(S,S)\nlet alias = \\pairs<R>\n",
        true,
    );
    run(&mut rt, "forall q alias:\n    q(1) $in R\n", false);
    run(
        &mut rt,
        "have fn identity(x R) R = x\nlet copied = identity\n",
        true,
    );
    run(&mut rt, "copied(1) = 1\n", false);
    let count = rt.top_exec_env().facts.facts_by_id.len();
    run(
        &mut rt,
        "forall p \\pairs<R>:\n    p(1) $in R\n    0 = 1\n",
        false,
    );
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
    run(&mut rt, "have p \\pairs<R> = (1,2)\np(2) = 2\n", true);
}

#[test]
fn template_type_interfaces_keep_conversion_and_native_evidence() {
    use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};
    let mut rt = runtime();
    run(
        &mut rt,
        "template<S set>:\n    have pairs set = cart(S,S)\n",
        true,
    );
    let result = run(&mut rt, "(1,2) $in \\pairs<R>\n", true);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &result.statement_results[0]
    else {
        panic!("fact")
    };
    let VerifyFactResult::AtomicExceptEquality(verify) = &stmt.verify_result else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(success) = verify.as_ref() else {
        panic!("success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByTemplateMembership(proof) =
        &success.searched_proof
    else {
        panic!("conversion")
    };
    assert_eq!(proof.expansions.len(), 1);
    assert!(matches!(proof.expansions[0].set, Obj::ProductShape(_)));
    assert!(!matches!(
        proof.residual.as_ref(),
        AtomicExceptEqualityFactSearchedProof::ByTemplateMembership(_)
    ));
    let stored = &stmt.store_and_infer_result;
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &stored.infer else {
        panic!("membership")
    };
    let [InferInFactResult::Template(infer)] = rules.as_slice() else {
        panic!("template")
    };
    assert_eq!(infer.source_fact_id, stored.primary_fact_id());
    assert_eq!(infer.stores.len(), 1);
    assert!(infer
        .native_rules
        .iter()
        .any(|r| matches!(r, InferInFactResult::CartCoordinates(_))));
    for id in stored.stored_fact_ids() {
        assert!(rt.fact_by_id_in_stack(id).is_some());
    }
    let detail =
        crate::json_output::project_stmt_detailed(&result.statement_results[0], &rt).stringify();
    for key in [
        "by_template_membership",
        "expanded_memberships",
        "residual",
        "template_membership_rules",
        "native_conclusions",
    ] {
        assert!(detail.contains(key), "{key}: {detail}");
    }
}

#[test]
fn template_type_interfaces_convert_only_the_seed_not_derived_builder_conditions() {
    let mut rt = runtime();
    run(
        &mut rt,
        "prop inner(x R):\n    x=x\ntemplate<S set>:\n    have marked set = {x R: $inner(x)}\n",
        true,
    );
    let result = run(&mut rt, "forall x \\marked<R>:\n    x=x\n", true);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &result.statement_results[0]
    else {
        panic!("fact")
    };
    let VerifyFactResult::ForallFact(verified) = &stmt.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(local)) =
        verified.as_ref()
    else {
        panic!("local")
    };
    let source = &local
        .introduced_params
        .defined_params
        .store_and_infer_results[0];
    let facts = source
        .stored_fact_ids()
        .into_iter()
        .filter_map(|id| local.local_env.facts.facts_by_id.get(&id))
        .map(|f| f.readable_string())
        .collect::<Vec<_>>();
    assert!(facts.iter().any(|f| f == "$inner(x)"));
    assert!(!facts.iter().any(|f| f == "x = x"));
}

#[test]
fn template_type_interfaces_lean_export_fails_closed() {
    let mut rt = runtime();
    let result = run(
        &mut rt,
        "template<S set>:\n    have pairs set = cart(S,S)\n(1,2) $in \\pairs<R>\n",
        true,
    );
    let compiler = crate::compile_to_lean::LitexToLeanCompiler::new(rt);
    assert!(compiler
        .compile_run(&result, "template_membership")
        .is_err());
}

#[test]
fn template_type_interfaces_nested_same_owner_is_not_a_cycle() {
    run(
        &mut runtime(),
        "template<S set>:\n    have carrier set = S\nhave value \\carrier<\\carrier<R>> = 1\n",
        true,
    );
}

#[test]
fn template_type_interfaces_reject_invalid_indices_lengths_and_false_results() {
    for code in [
        "template<S set>:\n    have pairs set = cart(S,S)\nforall p \\pairs<R>:\n    p(3) $in R\n",
        "template<S set,n N>:\n    have vectors set = finite_seq(S,n)\nhave v \\vectors<R,3> = (1,2)\n",
        "template<S set>:\n    have pairs set = cart(S,S)\ntemplate<S set>:\n    have fn first(p \\pairs<S>) S = p(1)\n\\first<R>((1,2))=2\n",
        "template<S set>:\n    have pairs set = cart(S,S)\nhave p \\pairs<R> = (1,1/0)\n",
    ] { run(&mut runtime(),code,false); }
}

#[test]
fn template_type_interfaces_preserve_additional_surface_carrier_properties() {
    run(&mut runtime(), "template<S set>:\n    have whole set = R\nforall x \\whole<R>:\n    \\whole<R> = {y R: y>=0}\n    =>:\n        x $in \\whole<R>\n        x>=0\n", true);
}
