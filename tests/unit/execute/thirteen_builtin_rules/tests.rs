use crate::json_output::{emit_run_detailed, emit_run_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

const TRACERS: &[(&str,&str)] = &[
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/finite_set_product_reindex.lit"),"FiniteSetProductReindex"),
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/finite_set_reduce_reindex.lit"),"FiniteSetReduceReindex"),
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/finite_set_sum_disjoint_union.lit"),"FiniteSetSumDisjointUnion"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/finite_set_sum_triangle.lit"),"FiniteSetSumTriangle"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/finite_index_union.lit"),"FiniteIndexUnion"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/floor_monotone.lit"),"FloorMonotone"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/ceil_monotone.lit"),"CeilMonotone"),
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/euclidean_remainder.lit"),"EuclideanRemainder"),
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/factorial_divisibility.lit"),"FactorialDivisibility"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/complex_triangle.lit"),"ComplexTriangle"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/complex_reverse_triangle.lit"),"ComplexReverseTriangle"),
    (include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/lcm_common_multiple_bound.lit"),"LcmCommonMultipleBound"),
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/range_size.lit"),"RangeSize"),
    (include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/closed_range_size.lit"),"ClosedRangeSize"),
];
const LEG14: &str = "forall A,B finite_set,f fn(x union(A,B))R:\n    intersect(A,B)={}\n    =>:\n        finite_set_sum(union(A,B),f)=finite_set_sum(A,fn(x A)R {f(x)})+finite_set_sum(B,fn(x B)R {f(x)})\n";
const LEG22: &str = "forall S finite_set,f fn(x S)R:\n    abs(finite_set_sum(S,f))<=finite_set_sum(S,fn(x S)R {abs(f(x))})\n";
const LEG32: &str = "forall I nonempty_set,X set,A fn(idx I)power_set(X):\n    $is_finite_set(I)\n    forall k I:\n        $is_finite_set(A(k))\n    =>:\n        $is_finite_set(index_union(I,X,A))\n";
const LEG15: &str =
    "forall x,y R:\n    x<=y\n    =>:\n        floor(x)<=floor(y)\n        ceil(x)<=ceil(y)\n";
const LEG16: &str = "forall a,q Z,m N+,r N:\n    a=m*q+r\n    r<m\n    =>:\n        a%m=r\n";
const LEG18: &str = "forall m,n N:\n    m<=n\n    factorial(m) $in N+\n    factorial(n) $in Z\n    =>:\n        factorial(n)%factorial(m)=0\n";
const LEG19: &str = "forall z,w C:\n    C_abs(z+w)<=C_abs(z)+C_abs(w)\n";
const LEG20: &str = "forall z,w C:\n    abs(C_abs(z)-C_abs(w))<=C_abs(z-w)\n";
const LEG23: &str =
    "forall a,b Z*,m N+:\n    m%abs(a)=0\n    m%abs(b)=0\n    =>:\n        lcm(a,b)<=m\n";
const LEG31: &str = include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/cart_reconstruction.lit");
const CART_DEFINITION: &str = include_str!("../../../../examples/proof_nodes/equal/by_object_definition/cart_function_set_definition.lit");
const LEG33: &str = "forall a,b N:\n    a<=b\n    =>:\n        finite_set_size(range(a,b))=b-a\n";

#[test]
fn run_examples_thirteen_builtin_rules_tracers() {
    // The original Cartesian capability remains tested on its new definition
    // route; it is no longer a constructor-shape builtin leaf.
    assert_eq!(TRACERS.len() + 1, 15);
    for (code, rule) in TRACERS {
        let json = check(code, true);
        assert!(
            find_rule(&json, rule).is_some(),
            "actual winning {rule}: {}",
            json.stringify_pretty()
        );
    }
    let reconstruction=check(LEG31,true);
    assert!(reconstruction.stringify().contains("cart_function_set_definition"));
    check(CART_DEFINITION,true);
}

#[test]
fn finite_partition_restrictions_and_nearby_failures() {
    for code in [
        LEG14
            .replace("finite_set_sum", "finite_set_product")
            .replace("})+finite_set_product", "})*finite_set_product"),
        LEG14
            .replace("finite_set_sum(union(A,B),f)=", "")
            .trim()
            .to_string()
            + "=finite_set_sum(union(A,B),f)",
        LEG14
            .replace("fn(x A)R {f(x)}", "fn(t A)R {f(t)}")
            .replace("fn(x B)R {f(x)}", "fn(u B)R {f(u)}"),
    ] {
        check(&code, true);
    }
    for code in [
        LEG14.replace("    intersect(A,B)={}\n    =>:\n", ""),
        LEG14
            .replace("f fn(x union(A,B))R", "f,h fn(x union(A,B))R")
            .replace("fn(x A)R {f(x)}", "fn(x A)R {h(x)}"),
        LEG14.replace("fn(x A)R {f(x)}", "fn(x A)R {f(x)+1}"),
        LEG14.replace("fn(x B)R {f(x)}", "fn(x B)R {f(x)+1}"),
        LEG14.replace("fn(x A)R {f(x)}", "fn(x B)R {f(x)}"),
        LEG14.replace("A,B finite_set", "A,B nonempty_set"),
    ] {
        check(&code, false);
    }
    for (code, rule) in [
        (LEG14.to_string(), "FiniteSetSumDisjointUnion"),
        (
            LEG14
                .replace("finite_set_sum", "finite_set_product")
                .replace("})+finite_set_product", "})*finite_set_product"),
            "FiniteSetProductDisjointUnion",
        ),
    ] {
        let json = check(&code, true);
        let JsonValue::Object(fields) = find_rule(&json, rule).unwrap() else {
            panic!("object")
        };
        let JsonValue::Array(callbacks) = fields.get("callbacks").unwrap() else {
            panic!("array")
        };
        assert_eq!(callbacks.len(), 2);
        assert!(callbacks
            .iter()
            .all(|p| p.stringify_pretty().contains("literal_restriction")));
        let premises = fields.get("premises").unwrap().stringify_pretty();
        assert!(
            premises.contains("intersect(A, B)") && premises.contains("cite_fact_id"),
            "{premises}"
        );
    }
}

#[test]
fn finite_triangle_exact_summands_and_bound_binders() {
    check(
        &LEG22.replace("fn(x S)R {abs(f(x))}", "fn(index S)R {abs(f(index))}"),
        true,
    );
    for code in [
        LEG22
            .replace("f fn(x S)R", "f,h fn(x S)R")
            .replace("{abs(f(x))}", "{abs(h(x))}"),
        LEG22
            .replace("f fn(x S)R", "c S,f fn(x S)R")
            .replace("{abs(f(x))}", "{abs(f(c))}"),
        LEG22.replace("{abs(f(x))}", "{f(x)}"),
        LEG22
            .replace("S finite_set", "S,T finite_set")
            .replace("finite_set_sum(S,fn(x S)", "finite_set_sum(T,fn(x T)"),
        LEG22.replace("S finite_set", "S nonempty_set"),
        LEG22
            .replace("f fn(x S)R", "f fn(x S)C")
            .replace("fn(x S)R {abs(f(x))}", "fn(x S)R {C_abs(f(x))}"),
    ] {
        check(&code, false);
    }
}

#[test]
fn indexed_union_consumes_exact_universal_source() {
    let json = check(
        &LEG32
            .replace("forall k I:", "forall item I:")
            .replace("A(k)", "A(item)"),
        true,
    );
    let JsonValue::Object(fields) = find_rule(&json, "FiniteIndexUnion").unwrap() else {
        panic!("object")
    };
    let JsonValue::Object(fibres) = fields.get("fibres").unwrap() else {
        panic!("certificate")
    };
    assert!(fibres
        .get("fact")
        .unwrap()
        .as_str()
        .unwrap()
        .contains("$is_finite_set(A("));
    assert!(!fibres
        .get("cite_fact_id")
        .unwrap()
        .as_str()
        .unwrap()
        .is_empty());
    let JsonValue::Array(renamings) = fibres.get("parameter_renamings").unwrap() else {
        panic!("renamings")
    };
    assert_eq!(renamings.len(), 1);
    let JsonValue::Object(pair) = &renamings[0] else {
        panic!("pair")
    };
    assert_ne!(pair.get("source"), pair.get("target"));
    assert!(fields
        .get("index_finite")
        .unwrap()
        .stringify_pretty()
        .contains("cite_fact_id"));
    for code in [
        LEG32.replace("    $is_finite_set(I)\n", ""),
        LEG32.replace("    forall k I:\n        $is_finite_set(A(k))\n", ""),
        LEG32
            .replace("A fn(idx I)", "A,B fn(idx I)")
            .replace("$is_finite_set(A(k))", "$is_finite_set(B(k))"),
        LEG32
            .replace(
                "A fn(idx I)power_set(X)",
                "p fn(idx I)R,A fn(idx I)power_set(X)",
            )
            .replace(
                "    forall k I:\n        $is_finite_set(A(k))",
                "    forall k I:\n        p(k)=0\n        =>:\n            $is_finite_set(A(k))",
            ),
    ] {
        check(&code, false);
    }
}

#[test]
fn previous_eight_families_boundaries() {
    for code in [
        LEG15.replace("    x<=y\n    =>:\n", ""),
        LEG15.replace("floor(x)<=floor(y)", "floor(x)<=floor(y)-1"),
        LEG15.replace("ceil(x)<=ceil(y)", "ceil(x)<=ceil(y)-1"),
        LEG16.replace("    a=m*q+r\n", ""),
        LEG16.replace("r<m", "r<=m"),
        LEG16.replace("a%m=r", "a%m=r+1"),
        LEG18.replace("    m<=n\n", ""),
        LEG18.replace("factorial(n)%factorial(m)=0", "factorial(n)%factorial(m)=1"),
        LEG19.replace("C_abs(z)+C_abs(w)", "C_abs(z)-C_abs(w)"),
        LEG19
            .replace("z,w C", "z,w,h C")
            .replace("C_abs(z+w)", "C_abs(z+w+h)"),
        LEG20.replace("C_abs(z-w)", "C_abs(z+w)"),
        LEG23.replace("    m%abs(a)=0\n", ""),
        LEG23.replace("    m%abs(b)=0\n", ""),
        LEG23.replace("lcm(a,b)<=m", "lcm(a,b)<m"),
        LEG31.replace("p(1) $in A, ", ""),
        LEG31.replace(", p(2) $in B", ""),
        LEG31.replace("K=cart(A,B)", "K=cart(A,A)"),
        LEG33.replace("    a<=b\n    =>:\n", ""),
        LEG33.replace("=b-a", "=b-a+1"),
        LEG33.replace("range(a,b)", "closed_range(a,b)"),
        LEG33.replace("a,b N", "a,b R"),
    ] {
        check(&code, false);
    }
    check(
        &LEG33.replace(
            "finite_set_size(range(a,b))=b-a",
            "b-a=finite_set_size(range(a,b))",
        ),
        true,
    );
    check(&LEG16.replace("a%m=r", "r=a%m"), true);
    check(&LEG31.replace("K=cart(A,B)", "cart(A,B)=K"), true);
}

#[test]
fn failed_rules_do_not_publish_assumptions() {
    let mut rt = runtime(OutputLanguage::English);
    let missing = LEG32.replace("    $is_finite_set(I)\n", "");
    assert!(!rt.run_litex_code(&missing).unwrap().success);
    assert!(rt.run_litex_code(LEG32).unwrap().success);
    assert!(!rt.run_litex_code(&missing).unwrap().success);
    assert!(
        !rt.run_litex_code(&LEG14.replace("    intersect(A,B)={}\n    =>:\n", ""))
            .unwrap()
            .success
    );
    let missing_coordinate=LEG31.replace(", p(2) $in B", "");
    assert!(!rt.run_litex_code(&missing_coordinate).unwrap().success);
    assert!(rt.run_litex_code(LEG31).unwrap().success);
    assert!(!rt.run_litex_code(&missing_coordinate).unwrap().success);
    assert!(rt.run_litex_code(LEG14).unwrap().success);
    assert!(
        !rt.run_litex_code(&LEG14.replace("    intersect(A,B)={}\n    =>:\n", ""))
            .unwrap()
            .success
    );
}

#[test]
fn all_leafs_permission_language_and_scope_consumers() {
    use crate::ast::fact::{AtomicFact, ExistOrAndChainAtomicFact, Fact};
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::{
        AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof,
    };
    use crate::execute::execute_fact_stmt::{
        VerifyFactWellDefinedResult, VerifyState, VerifyStateLevel,
    };
    use crate::tokenize::Tokenizer;
    let pointwise = "forall A,B finite_set:\n    intersect(A,B)={}\n    =>:\n        finite_set_sum(union(A,B),fn(x union(A,B))R {0})=finite_set_sum(A,fn(x A)R {0})+finite_set_sum(B,fn(x B)R {0})";
    for (code, _) in TRACERS
        .iter()
        .copied()
        .chain([(pointwise, "FiniteSetSumDisjointUnion")])
    {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::ForallFact(conditional)) = &statements[0] else {
            panic!("forall")
        };
        let (_,local_env)=rt.run_in_local_env_and_take_env(|rt| {
            assert!(rt.introduce_typed_parameters(&conditional.typed_parameters,VerifyState::top_level())?.is_ok());
            for premise in &conditional.dom_facts {
                assert!(matches!(rt.verify_fact_well_definedness(premise,VerifyState::top_level())?,VerifyFactWellDefinedResult::Success(_)));
                rt.store_fact_and_infer(premise,VerifyState::top_level())?;
            }
            let ExistOrAndChainAtomicFact::AtomicFact(goal)=&conditional.then_facts[0] else {panic!("atomic")};
            match goal {
                AtomicFact::EqualFact(equal) => assert!(!rt.verify_equal_fact_well_definedness(equal,VerifyState::top_level())?.is_failed()),
                _ => assert!(!rt.verify_atomic_fact_well_definedness(goal,VerifyState::top_level())?.is_failed()),
            }
            let before=rt.execution_environments_stack.iter().map(|e|(e.facts.facts_by_id.len(),e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
            let mut texts=Vec::new();
            match goal {
                AtomicFact::EqualFact(equal) => {
                    assert!(rt.search_equal_fact_proof(equal,VerifyState::new(VerifyStateLevel::KnownSpecialProperty))?.is_none(),"{code}");
                    let Some(EqualFactSearchedProof::ByBuiltinRule(rule))=rt.search_equal_fact_proof(equal,VerifyState::new(VerifyStateLevel::BuiltinRule))? else {panic!("builtin: {code}")};
                    for lang in languages() {texts.push(rule.rule_name_and_message(lang));}
                    // Scoped pointwise branch retains its closed local evidence.
                    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::{EqualitySearchProofByBuiltinRule as E,aggregate_identity_builtin_rule_proof as A};
                    if let E::AggregateIdentity(A::AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(p))=rule {
                        assert_eq!(p.callbacks.len(),2);
                        if code==pointwise {
                            for callback in &p.callbacks {
                                let A::FinitePartitionCallbackAgreementProof::Pointwise(proof)=callback else {panic!("pointwise evidence")};
                                assert!(!proof.local_env.facts.facts_by_id.is_empty());
                                assert_eq!(proof.function_expansions.len(),2);
                                assert!(!proof.equality.is_failed());
                            }
                        }
                    }
                }
                _ => {
                    assert!(rt.search_atomic_except_equality_fact_proof(goal,VerifyState::new(VerifyStateLevel::KnownSpecialProperty))?.is_none(),"{code}");
                    let Some(AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule))=rt.search_atomic_except_equality_fact_proof(goal,VerifyState::new(VerifyStateLevel::BuiltinRule))? else {panic!("builtin: {code}")};
                    for lang in languages() {texts.push(rule.rule_name_and_message(lang));}
                }
            }
            assert_eq!(texts.len(),10);
            for text in &texts {assert!(!text.rule_name.is_empty() && !text.message.is_empty());}
            for text in &texts[1..] {assert_ne!(text.rule_name,texts[0].rule_name);assert_ne!(text.message,texts[0].message);}
            let after=rt.execution_environments_stack.iter().map(|e|(e.facts.facts_by_id.len(),e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
            assert_eq!(before,after,"read-only: {code}");
            Ok(())
        }).unwrap();
        assert_eq!(rt.execution_environments_stack.len(), 1);
        drop(local_env);
    }
}

#[test]
fn cart_definition_obeys_definition_permissions_and_preserves_scope() {
    use crate::ast::fact::{AtomicFact, ExistOrAndChainAtomicFact, Fact};
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByObjectDefinition;
    use crate::execute::execute_fact_stmt::{VerifyState,VerifyStateLevel};
    use crate::tokenize::Tokenizer;
    let mut rt=runtime(OutputLanguage::English);
    let tokens=Tokenizer::new().tokenize(CART_DEFINITION,rt.current_file.clone()).unwrap();
    let statements=rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::ForallFact(definition))=&statements[0] else {panic!("forall")};
    let (_,local_env)=rt.run_in_local_env_and_take_env(|rt| {
        assert!(rt.introduce_typed_parameters(&definition.typed_parameters,VerifyState::top_level())?.is_ok());
        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal))=&definition.then_facts[0] else {panic!("equality")};
        assert!(!rt.verify_equal_fact_well_definedness(equal,VerifyState::top_level())?.is_failed());
        let before=rt.execution_environments_stack.iter().map(|env| (env.facts.facts_by_id.len(),env.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
        for level in [VerifyStateLevel::Direct,VerifyStateLevel::KnownSpecialProperty,VerifyStateLevel::BuiltinRule,VerifyStateLevel::Strategy] {
            assert!(rt.search_equal_fact_proof(equal,VerifyState::new(level))?.is_none(),"definition bypassed {level:?}");
        }
        let Some(EqualFactSearchedProof::ByObjectDefinition(EqualitySearchProofByObjectDefinition::CartesianDefinition(_)))=
            rt.search_equal_fact_proof(equal,VerifyState::new(VerifyStateLevel::DefinitionAndForall))?
            else {panic!("complete Cartesian definition proof")};
        let after=rt.execution_environments_stack.iter().map(|env| (env.facts.facts_by_id.len(),env.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
        assert_eq!(before,after,"definition search published facts or WD cache");
        Ok(())
    }).unwrap();
    assert_eq!(rt.execution_environments_stack.len(),1);
    drop(local_env);
}

#[test]
fn normal_and_detailed_producer_consumers() {
    for lang in languages() {
        for source in TRACERS.iter().map(|(source,_)| *source).chain([LEG31,CART_DEFINITION]) {
            let mut rt = runtime(lang);
            let run = rt.run_litex_code(source).unwrap();
            assert!(run.success, "{source}");
            JsonValue::parse(&emit_run_normal(&run, &rt, "eval", None)).unwrap();
            JsonValue::parse(&emit_run_detailed(&run, &rt, "eval", None)).unwrap();
        }
    }
}

fn languages() -> [OutputLanguage; 10] {
    [
        OutputLanguage::English,
        OutputLanguage::Chinese,
        OutputLanguage::ChineseTraditional,
        OutputLanguage::French,
        OutputLanguage::Russian,
        OutputLanguage::Spanish,
        OutputLanguage::Arabic,
        OutputLanguage::Japanese,
        OutputLanguage::Korean,
        OutputLanguage::Vietnamese,
    ]
}
fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
fn check(code: &str, expected: bool) -> JsonValue {
    let mut rt = runtime(OutputLanguage::English);
    let run = rt.run_litex_code(code).unwrap();
    let output = emit_run_detailed(&run, &rt, "eval", None);
    assert_eq!(run.success, expected, "{code}\n{output}");
    assert!(run.session_error.is_none(),"unexpected parse/session error: {code}\n{output}");
    assert!(!run.statement_results.is_empty(),"empty capability check: {code}");
    JsonValue::parse(&output).unwrap()
}
fn find_rule(value: &JsonValue, rule: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields.get("rule").and_then(|v| v.as_str().ok()) == Some(rule) {
                return Some(value.clone());
            }
            for (_, v) in fields.iter() {
                if let Some(r) = find_rule(v, rule) {
                    return Some(r);
                }
            }
        }
        JsonValue::Array(values) => {
            for v in values {
                if let Some(r) = find_rule(v, rule) {
                    return Some(r);
                }
            }
        }
        _ => {}
    }
    None
}
