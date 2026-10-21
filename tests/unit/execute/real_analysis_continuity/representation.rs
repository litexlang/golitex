use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::prelude::*;
use crate::tokenize::Tokenizer;
use std::collections::{HashMap, HashSet};
fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn check(rt: &mut Runtime, code: &str, expected: bool) {
    let run = rt.run_litex_code(code).unwrap();
    assert_eq!(run.success, expected, "{code}");
    assert!(run.session_error.is_none(), "{code}");
}
fn atomic(rt: &mut Runtime, source: &str) -> AtomicFact {
    let blocks = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(f)) = rt.parse(&blocks).unwrap().remove(0) else {
        panic!("atomic")
    };
    f
}
fn object(rt: &mut Runtime, source: &str) -> Obj {
    let AtomicFact::EqualFact(f) = atomic(rt, &format!("{source}={source}")) else {
        panic!("object")
    };
    f.left
}
#[test]
fn all_analysis_predicates_preserve_tags_polarity_and_substituted_operands() {
    let mut rt = runtime();
    check(&mut rt, "have a,b seq(R)", true);
    let a = rt.resolve_plain_atom("a").unwrap();
    let b = Obj::Identifier(IdentifierObj::plain(
        rt.resolve_plain_atom("b").unwrap(),
        "b".into(),
    ));
    let map = HashMap::from([(a, b)]);
    let mut sources = vec![
        "$is_real_upper_bound(fn_range(a),1)".to_string(),
        "$is_real_lower_bound(fn_range(a),1)".to_string(),
    ];
    for kind in ["above", "below", ""] {
        sources.push(format!(
            "$is_real_bounded{}(fn_range(a))",
            if kind.is_empty() {
                String::new()
            } else {
                format!("_{kind}")
            }
        ));
    }
    for kind in [
        "nondecreasing",
        "nonincreasing",
        "strictly_increasing",
        "strictly_decreasing",
        "bounded_above",
        "bounded_below",
        "bounded",
        "cauchy",
        "convergent",
    ] {
        sources.push(format!("$is_seq_{kind}(a)"));
    }
    for side in ["at", "left", "right"] {
        sources.push(format!("$is_real_accumulation_{side}(fn_range(a),1)"));
        sources.push(format!("$is_continuous_{side}(a,1)"));
    }
    sources.extend(
        [
            "$is_continuous(a)",
            "$is_uniformly_continuous(a)",
            "$is_lipschitz(a,1)",
        ]
        .map(str::to_string),
    );
    assert_eq!(sources.len(), 23);
    for source in sources {
        let positive = atomic(&mut rt, &source);
        let before = positive.clone();
        let id = rt.global_ids.allocate_fact_id();
        let negative = crate::ast::fact::negate_atomic_fact(&positive, id).unwrap();
        assert_eq!(negative.fact_id(), id);
        assert!(!crate::ast::fact::atomic_fact_has_positive_polarity(
            &negative
        ));
        let id = rt.global_ids.allocate_fact_id();
        let round = crate::ast::fact::negate_atomic_fact(&negative, id).unwrap();
        assert_eq!(
            round.readable_string(),
            positive.readable_string(),
            "{source}"
        );
        for fact in [&positive, &negative] {
            let actual = rt.inst_atomic_fact(fact, &map).unwrap();
            let expected = if crate::ast::fact::atomic_fact_has_positive_polarity(fact) {
                source.replace("(a", "(b")
            } else {
                format!("not {}", source.replace("(a", "(b"))
            };
            let expected = atomic(&mut rt, &expected);
            assert_eq!(
                actual.readable_string(),
                expected.readable_string(),
                "{source}"
            );
        }
        assert_eq!(positive, before, "substitution mutated its input");
    }
}
#[test]
fn bound_object_substitution_does_not_capture_external_set_names() {
    for operator in ["sup", "inf"] {
        let mut rt = runtime();
        check(&mut rt, "have A power_set(R)", true);
        let original = object(
            &mut rt,
            &format!("fn(t power_set(R)) R{{{operator}(A)+{operator}(t)}}"),
        );
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &original else {
            panic!("function")
        };
        let bound = f.body.set_bound_parameters.groups[0].params[0].id;
        let a = rt.resolve_plain_atom("A").unwrap();
        check(&mut rt, "have t power_set(R)", true);
        let external = rt.resolve_plain_atom("t").unwrap();
        assert_ne!(external, bound);
        let replacement = object(&mut rt, &format!("{{z R:z<{operator}(t)}}"));
        let empty = Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] }));
        let actual = rt
            .inst_obj(
                &original,
                &HashMap::from([(a, replacement), (external, empty.clone()), (bound, empty)]),
            )
            .unwrap();
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(&actual, &HashSet::new(), &mut free);
        assert_eq!(free, HashSet::from([external]));
        let expected = object(
            &mut rt,
            &format!("fn(u power_set(R)) R{{{operator}({{z R:z<{operator}(t)}})+{operator}(u)}}"),
        );
        let captured = object(
            &mut rt,
            &format!("fn(u power_set(R)) R{{{operator}({{z R:z<{operator}(u)}})+{operator}(u)}}"),
        );
        let alpha=crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal;
        assert!(alpha(&actual, &expected));
        assert!(!alpha(&actual, &captured));
    }
}
#[test]
fn selected_bounds_and_properties_transport_only_through_proved_equalities() {
    for (operator, cert) in [
        ("sup", "is_real_least_upper_bound"),
        ("inf", "is_real_greatest_lower_bound"),
    ] {
        check(&mut runtime(),&format!("forall A,B power_set(R),L R:\n    A=B\n    ${cert}(A,L)\n    =>:\n        {operator}(A)={operator}(B)"),true);
    }
    for property in [
        "is_continuous_at",
        "is_continuous_left",
        "is_continuous_right",
    ] {
        check(&mut runtime(),&format!("forall f,g fn(x R) R,a,b R:\n    f=g\n    a=b\n    ${property}(f,a)\n    =>:\n        ${property}(g,b)"),true);
    }
    check(&mut runtime(),"forall f fn(x R) R,a R:\n    $is_continuous_left(f,a)\n    =>:\n        $is_continuous_at(f,a)",false);
}
#[test]
fn both_bounds_expose_each_definition_part_without_completeness_search() {
    check(&mut runtime(),"forall a seq(R):\n    $is_seq_bounded(a)\n    =>:\n        $is_seq_bounded_above(a)\n        $is_seq_bounded_below(a)",true);
    check(&mut runtime(),"forall A power_set(R):\n    $is_real_bounded(A)\n    =>:\n        $is_real_bounded_above(A)\n        $is_real_bounded_below(A)",true);
}
