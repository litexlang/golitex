use crate::exec_env::EqualitySide;
use crate::launch_command::OutputLanguage;
use crate::prelude::*;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn accepted(rt: &mut Runtime, source: &str) {
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none(), "{source}");
}

fn equal(rt: &mut Runtime, source: &str) -> EqualFact {
    let tokens = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("equality: {source}")
    };
    fact
}

#[test]
fn classified_properties_tracer() {
    accepted(&mut runtime(), include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_object_definition/by_fn_application/classified_exact_properties.lit")));
}

#[test]
fn classified_properties_separate_each_used_outer_constructor_and_keep_citations() {
    for (rhs, shape) in [
        ("fn(x R) R {x+1}", EqualToObjShape::AnonymousFn),
        ("fn(x R) R", EqualToObjShape::FnSet),
        ("(1,2)", EqualToObjShape::Tuple),
        ("cart(R,R)", EqualToObjShape::Cart),
        ("{x R: x>0}", EqualToObjShape::SetBuilder),
        ("{1,2}", EqualToObjShape::ListSet),
        ("range(1,3)", EqualToObjShape::Range),
        ("closed_range(1,2)", EqualToObjShape::ClosedRange),
        ("seq(R)", EqualToObjShape::SeqSet),
        ("finite_seq(R,2)", EqualToObjShape::FiniteSeqSet),
        ("power_set(R)", EqualToObjShape::PowerSet),
        ("preimage(step,2)", EqualToObjShape::Preimage),
        ("preimage_set(step,{2})", EqualToObjShape::PreimageSet),
        ("step(2)", EqualToObjShape::FnObj),
        ("\\shift<2>", EqualToObjShape::InstantiatedTemplateObj),
        ("point.x", EqualToObjShape::FieldAccess),
        ("1/2", EqualToObjShape::Other),
    ] {
        let mut rt = runtime();
        accepted(&mut rt, "have fn step(x R) R=x+1\ntemplate<a R>:\n    have fn shift(x R) R=x+a\nstruct Point:\n    x R\n    y R\nhave point &Point=(1,2)");
        accepted(&mut rt, &format!("let alias={rhs}"));
        let comparison = equal(&mut rt, &format!("alias={rhs}"));
        let properties = &rt.top_exec_env().special_properties[&comparison.left.ir()];
        let indices = properties.equalities.indices_for_shapes(&[shape]);
        assert!(!indices.is_empty(), "{rhs}: missing {shape:?} bucket");
        let endpoint = properties.equalities.ordered[indices[0]];
        assert_eq!(endpoint.value_side, EqualitySide::Right);
        let Fact::AtomicFact(AtomicFact::EqualFact(source)) =
            rt.fact_by_id_in_stack(endpoint.fact_id).unwrap()
        else {
            panic!("source")
        };
        assert_eq!(source.left.ir(), comparison.left.ir());
        // Re-parsing allocates fresh binder IDs; compare the RHS by alpha identity.
        let mut rhs_match = comparison.clone();
        rhs_match.left = source.right.clone();
        assert!(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same(&rhs_match).is_some(), "{rhs}: stored RHS differs");
        let reverse = &rt.top_exec_env().special_properties[&source.right.ir()];
        assert!(reverse
            .equalities
            .ordered
            .iter()
            .any(|row| row.fact_id == source.fact_id && row.value_side == EqualitySide::Left));
        let hits = rt.exact_property_object_values_of_shapes(&comparison.left, &[shape]);
        if shape == EqualToObjShape::Other {
            // The identifier itself matches Other and has no equality citation.
            assert!(hits[0].1.is_empty());
            assert_eq!(hits[0].0.ir(), comparison.left.ir());
        }
        let direct: Vec<_> = hits.iter().filter(|(_, path)| !path.is_empty()).collect();
        assert!(!direct.is_empty(), "{rhs}: missing stored candidate");
        assert_eq!(direct[0].1[0].2, source.fact_id);
        assert_eq!(direct[0].0.ir(), source.right.ir());
        for (value, path) in direct {
            assert_eq!(path.len(), 1);
            let Fact::AtomicFact(AtomicFact::EqualFact(cited)) =
                rt.fact_by_id_in_stack(path[0].2).unwrap()
            else {
                panic!("equality source")
            };
            assert!(
                (cited.left.ir() == comparison.left.ir() && cited.right.ir() == value.ir())
                    || (cited.right.ir() == comparison.left.ir() && cited.left.ir() == value.ir())
            );
        }
    }
}

#[test]
fn classified_properties_bucket_union_preserves_insertion_and_scope_order() {
    let mut rt = runtime();
    accepted(&mut rt, "have subject set");
    // Index-only fixtures exercise ordering across different constructors.
    // They are not used as premises for mathematical verification.
    let mut ids = Vec::new();
    for source in ["subject=(1,2)", "subject=fn(x R) R {x}", "subject={1,2}"] {
        let fact = equal(&mut rt, source);
        ids.push(fact.fact_id);
        rt.store_atomic_fact(&AtomicFact::EqualFact(fact)).unwrap();
    }
    let subject = equal(&mut rt, "subject=subject").left;
    let shapes = [
        EqualToObjShape::ListSet,
        EqualToObjShape::AnonymousFn,
        EqualToObjShape::Tuple,
        EqualToObjShape::Tuple,
    ];
    let hits = rt.exact_property_object_values_of_shapes(&subject, &shapes);
    assert_eq!(
        hits.iter().map(|(_, path)| path[0].2).collect::<Vec<_>>(),
        ids
    );
    let ((inner_id, inner_hits), _local_env) = rt
        .run_in_local_env_and_take_env(|rt| {
            let fact = equal(rt, "subject=(3,4)");
            let id = fact.fact_id;
            rt.store_atomic_fact(&AtomicFact::EqualFact(fact))?;
            Ok((
                id,
                rt.exact_property_object_values_of_shapes(&subject, &shapes),
            ))
        })
        .unwrap();
    assert_eq!(inner_hits[0].1[0].2, inner_id);
    assert_eq!(
        inner_hits[1..]
            .iter()
            .map(|(_, path)| path[0].2)
            .collect::<Vec<_>>(),
        ids
    );
    assert_eq!(
        rt.exact_property_object_values_of_shapes(&subject, &shapes),
        hits
    );
}

#[test]
fn classified_properties_do_not_turn_literals_or_alias_chains_into_body_citations() {
    let mut rt = runtime();
    accepted(&mut rt, "have fn step(x R) R=x+1\nlet alias=step");
    let alias = equal(&mut rt, "alias=alias").left;
    assert!(rt.known_equal_to_anonymous_functions(&alias).is_empty());
    let before = rt.top_exec_env().special_properties.clone();
    let run = rt.run_litex_code("alias(2)=3").unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert_eq!(rt.top_exec_env().special_properties, before);
    accepted(&mut rt, "alias=fn(x R) R {x+1}\nalias(2)=3");
    let hits = rt.known_equal_to_anonymous_functions(&alias);
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].1.len(), 1);
    let literal = equal(&mut rt, "fn(x R) R {x}=fn(x R) R {x}").left;
    assert!(rt.known_equal_to_anonymous_functions(&literal).is_empty());
    assert_eq!(
        rt.exact_property_object_values_of_shapes(&literal, &[EqualToObjShape::AnonymousFn])[0]
            .1
            .len(),
        0
    );
}

#[test]
fn classified_properties_literal_to_literal_and_reflexive_sources_are_directional() {
    let mut rt = runtime();
    // Index-only fixtures cover both literal endpoints without proof search.
    let fact = equal(&mut rt, "fn(x R) R {x}=fn(y R) R {y+0}");
    rt.store_atomic_fact(&AtomicFact::EqualFact(fact.clone()))
        .unwrap();
    let right_hits = rt.known_equal_to_anonymous_functions(&fact.right);
    assert_eq!(right_hits.len(), 1);
    assert_eq!(right_hits[0].1[0].2, fact.fact_id);
    assert_eq!(right_hits[0].1[0].1.ir(), fact.left.ir());
    let reflexive = equal(&mut rt, "(1,2)=(1,2)");
    rt.store_atomic_fact(&AtomicFact::EqualFact(reflexive.clone()))
        .unwrap();
    rt.store_atomic_fact(&AtomicFact::EqualFact(reflexive.clone()))
        .unwrap();
    let properties = &rt.top_exec_env().special_properties[&reflexive.left.ir()];
    assert_eq!(properties.equalities.ordered.len(), 1);
    assert_eq!(
        properties.equalities.ordered[0].value_side,
        EqualitySide::Right
    );
    assert!(rt.known_equal_to_tuples(&reflexive.left).is_empty());
}

#[test]
fn classified_properties_failed_compound_statements_discard_all_buckets() {
    let mut rt = runtime();
    accepted(&mut rt, "have fn step(x R) R=x+1");
    let before = rt.top_exec_env().special_properties.clone();
    let run = rt.run_litex_code("claim:\n    ? 0=1\n    let body=fn(x R) R {x}\n    let pair=(1,2)\n    let builder={x R: x>0}\n    let listed={1,2}\n    let interval=range(1,3)").unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert_eq!(rt.top_exec_env().special_properties, before);
    for name in ["body", "pair", "builder", "listed", "interval"] {
        assert!(!rt.plain_atom_is_visible(name));
    }
    accepted(&mut rt, "step(2)=3");
}

#[test]
fn classified_properties_keep_numeric_substitution_separate_and_forall_bodies_local() {
    let mut rt = runtime();
    accepted(&mut rt, "have a R=1/2\na+a=1");
    let a = equal(&mut rt, "a=a").left;
    assert!(!rt.top_exec_env().facts.known_closed_numeric_equal[&a.ir()].is_empty());
    assert!(rt.known_equal_to_anonymous_functions(&a).is_empty());
    let before = rt.top_exec_env().special_properties.clone();
    accepted(&mut rt, "forall f fn(t R: t>0) R, x R:\n    fn(t R: t>0) R {t}=f\n    x>0\n    =>:\n        2*f(x)=2*x");
    assert_eq!(rt.top_exec_env().special_properties, before);
    let run = rt
        .run_litex_code(
            "forall f fn(t R: t>0) R, x R:\n    f=fn(t R: t>0) R {t}\n    =>:\n        2*f(x)=2*x",
        )
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert_eq!(rt.top_exec_env().special_properties, before);
}
