use super::*;

fn named_obj(name: &str) -> Obj {
    AtomObj::Identifier(Identifier::new(name.to_string())).into()
}

fn equality(left: &str, right: &str) -> EqualFact {
    EqualFact::new(named_obj(left), named_obj(right), default_line_file())
}

fn selected_real_template_instance() -> (Obj, Obj) {
    let surface_name = "\\selected<R>".to_string();
    let surface_identifier: Obj = Identifier::new(surface_name).into();
    let instantiated_template: Obj = InstantiatedTemplateObj::new(
        AtomicName::WithoutMod("selected".to_string()),
        vec![StandardSet::R.into()],
    )
    .into();
    assert_eq!(
        obj_equality_key(&surface_identifier),
        obj_equality_key(&instantiated_template),
        "the regression requires two Rust representations of one semantic object",
    );
    (surface_identifier, instantiated_template)
}

#[test]
fn equality_classes_merge_and_enumerate_from_any_member() {
    let mut known = KnownEquality::new();
    known.store(&equality("x0", "x1"));
    known.store(&equality("x2", "x3"));
    known.store(&equality("x1", "x2"));

    for key in ["x0", "x1", "x2", "x3"] {
        let (_, members) = known.get(key).expect("member must have an equality class");
        let mut member_keys = members.iter().map(obj_equality_key).collect::<Vec<_>>();
        member_keys.sort();
        assert_eq!(member_keys, vec!["x0", "x1", "x2", "x3"]);
    }
}

#[test]
fn equality_class_id_is_shared_by_every_member() {
    let mut known = KnownEquality::new();
    known.store(&equality("x0", "x1"));
    known.store(&equality("x2", "x3"));

    let left_class = known.get_with_class_id("x0").unwrap().0;
    let right_class = known.get_with_class_id("x2").unwrap().0;
    assert_ne!(left_class, right_class);

    known.store(&equality("x1", "x2"));
    let merged_class = known.get_with_class_id("x0").unwrap().0;
    for key in ["x1", "x2", "x3"] {
        assert_eq!(known.get_with_class_id(key).unwrap().0, merged_class);
    }
}

#[test]
fn equality_clone_is_an_independent_transaction_snapshot() {
    let mut original = KnownEquality::new();
    original.store(&equality("x0", "x1"));

    let mut snapshot = original.clone();
    snapshot.store(&equality("x1", "x2"));

    assert!(original.get("x2").is_none());
    assert_eq!(original.get("x0").unwrap().1.len(), 2);
    assert_eq!(snapshot.get("x0").unwrap().1.len(), 3);
}

#[test]
fn redundant_equality_keeps_the_existing_direct_proof_forest() {
    let mut known = KnownEquality::new();
    known.store(&equality("x0", "x1"));
    known.store(&equality("x1", "x2"));
    let proof_count_before = known
        .values()
        .map(|(proofs, _)| proofs.len())
        .sum::<usize>();

    known.store(&equality("x0", "x2"));

    let proof_count_after = known
        .values()
        .map(|(proofs, _)| proofs.len())
        .sum::<usize>();
    assert_eq!(proof_count_after, proof_count_before);
}

#[test]
fn direct_equalities_are_unique_and_deterministically_ordered() {
    let mut known = KnownEquality::new();
    known.store(&equality("x2", "x3"));
    known.store(&equality("x0", "x1"));
    known.store(&equality("x1", "x2"));

    let edges = known
        .direct_equalities()
        .iter()
        .map(|equality| {
            let left = obj_equality_key(&equality.left);
            let right = obj_equality_key(&equality.right);
            if left <= right {
                (left, right)
            } else {
                (right, left)
            }
        })
        .collect::<Vec<_>>();

    assert_eq!(
        edges,
        vec![
            ("x0".to_string(), "x1".to_string()),
            ("x1".to_string(), "x2".to_string()),
            ("x2".to_string(), "x3".to_string()),
        ]
    );
}

#[test]
fn equality_proof_path_preserves_edge_order_and_orientation() {
    let mut known = KnownEquality::new();
    known.store(&equality("x0", "x1"));
    known.store(&equality("x1", "x2"));

    let forward = known
        .proof_path(&named_obj("x0"), &named_obj("x2"))
        .expect("forward path");
    assert_eq!(forward.len(), 2);
    assert_eq!(forward[0].from.to_string(), "x0");
    assert_eq!(forward[0].to.to_string(), "x1");
    assert_eq!(forward[1].from.to_string(), "x1");
    assert_eq!(forward[1].to.to_string(), "x2");

    let backward = known
        .proof_path(&named_obj("x2"), &named_obj("x0"))
        .expect("backward path");
    assert_eq!(backward.len(), 2);
    assert_eq!(backward[0].from.to_string(), "x2");
    assert_eq!(backward[0].to.to_string(), "x1");
    assert_eq!(backward[1].from.to_string(), "x1");
    assert_eq!(backward[1].to.to_string(), "x0");
}

#[test]
fn equality_proof_path_carries_exact_fact_ids() {
    let mut known = KnownEquality::new();
    let first = equality("x0", "x1");
    let second = equality("x1", "x2");
    let first_id = first.fact_id;
    let second_id = second.fact_id;
    known.store(&first);
    known.store(&second);

    let path = known
        .proof_path(&named_obj("x0"), &named_obj("x2"))
        .expect("proof path");
    assert_eq!(
        path.iter().map(|step| step.fact_id).collect::<Vec<_>>(),
        vec![first_id, second_id]
    );
}

#[test]
fn equality_history_records_class_growth_and_redundant_edges() {
    let mut known = KnownEquality::new();
    let first = equality("x0", "x1");
    let second = equality("x1", "x2");
    let redundant = equality("x0", "x2");
    let first_id = first.fact_id;
    let second_id = second.fact_id;
    let redundant_id = redundant.fact_id;

    known.store(&first);
    known.store(&second);
    known.store(&redundant);

    assert_eq!(known.history().len(), 3);
    assert!(matches!(
        known.history()[0],
        EqualityHistoryEvent::ClassesMerged { via_fact_id, .. } if via_fact_id == first_id
    ));
    assert!(matches!(
        known.history()[1],
        EqualityHistoryEvent::ClassesMerged { via_fact_id, .. } if via_fact_id == second_id
    ));
    assert!(matches!(
        known.history()[2],
        EqualityHistoryEvent::EdgeAddedInsideExistingClass { fact_id, .. } if fact_id == redundant_id
    ));
}

#[test]
fn later_equality_endpoint_upgrades_a_surface_identifier_to_its_template_instance() {
    let mut known = KnownEquality::new();
    let (surface_identifier, instantiated_template) = selected_real_template_instance();
    let ambient = named_obj("Ambient");
    let template_key = obj_equality_key(&instantiated_template);

    known.store(&EqualFact::new(
        surface_identifier,
        ambient.clone(),
        default_line_file(),
    ));
    assert!(known
        .get(&obj_equality_key(&ambient))
        .expect("Ambient equality class")
        .1
        .iter()
        .all(|member| !matches!(member, Obj::InstantiatedTemplateObj(_))));

    // This equality is redundant at the semantic-key level, but it is the
    // first time the equality store sees the concrete template-instance
    // representation. The class must retain that richer representation.
    known.store(&EqualFact::new(
        instantiated_template,
        ambient.clone(),
        default_line_file(),
    ));

    let (_, members) = known
        .get(&obj_equality_key(&ambient))
        .expect("Ambient equality class remains available");
    assert_eq!(
        members
            .iter()
            .filter(|member| matches!(member, Obj::InstantiatedTemplateObj(_)))
            .count(),
        1,
        "the semantic key should deterministically retain one concrete template instance",
    );
    let template_key_members = members
        .iter()
        .filter(|member| obj_equality_key(member) == template_key)
        .collect::<Vec<_>>();
    assert_eq!(template_key_members.len(), 1);
    assert!(matches!(
        template_key_members[0],
        Obj::InstantiatedTemplateObj(_)
    ));
}
