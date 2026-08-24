use super::*;

fn named_obj(name: &str) -> Obj {
    AtomObj::Identifier(Identifier::new(name.to_string())).into()
}

fn equality(left: &str, right: &str) -> EqualFact {
    EqualFact::new(named_obj(left), named_obj(right), default_line_file())
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
