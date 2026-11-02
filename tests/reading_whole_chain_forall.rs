//! A whole-forall chain retains the WD checks that actually ran on its goal.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

trait Field {
    fn field(&self, key: &str) -> &JsonValue;
}
impl Field for JsonValue {
    fn field(&self, key: &str) -> &JsonValue {
        self.as_object()
            .ok()
            .and_then(|fields| fields.get(key))
            .unwrap_or(&JsonValue::Null)
    }
}
fn resolve(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = value.clone();
    while value.field("kind").as_str().ok() == Some("evidence_reference") {
        value = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row.field("id") == value.field("evidence_id"))
            .unwrap()
            .field("node")
            .clone();
    }
    value
}
fn unwrap(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut node = resolve(document, value);
    while node.field("fields").field("0") != &JsonValue::Null {
        node = resolve(document, node.field("fields").field("0"));
    }
    node
}
fn whole_chains(document: &JsonValue) -> Vec<JsonValue> {
    document
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row.field("node"))
        .filter(|node| {
            node.field("type").as_str().ok() == Some("VerifyChainFactSuccess")
                && node.field("fields").field("known_forall") != &JsonValue::Null
        })
        .cloned()
        .collect()
}

#[test]
fn whole_chain_retains_application_then_exact_goal_formation() {
    for source in [
        "forall t R:\n    t=t+0=t\nhave x R=2\nx=x+0=x\n",
        "forall t R:\n    t=t\n    t=t+0=t\nhave x R=2\nx=x+0=x\n",
        "forall t R:\n    t>=0\n    =>:\n        0<=t=t\nhave x R=2\nx>=0\n0<=x=x\n",
        "forall a,b R:\n    a+b=b+a=a+b\nhave x R=1\nhave y R=2\nx+y=y+x=x+y\n",
    ] {
        let built = build_reading(
            &ReadingInput::Source(source.into()),
            true,
            OutputLanguage::English,
        );
        assert!(built.success);
        let document = &built.document;
        let chains = whole_chains(document);
        assert_eq!(chains.len(), 1, "{source}");
        let chain = &chains[0];
        assert!(chain
            .field("fields")
            .field("adjacent")
            .as_array()
            .unwrap()
            .is_empty());
        let retained = resolve(document, chain.field("fields").field("known_forall"));
        assert_eq!(
            retained.field("type").as_str().unwrap(),
            "KnownForallChainProof"
        );
        let application = unwrap(document, retained.field("fields").field("application"));
        assert_eq!(
            application.field("type").as_str().unwrap(),
            "DetailedSearchProofByKnownForallFact"
        );
        let formation = unwrap(
            document,
            retained.field("fields").field("well_defined_proof"),
        );
        assert_eq!(
            formation.field("type").as_str().unwrap(),
            "DetailedChainFactWellDefinedProof"
        );
        let checked = formation
            .field("fields")
            .field("adjacent")
            .as_array()
            .unwrap();
        let goal = resolve(document, chain.field("fields").field("fact"));
        let objects = goal.field("fields").field("objs").as_array().unwrap();
        assert_eq!(checked.len() + 1, objects.len());
        for (index, certificate) in checked.iter().enumerate() {
            let certificate = unwrap(document, certificate);
            let parameters = certificate
                .field("fields")
                .field("well_defined_of_each_parameter")
                .as_array()
                .unwrap();
            assert_eq!(parameters.len(), 2);
            for (offset, parameter) in parameters.iter().enumerate() {
                let object = unwrap(document, parameter);
                assert_eq!(
                    object.field("fields").field("obj"),
                    &objects[index + offset],
                    "WD belongs to this original goal edge"
                );
            }
        }
    }
}

#[test]
fn missing_premise_or_invalid_expression_does_not_gain_whole_chain_success() {
    for source in [
        "forall t R:\n    t>=0\n    =>:\n        0<=t=t\nhave x R=-1\n0<=x=x\n",
        "forall t R:\n    t=t+0=t\n1/0=1/0+0=1/0\n",
    ] {
        let built = build_reading(
            &ReadingInput::Source(source.into()),
            true,
            OutputLanguage::English,
        );
        assert!(!built.success);
        assert!(whole_chains(&built.document).is_empty());
    }
}

#[test]
fn complex_identity_keeps_its_actual_adjacent_fallback() {
    let built = build_reading(
        &ReadingInput::Source("forall t R:\n    t=t+0=t\nhave z C\nz=z+0=z\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(built.success);
    assert!(whole_chains(&built.document).is_empty());
}
