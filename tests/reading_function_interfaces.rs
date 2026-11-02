//! Reading retains the interfaces computed along an actual function call.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value.as_object().unwrap().get(key).unwrap()
}

fn document(source: &str, success: bool) -> JsonValue {
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert_eq!(result.success, success);
    result.document
}

fn resolve<'a>(document: &'a JsonValue, mut value: &'a JsonValue) -> &'a JsonValue {
    while value
        .as_object()
        .ok()
        .and_then(|obj| obj.get("kind"))
        .and_then(|value| value.as_str().ok())
        == Some("evidence_reference")
    {
        let id = field(value, "evidence_id");
        value = field(document, "evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| field(row, "id") == id)
            .map(|row| field(row, "node"))
            .unwrap();
    }
    value
}

#[test]
fn aliased_return_space_retains_each_applied_interface_and_final_carrier() {
    let data = document(include_str!("../examples/proof_nodes/atomic/by_known_special_property/function_return_interface_layers.lit"), true);
    let nodes = field(&data, "evidence_nodes").as_array().unwrap();
    let applied: Vec<_> = nodes
        .iter()
        .map(|row| field(row, "node"))
        .filter(|node| field(node, "type").as_str().ok() == Some("AppliedFnSetReturnSignature"))
        .filter(|node| {
            field(
                resolve(&data, field(field(node, "fields"), "application")),
                "fields",
            )
            .as_object()
            .unwrap()
            .get("body")
            .unwrap()
            .as_array()
            .unwrap()
            .len()
                == 2
        })
        .collect();
    assert!(!applied.is_empty());
    for item in applied {
        let fields = field(item, "fields");
        let layers = field(fields, "layers").as_array().unwrap();
        assert_eq!(layers.len(), 2);
        for (layer, expected) in layers.iter().zip(["t", "x"]) {
            let signature = resolve(&data, layer);
            assert_eq!(field(signature, "type").as_str().ok(), Some("FnSet"));
            let params = resolve(
                &data,
                field(field(signature, "fields"), "set_bound_parameters"),
            );
            let group = resolve(
                &data,
                &field(field(params, "fields"), "groups").as_array().unwrap()[0],
            );
            let parameter = &field(field(group, "fields"), "params").as_array().unwrap()[0];
            assert_eq!(field(parameter, "name").as_str().ok(), Some(expected));
        }
        assert_eq!(
            field(resolve(&data, field(fields, "return_set")), "text")
                .as_str()
                .ok(),
            Some("R")
        );
        assert!(
            fields
                .as_object()
                .unwrap()
                .get("well_defined_proof")
                .is_none(),
            "interface computation is not an independent argument proof"
        );
    }
    for node in nodes.iter().map(|row| field(row, "node")) {
        if matches!(
            field(node, "type").as_str().ok(),
            Some(
                "SignatureStandardReturnProof" | "FnApplicationInCodomainKnownSpecialPropertyProof"
            )
        ) {
            assert_eq!(
                field(
                    resolve(&data, field(field(node, "fields"), "applied")),
                    "type"
                )
                .as_str()
                .ok(),
                Some("AppliedFnSetReturnSignature")
            );
        }
    }
}

#[test]
fn invalid_call_guards_and_nonmatching_complete_domains_still_fail() {
    for source in [
        "have fn property_reader_guard(x R: x != 0) R = 1 / x\nproperty_reader_guard(0) $in C\n",
        "have fn property_reader_apply(g fn(x R: x != 0) R) R = g(1)\nproperty_reader_apply(fn(x R) R {x}) $in R\n",
    ] {
        let data = document(source, false);
        let statements = field(&data, "statements").as_array().unwrap();
        assert_eq!(field(&statements[0], "status").as_str().unwrap(), "accepted");
        let last = statements.last().unwrap();
        assert_eq!(field(last, "status").as_str().unwrap(), "rejected");
        assert_eq!(field(field(last, "failure"), "phase").as_str().unwrap(), "well_defined");
    }
}
