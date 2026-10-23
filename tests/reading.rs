use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, parse_reading_command, ReadingAction, ReadingInput};
use std::collections::BTreeSet;

#[test]
fn fact_level_hypotheses_and_conclusions_keep_different_evidence_roles() {
    let result = build_reading(
        &ReadingInput::Source("forall x R:\n    x = 2\n    =>:\n        x + 1 = 3\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let facts = result.document.field("facts").as_array().unwrap();
    let hypothesis = facts
        .iter()
        .find(|fact| {
            fact.field("text").as_str().unwrap() == "x = 2"
                && fact.as_object().unwrap().get("role").is_some()
        })
        .unwrap();
    let conclusion = facts
        .iter()
        .find(|fact| {
            fact.field("text").as_str().unwrap() == "(x + 1) = 3"
                && fact.as_object().unwrap().get("role").is_some()
        })
        .unwrap();
    assert_eq!(hypothesis.field("role").as_str().unwrap(), "hypothesis");
    assert_eq!(hypothesis.field("line").as_u64().unwrap(), 2);
    assert_eq!(conclusion.field("role").as_str().unwrap(), "verified");
    assert_eq!(conclusion.field("line").as_u64().unwrap(), 4);
    assert!(matches!(
        hypothesis.field("is_primary"),
        JsonValue::Bool(true)
    ));
    let evidence = reachable_evidence(&result.document, conclusion.field("evidence"));
    assert!(evidence.contains(hypothesis.field("id").as_str().unwrap()));
    let outer = &result.document.field("statements").as_array().unwrap()[0];
    assert!(
        !ids(outer.field("produced_fact_ids")).contains(hypothesis.field("id").as_str().unwrap())
    );
    assert!(
        !ids(outer.field("produced_fact_ids")).contains(conclusion.field("id").as_str().unwrap())
    );
}

#[test]
fn cached_wd_references_resolve_to_actual_scoped_registrations() {
    let result = build_reading(
        &ReadingInput::Source("have x R\n0 <= x ^ 2\n1 <= x ^ 2 + 1\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let records = result
        .document
        .field("well_definedness")
        .as_array()
        .unwrap();
    let statements = result.document.field("statements").as_array().unwrap();
    let square = records
        .iter()
        .find(|record| record.field("object").as_str().unwrap().contains("x ^ 2"))
        .unwrap();
    assert_eq!(
        square.field("producer_statement_id"),
        statements[1].field("id")
    );
    assert!(ids(statements[2].field("well_definedness_ids"))
        .contains(square.field("id").as_str().unwrap()));
    assert!(square.as_object().unwrap().get("evidence").is_some());
    for statement in statements {
        assert_eq!(
            statement
                .field("coverage")
                .field("well_definedness")
                .as_str()
                .unwrap(),
            "complete"
        );
        for id in ids(statement.field("well_definedness_ids")) {
            let record = records
                .iter()
                .find(|record| record.field("id").as_str().unwrap() == id)
                .unwrap();
            assert!(statements
                .iter()
                .any(|statement| statement.field("id") == record.field("producer_statement_id")));
            assert!(!record.field("scope_id").as_str().unwrap().is_empty());
        }
    }
}

#[test]
fn temporary_calculation_subject_ids_are_not_dangling_citations() {
    // Unchanged proof from Mechanics Chapter 1: internal EqualFact subjects
    // can be temporary even though every real stored-fact citation resolves.
    let result = build_reading(
        &ReadingInput::Source("forall x R:\n    x = 2\n    =>:\n        x + 1 = 3\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let facts = result
        .document
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .map(|fact| fact.field("id").as_str().unwrap())
        .collect::<BTreeSet<_>>();
    let mut pending = vec![result.document.field("evidence_nodes")];
    let mut temporary = 0;
    while let Some(value) = pending.pop() {
        match value {
            JsonValue::Array(values) => pending.extend(values),
            JsonValue::Object(fields) => {
                match fields.get("kind").and_then(|value| value.as_str().ok()) {
                    Some("fact_reference") => {
                        assert!(facts.contains(value.field("fact_id").as_str().unwrap()))
                    }
                    Some("fact_identity")
                        if !facts.contains(value.field("fact_id").as_str().unwrap()) =>
                    {
                        temporary += 1
                    }
                    _ => {}
                }
                pending.extend(fields.iter().map(|(_, value)| value));
            }
            _ => {}
        }
    }
    assert!(
        temporary > 0,
        "the real calculation must exercise an unstored subject"
    );
}

#[test]
fn inferred_conclusions_keep_their_seed_evidence_and_later_citation() {
    let result = build_reading(
        &ReadingInput::Source(include_str!("../examples/reading/inferred_facts.lit").into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let statements = result.document.field("statements").as_array().unwrap();
    let meaning = statements[1].field("mathematics");
    assert_eq!(
        meaning.field("kind").as_str().unwrap(),
        "predicate_definition"
    );
    assert_eq!(
        meaning.field("subject").as_str().unwrap(),
        "$reading_outer(ro)"
    );
    assert_eq!(
        meaning.field("parameters").as_array().unwrap()[0]
            .field("domain")
            .as_str()
            .unwrap(),
        "R"
    );
    assert_eq!(
        meaning.field("facts").as_array().unwrap()[0]
            .as_str()
            .unwrap(),
        "$reading_inner(ro)"
    );
    assert_eq!(
        statements
            .iter()
            .map(|statement| statement.field("statement_kind").as_str().unwrap())
            .collect::<Vec<_>>(),
        [
            "Definition.DefPropStmt",
            "Definition.DefPropStmt",
            "Definition.DefineObj.HaveObjInNonemptySetStmt",
            "By.ByDefStmt",
            "Fact",
        ],
        "syntax identity is independent of stored fact roles and inference origins"
    );
    for definition in &statements[..2] {
        assert!(
            ids(definition.field("inferred_fact_ids")).is_empty(),
            "prop checking internals are not outputs of the declaration"
        );
    }
    for statement in statements {
        assert!(
            ids(statement.field("inferred_fact_ids"))
                .is_subset(&ids(statement.field("produced_fact_ids"))),
            "only actual published inference outputs belong under a statement"
        );
    }
    let inferred = ids(statements[3].field("inferred_fact_ids"));
    let citations = ids(statements[4].field("cited_fact_ids"));
    let id = inferred
        .intersection(&citations)
        .next()
        .expect("later statement cites the actual inferred fact");
    let facts = result.document.field("facts").as_array().unwrap();
    assert!(
        facts
            .iter()
            .any(|fact| fact.field("text").as_str().unwrap() == "ro $in R"),
        "internal verification evidence is retained, not deleted to hide the row"
    );
    assert!(
        facts
            .iter()
            .any(|fact| inferred.contains(fact.field("id").as_str().unwrap())
                && fact.field("text").as_str().unwrap() == "reading_value $in R"),
        "real membership inference is preserved; filtering is by ownership, not text"
    );
    let fact = facts
        .iter()
        .find(|fact| fact.field("id").as_str().unwrap() == id)
        .unwrap();
    assert_eq!(
        fact.field("text").as_str().unwrap(),
        "$reading_inner(reading_value)"
    );
    assert_eq!(
        fact.field("producer_statement_id"),
        statements[3].field("id")
    );
    let inferences = result.document.field("inferences").as_array().unwrap();
    let inference = inferences
        .iter()
        .find(|inference| ids(inference.field("fact_ids")).contains(id))
        .unwrap();
    assert_eq!(
        inference.field("producer_statement_id"),
        statements[3].field("id")
    );
    assert!(ids(fact.field("inference_ids")).contains(inference.field("id").as_str().unwrap()));
    let seed = facts
        .iter()
        .find(|fact| fact.field("id") == inference.field("source_fact_id"))
        .unwrap();
    assert_eq!(
        seed.field("text").as_str().unwrap(),
        "$reading_outer(reading_value)"
    );
    assert_eq!(inference.field("scope_id"), seed.field("scope_id"));
    let origins = inference.field("conclusion_origins").as_array().unwrap();
    let expansion = origins
        .iter()
        .find(|origin| origin.field("fact_id").as_str().unwrap() == id)
        .unwrap();
    assert_eq!(expansion.field("kind").as_str().unwrap(), "definition");
    assert_eq!(
        expansion.field("definition_statement_id"),
        statements[1].field("id")
    );
    let definition_symbol = result
        .document
        .field("symbols")
        .as_array()
        .unwrap()
        .iter()
        .find(|symbol| symbol.field("id") == expansion.field("source_symbol_id"))
        .unwrap();
    assert_eq!(
        definition_symbol.field("name").as_str().unwrap(),
        "reading_outer"
    );
    assert_eq!(
        definition_symbol.field("definition_statement_id"),
        statements[1].field("id")
    );
    assert!(expansion
        .field("rule_id")
        .as_str()
        .unwrap()
        .ends_with("::ExpandDefinition"));
    let membership = origins
        .iter()
        .find(|origin| {
            facts.iter().any(|fact| {
                fact.field("id") == origin.field("fact_id")
                    && fact.field("text").as_str().unwrap() == "reading_value $in R"
            })
        })
        .unwrap();
    assert_eq!(
        membership.field("kind").as_str().unwrap(),
        "parameter_type",
        "do not attribute the whole inference batch to definition expansion"
    );
    assert!(membership
        .field("rule_id")
        .as_str()
        .unwrap()
        .ends_with("::ParamTypes"));
    assert_eq!(
        membership.field("definition_statement_id"),
        statements[1].field("id")
    );
    assert!(
        reachable_evidence(&result.document, inference.field("evidence"))
            .contains("ExpandDefinition")
    );
    assert!(ids(inference.field("rule_ids"))
        .iter()
        .any(|id| id.contains("ExpandDefinition")));
    assert!(
        !ids(statements[4].field("inferred_fact_ids")).contains(id),
        "rechecking is not the original inference producer"
    );
    for inference in inferences {
        assert!(facts
            .iter()
            .any(|fact| fact.field("id") == inference.field("source_fact_id")));
        assert!(statements
            .iter()
            .any(|stmt| stmt.field("id") == inference.field("producer_statement_id")));
        for id in ids(inference.field("fact_ids")) {
            let fact = facts
                .iter()
                .find(|fact| fact.field("id").as_str().unwrap() == id)
                .unwrap();
            assert!(
                ids(fact.field("inference_ids")).contains(inference.field("id").as_str().unwrap())
            );
        }
    }
}

#[test]
fn mathematical_meaning_keeps_complete_iff_clauses_and_dependent_parameter_kinds() {
    let result = build_reading(
        &ReadingInput::Source(include_str!("../examples/reading/mathematical_meaning.lit").into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success, "{}", result.document.stringify());
    let statements = result.document.field("statements").as_array().unwrap();
    let definition = statements[0].field("mathematics");
    let parameters = definition.field("parameters").as_array().unwrap();
    assert_eq!(parameters[0].field("kind").as_str().unwrap(), "set");
    assert!(matches!(parameters[0].field("domain"), JsonValue::Null));
    assert_eq!(parameters[1].field("kind").as_str().unwrap(), "element");
    assert_eq!(parameters[1].field("domain").as_str().unwrap(), "A");
    assert_eq!(definition.field("facts").as_array().unwrap().len(), 2);
    let tex = definition.field("latex");
    let domains = tex.field("parameters").as_array().unwrap();
    assert!(domains[0].as_str().unwrap().contains(r"A:\text{set}"));
    assert!(!domains[0].as_str().unwrap().contains(r"\in"));
    assert!(domains[1].as_str().unwrap().contains(r"x\in A"));
    assert_eq!(tex.field("facts").as_array().unwrap().len(), 2);
    let expansions = result
        .document
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|inference| {
            let math = inference.as_object().unwrap().get("mathematics")?;
            math.as_object().ok()?;
            Some((inference, math))
        })
        .collect::<Vec<_>>();
    let (_, application) = expansions
        .iter()
        .find(|(_, math)| {
            math.field("subject").as_str().unwrap() == "$reading_conditions(reading_carrier, 1)"
        })
        .unwrap();
    assert_eq!(
        application.field("parameters").as_array().unwrap()[1]
            .field("domain")
            .as_str()
            .unwrap(),
        "reading_carrier"
    );
    assert_eq!(
        application.field("parameters").as_array().unwrap()[0]
            .field("kind")
            .as_str()
            .unwrap(),
        "set"
    );
    assert_eq!(
        application
            .field("facts")
            .as_array()
            .unwrap()
            .iter()
            .map(|fact| fact.as_str().unwrap())
            .collect::<Vec<_>>(),
        ["1 = 1", "1 $in reading_carrier"]
    );
    let (inference, chain) = expansions
        .iter()
        .find(|(_, math)| math.field("subject").as_str().unwrap() == "$reading_chain(1)")
        .unwrap();
    assert_eq!(
        chain
            .field("latex")
            .field("facts")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(chain.field("latex").field("facts").as_array().unwrap()[0]
        .as_str()
        .unwrap()
        .contains("1 = 1 = 1"));
    assert_eq!(
        chain
            .field("facts")
            .as_array()
            .unwrap()
            .iter()
            .map(|fact| fact.as_str().unwrap())
            .collect::<Vec<_>>(),
        ["1 = 1 = 1"]
    );
    assert!(
        ids(inference.field("fact_ids")).len() > chain.field("facts").as_array().unwrap().len(),
        "one whole chain clause must not be reconstructed from its several published components"
    );
    let function = statements
        .iter()
        .find(|statement| {
            statement.field("statement_kind").as_str().unwrap() == "Definition.HaveFnEqualStmt"
        })
        .unwrap()
        .field("mathematics");
    assert_eq!(function.field("kind").as_str().unwrap(), "function");
    assert_eq!(function.field("codomain").as_str().unwrap(), "R");
    let abstract_prop = statements.last().unwrap().field("mathematics");
    assert_eq!(
        abstract_prop.field("kind").as_str().unwrap(),
        "abstract_predicate"
    );
    assert!(
        abstract_prop.as_object().unwrap().get("facts").is_none(),
        "an abstract interface must not gain invented iff clauses"
    );
}

#[test]
fn least_squares_latex_preserves_each_real_domain_and_the_whole_quantifier() {
    let result = build_reading(
        &ReadingInput::Source(
            include_str!("../examples/reading/homepage/01-mean-squared-error.lit").into(),
        ),
        true,
        OutputLanguage::Chinese,
    );
    assert!(result.success);
    let statements = result.document.field("statements").as_array().unwrap();
    let definition = statements[0].field("mathematics");
    let latex = definition.field("latex");
    assert_eq!(
        latex.field("subject").as_str().unwrap(),
        r"\mathit{is\_least\_squares\_center}(\mathit{center}, a, b, c)"
    );
    let domains = latex.field("parameters").as_array().unwrap();
    assert_eq!(domains.len(), 4);
    assert!(domains
        .iter()
        .all(|value| value.as_str().unwrap().contains(r"\in \mathbb{R}")));
    let clauses = latex.field("facts").as_array().unwrap();
    assert_eq!(clauses.len(), 1);
    let formula = clauses[0].as_str().unwrap();
    assert!(
        formula.contains(r"\forall \mathit{candidate}\in \mathbb{R}"),
        "{formula}"
    );
    assert!(
        formula.contains(r"\leq") && formula.contains(r"\mathit{center}"),
        "{formula}"
    );
    assert_eq!(
        formula.matches("^{2}").count(),
        6,
        "both sides of the inequality must survive: {formula}"
    );
    let application = result
        .document
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .find_map(|batch| {
            let math = batch.as_object().unwrap().get("mathematics")?;
            let fields = math.as_object().ok()?;
            fields
                .get("subject")?
                .as_str()
                .ok()?
                .contains("mean(72, 84, 96)")
                .then_some(math)
        })
        .unwrap();
    assert_eq!(
        application
            .field("latex")
            .field("parameters")
            .as_array()
            .unwrap()
            .len(),
        4
    );
    let concrete_subject = application
        .field("latex")
        .field("subject")
        .as_str()
        .unwrap();
    assert!(
        concrete_subject.contains(r"\mathit{mean}(72, 84, 96)"),
        "{concrete_subject}"
    );
    assert!(
        !concrete_subject.contains("candidate"),
        "candidate stays bound in the condition"
    );
    let concrete = application
        .field("latex")
        .field("facts")
        .as_array()
        .unwrap()[0]
        .as_str()
        .unwrap();
    assert!(
        concrete.contains("72")
            && concrete.contains("84")
            && concrete.contains("96")
            && concrete.contains(r"\forall")
    );
}

#[test]
fn abstract_predicate_rejection_does_not_gain_a_definition_equivalence() {
    let result = build_reading(
        &ReadingInput::Source("abstract_prop unexplained(x)\nby def $unexplained(1)\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(!result.success);
    let statements = result.document.field("statements").as_array().unwrap();
    assert_eq!(statements[1].field("status").as_str().unwrap(), "rejected");
    assert_eq!(
        statements[1]
            .field("mathematics")
            .field("kind")
            .as_str()
            .unwrap(),
        "fact"
    );
    assert!(result
        .document
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .all(|inference| inference.field("producer_statement_id") != statements[1].field("id")));
}

#[test]
fn real_rule_children_and_prior_fact_citations_are_exported() {
    let source = "have x R\n0 <= x ^ 2\n1 <= x ^ 2 + 1\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let statements = (&result.document).field("statements").as_array().unwrap();
    assert_eq!(statements.len(), 3);
    let evidence = reachable_evidence(&result.document, statements[1].field("evidence"));
    assert!(evidence.contains("EvenPowNonnegative"), "{evidence}");
    assert!(evidence.contains("base_in_real_proof"));
    let prior = ids((&statements[1]).field("produced_fact_ids"));
    let cited = ids((&statements[2]).field("cited_fact_ids"));
    assert!(
        !prior.is_disjoint(&cited),
        "prior={prior:?}, cited={cited:?}"
    );
    assert_eq!(
        ((&statements[2]).field("coverage"))
            .field("evidence")
            .as_str()
            .unwrap(),
        "complete"
    );
    let catalogue = (&result.document).field("rules").as_array().unwrap();
    assert!(catalogue.len() > 500);
    assert!(catalogue.iter().any(|rule| (rule)
        .field("id")
        .as_str()
        .unwrap()
        .contains("EvenPowNonnegative")));
}

#[test]
fn original_unicode_and_comment_offsets_select_only_real_occurrences() {
    let source = "# 中文注释中的 x 不应高亮\nhave x R\n0 <= x ^ 2 # x in a comment\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::Chinese,
    );
    assert!(result.success);
    assert_eq!(
        (&result.document).field("schema_version").as_str().unwrap(),
        "2"
    );
    let occurrences = (&result.document)
        .field("occurrences")
        .as_array()
        .unwrap()
        .iter()
        .filter(|occurrence| {
            let start = (occurrence).field("start_byte").as_u64().unwrap() as usize;
            let end = (occurrence).field("end_byte").as_u64().unwrap() as usize;
            &source[start..end] == "x"
        })
        .collect::<Vec<_>>();
    assert_eq!(occurrences.len(), 2, "{}", result.document.stringify());
    let tokens = result.document.field("sources").as_array().unwrap()[0]
        .field("tokens")
        .as_array()
        .unwrap();
    assert_eq!(
        tokens
            .iter()
            .filter(|t| t.field("text").as_str().unwrap() == "x")
            .count(),
        2
    );
    for token in tokens {
        let start = token.field("start_byte").as_u64().unwrap() as usize;
        let end = token.field("end_byte").as_u64().unwrap() as usize;
        assert_eq!(&source[start..end], token.field("text").as_str().unwrap());
        assert!(start > source.find('\n').unwrap());
        assert!(end <= source.rfind('#').unwrap());
    }
    for occurrence in &occurrences {
        let start = (occurrence).field("start_byte").as_u64().unwrap() as usize;
        let end = (occurrence).field("end_byte").as_u64().unwrap() as usize;
        assert_eq!(&source[start..end], "x");
    }
    assert_eq!(
        (&occurrences[0]).field("symbol_id"),
        (&occurrences[1]).field("symbol_id")
    );
}

#[test]
fn source_tokens_preserve_unicode_spans_and_exclude_inline_asides() {
    let source = "have x ℝ \"prop forall R\"\nx ∈ ℝ\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::Chinese,
    );
    assert!(result.success);
    let tokens = result.document.field("sources").as_array().unwrap()[0]
        .field("tokens")
        .as_array()
        .unwrap();
    assert!(!tokens
        .iter()
        .any(|t| matches!(t.field("text").as_str().unwrap(), "prop" | "forall")));
    let real = tokens
        .iter()
        .filter(|t| t.field("text").as_str().unwrap() == "R")
        .collect::<Vec<_>>();
    assert_eq!(real.len(), 2);
    for token in real {
        let start = token.field("start_byte").as_u64().unwrap() as usize;
        let end = token.field("end_byte").as_u64().unwrap() as usize;
        assert_eq!(&source[start..end], "ℝ");
    }
    let membership = tokens
        .iter()
        .find(|t| t.field("text").as_str().unwrap() == "in")
        .unwrap();
    let start = membership.field("start_byte").as_u64().unwrap() as usize;
    let end = membership.field("end_byte").as_u64().unwrap() as usize;
    assert_eq!(&source[start..end], "∈");
}

#[test]
fn sibling_binders_keep_distinct_semantic_identities() {
    let source = "forall t R:\n    t = t\nforall t R:\n    t + 0 = t\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success, "{}", result.document.stringify());
    let occurrences = (&result.document).field("occurrences").as_array().unwrap();
    let mut by_statement = std::collections::BTreeMap::<String, BTreeSet<String>>::new();
    for occurrence in occurrences.iter().filter(|occurrence| {
        let start = (occurrence).field("start_byte").as_u64().unwrap() as usize;
        let end = (occurrence).field("end_byte").as_u64().unwrap() as usize;
        &source[start..end] == "t"
    }) {
        by_statement
            .entry((occurrence).field("statement_id").as_str().unwrap().into())
            .or_default()
            .insert((occurrence).field("symbol_id").as_str().unwrap().into());
    }
    assert_eq!(by_statement.len(), 2);
    let values = by_statement.values().collect::<Vec<_>>();
    assert!(values[0].is_disjoint(values[1]));
}

#[test]
fn failed_statement_publishes_no_facts_and_later_statement_keeps_context() {
    let result = build_reading(
        &ReadingInput::Source("have z R\nz = 1\nz = z\n".into()),
        false,
        OutputLanguage::English,
    );
    assert!(!result.success);
    let statements = (&result.document).field("statements").as_array().unwrap();
    assert_eq!(statements.len(), 3);
    assert_eq!(
        statements[1].field("statement_kind").as_str().unwrap(),
        "Fact"
    );
    assert_eq!(
        statements[2].field("statement_kind").as_str().unwrap(),
        "Fact"
    );
    assert_eq!(
        (&statements[1]).field("status").as_str().unwrap(),
        "rejected"
    );
    assert!((&statements[1])
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    assert!(statements[1]
        .field("inferred_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    assert_eq!(
        (&statements[2]).field("status").as_str().unwrap(),
        "accepted"
    );
    assert_eq!(
        (&result.document).field("run_result").as_str().unwrap(),
        "failure"
    );
}

#[test]
fn reading_parser_respects_operands_and_rejects_incompatible_actions() {
    let args = |values: &[&str]| {
        values
            .iter()
            .map(|value| (*value).into())
            .collect::<Vec<String>>()
    };
    assert!(parse_reading_command(&args(&["-e", "-reading"]))
        .unwrap()
        .is_none());
    let command =
        parse_reading_command(&args(&["-reading", "-json", "-e", "-2 < 0", "-lang", "zh"]))
            .unwrap()
            .unwrap();
    assert_eq!(command.action, ReadingAction::Json);
    assert_eq!(command.input, ReadingInput::Source("-2 < 0".into()));
    for input in [
        vec!["-reading", "-json"],
        vec!["-reading", "-e", "1=1", "-json", "-export", "out"],
        vec!["-reading", "-e", "1=1", "-json", "-no-browser"],
        vec!["-reading", "-session"],
    ] {
        assert!(parse_reading_command(&args(&input)).is_err(), "{input:?}");
    }
}

#[test]
fn nested_claim_steps_keep_local_producers_and_publish_only_the_goal() {
    let source =
        "claim:\n    ? forall t R:\n        1 <= t ^ 2 + 1\n    0 <= t ^ 2\n    1 <= t ^ 2 + 1\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success, "{}", result.document.stringify());
    let statements = result.document.field("statements").as_array().unwrap();
    assert_eq!(statements.len(), 3);
    let outer = &statements[0];
    let square = &statements[1];
    let addition = &statements[2];
    assert_eq!(
        outer.field("statement_kind").as_str().unwrap(),
        "ProofBlock.ClaimStmt"
    );
    assert_eq!(square.field("statement_kind").as_str().unwrap(), "Fact");
    assert_eq!(addition.field("statement_kind").as_str().unwrap(), "Fact");
    assert_eq!(square.field("line").as_u64().unwrap(), 4);
    assert_eq!(addition.field("line").as_u64().unwrap(), 5);
    assert_eq!(square.field("parent_statement_id"), outer.field("id"));
    assert_eq!(addition.field("parent_statement_id"), outer.field("id"));
    assert_ne!(square.field("scope_id"), outer.field("scope_id"));
    let square_facts = ids(square.field("produced_fact_ids"));
    assert!(!square_facts.is_empty());
    assert!(!square_facts.is_disjoint(&ids(addition.field("cited_fact_ids"))));
    assert!(square_facts.is_disjoint(&ids(outer.field("produced_fact_ids"))));
    let facts = result.document.field("facts").as_array().unwrap();
    for id in square_facts {
        let fact = facts
            .iter()
            .find(|fact| fact.field("id").as_str().unwrap() == id)
            .unwrap();
        assert_eq!(fact.field("producer_statement_id"), square.field("id"));
        assert_eq!(fact.field("scope_id"), square.field("scope_id"));
    }
    assert!(!ids(outer.field("produced_fact_ids")).is_empty());
    assert!(
        reachable_evidence(&result.document, outer.field("evidence"))
            .contains("statement_reference")
    );
    assert_eq!(
        outer
            .field("coverage")
            .field("source_mapping")
            .as_str()
            .unwrap(),
        "complete"
    );
}

#[test]
fn inference_catalogue_contains_struct_payload_leaves() {
    let result = build_reading(&ReadingInput::Empty, false, OutputLanguage::English);
    let rules = result.document.field("rules").as_array().unwrap();
    assert!(
        rules
            .iter()
            .filter(|rule| rule.field("category").as_str().unwrap() == "infer")
            .count()
            > 50
    );
}

#[test]
fn sibling_local_predicate_definitions_do_not_share_highlights() {
    let source = "claim:\n    ? 0 = 0\n    prop mark(a R):\n        a = a\n    $mark(0)\nclaim:\n    ? 0 = 0\n    prop mark(a R):\n        a = 0\n    $mark(0)\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let symbols = result
        .document
        .field("symbols")
        .as_array()
        .unwrap()
        .iter()
        .filter(|symbol| symbol.field("name").as_str().unwrap() == "mark")
        .collect::<Vec<_>>();
    assert_eq!(symbols.len(), 2);
    assert_ne!(symbols[0].field("id"), symbols[1].field("id"));
    let mentions = result.document.field("occurrences").as_array().unwrap();
    for symbol in symbols {
        assert_eq!(
            result
                .document
                .field("statements")
                .as_array()
                .unwrap()
                .iter()
                .filter(|statement| statement
                    .as_object()
                    .unwrap()
                    .get("declaration_symbol_ids")
                    .and_then(|ids| ids.as_array().ok())
                    .is_some_and(|ids| ids.contains(symbol.field("id"))))
                .count(),
            1,
            "each local predicate owns its own declaration identity"
        );
        let occurrences = mentions
            .iter()
            .filter(|occurrence| occurrence.field("symbol_id") == symbol.field("id"))
            .collect::<Vec<_>>();
        assert_eq!(occurrences.len(), 2, "{}", result.document.stringify());
        assert_eq!(
            occurrences
                .iter()
                .filter(|occurrence| matches!(
                    occurrence.field("definition"),
                    JsonValue::Bool(true)
                ))
                .count(),
            1
        );
    }
}

#[test]
fn declaration_reference_badges_exclude_parameter_and_existential_binders() {
    for (source, kind, expected) in [
        (
            include_str!("../examples/test_statements/def_prop_stmt.lit"),
            "DefPropStmt",
            "prop_pos",
        ),
        (
            include_str!("../examples/test_statements/have_fn_equal_stmt.lit"),
            "HaveFnEqualStmt",
            "fn_square",
        ),
        (
            include_str!("../examples/test_statements/have_obj_equal_stmt.lit"),
            "HaveObjEqualStmt",
            "typed_n",
        ),
        (
            include_str!("../examples/test_statements/obtain_obj_from_exist_fact.lit"),
            "ObtainObjFromExistFact",
            "obtained_a",
        ),
        (
            include_str!("../examples/test_statements/have_by_preimage_stmt.lit"),
            "HaveByPreimageStmt",
            "pre_a",
        ),
        (
            include_str!("../examples/stmt_nodes/definition/def_template.lit"),
            "DefTemplateStmt",
            "carrier_copy",
        ),
    ] {
        let result = build_reading(
            &ReadingInput::Source(source.into()),
            true,
            OutputLanguage::Chinese,
        );
        assert!(
            result.success,
            "{kind}: {}",
            result.document.field("diagnostics").stringify()
        );
        let statement = result
            .document
            .field("statements")
            .as_array()
            .unwrap()
            .iter()
            .find(|statement| {
                statement
                    .field("statement_kind")
                    .as_str()
                    .unwrap()
                    .split('.')
                    .next_back()
                    == Some(kind)
            })
            .unwrap();
        let ids = statement
            .field("declaration_symbol_ids")
            .as_array()
            .unwrap();
        assert_eq!(
            ids.len(),
            1,
            "{kind}: parameters and nested binders must not become root declarations"
        );
        let symbol = result
            .document
            .field("symbols")
            .as_array()
            .unwrap()
            .iter()
            .find(|symbol| symbol.field("id") == &ids[0])
            .unwrap();
        assert_eq!(symbol.field("name").as_str().unwrap(), expected);
    }
}

#[test]
fn repeated_induction_body_keeps_distinct_execution_contexts() {
    let source = include_str!("../examples/stmt_nodes/by/by_induc.lit");
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let statements = result.document.field("statements").as_array().unwrap();
    assert_eq!(statements.len(), 3);
    assert_eq!(
        statements[0].field("statement_kind").as_str().unwrap(),
        "By.ByInducStmt"
    );
    assert_eq!(
        statements[1].field("statement_kind"),
        statements[2].field("statement_kind")
    );
    assert_eq!(
        statements[1].field("source_statement_id"),
        statements[2].field("source_statement_id")
    );
    assert_ne!(statements[1].field("id"), statements[2].field("id"));
    assert_ne!(
        statements[1].field("scope_id"),
        statements[2].field("scope_id")
    );
    assert_eq!(
        statements[0]
            .field("coverage")
            .field("source_mapping")
            .as_str()
            .unwrap(),
        "complete"
    );
}

#[test]
fn unexecuted_proof_body_keeps_syntax_identity_without_a_verdict() {
    let result = build_reading(
        &ReadingInput::Source("claim:\n    ? 1 = 1\n    1 = 2\n    1 = 1\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(!result.success);
    let statements = result.document.field("statements").as_array().unwrap();
    assert_eq!(statements.len(), 3);
    assert_eq!(
        statements[0].field("statement_kind").as_str().unwrap(),
        "ProofBlock.ClaimStmt"
    );
    let unexecuted = &statements[2];
    assert_eq!(unexecuted.field("status").as_str().unwrap(), "not_exported");
    assert_eq!(unexecuted.field("statement_kind").as_str().unwrap(), "Fact");
}

#[test]
fn explicit_user_assumptions_remain_visible_through_real_citations() {
    // Deliberately assumed input tests the trust boundary, not a proof route.
    let source = "have r R\ntrust r = 2\nr = 2\n";
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        false,
        OutputLanguage::English,
    );
    assert!(result.success);
    let statements = result.document.field("statements").as_array().unwrap();
    assert_eq!(
        statements[1].field("origin").as_str().unwrap(),
        "user_trust"
    );
    assert!(ids(statements[2].field("trust_dependencies"))
        .contains(statements[1].field("id").as_str().unwrap()));
    assert_eq!(
        result
            .document
            .field("trust_summary")
            .field("user_assumptions")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    let strict = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!strict.success);
    assert!(strict
        .document
        .field("trust_summary")
        .field("user_assumptions")
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn source_and_engine_fingerprints_are_bound_to_the_bundle() {
    let result = build_reading(
        &ReadingInput::Source("0 = 0".into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    for name in ["catalogue_id", "input_digest"] {
        assert!(result
            .document
            .field(name)
            .as_str()
            .unwrap()
            .starts_with("fnv1a64:"));
    }
    assert!(result
        .document
        .field("engine")
        .field("executable_id")
        .as_str()
        .unwrap()
        .starts_with("fnv1a64:"));
    assert!(matches!(
        result.document.field("execution_policy").field("strict"),
        JsonValue::Bool(true)
    ));
}

#[test]
fn language_changes_presentation_without_changing_machine_evidence() {
    let input = ReadingInput::Source("have x R\n0 <= x ^ 2\n1 <= x ^ 2 + 1\n".into());
    let english = build_reading(&input, true, OutputLanguage::English);
    let chinese = build_reading(&input, true, OutputLanguage::Chinese);
    assert!(english.success && chinese.success);
    for key in [
        "sources",
        "statements",
        "evidence_nodes",
        "inferences",
        "well_definedness",
        "facts",
        "symbols",
        "occurrences",
        "scopes",
        "input_digest",
        "catalogue_id",
    ] {
        assert_eq!(
            english.document.field(key),
            chinese.document.field(key),
            "machine field differs: {key}"
        );
    }
}

#[test]
fn exported_evidence_and_rule_references_resolve_inside_the_bundle() {
    let result = build_reading(
        &ReadingInput::Source("have x R\n0 <= x ^ 2\n1 <= x ^ 2 + 1\n".into()),
        true,
        OutputLanguage::English,
    );
    let rules = result
        .document
        .field("rules")
        .as_array()
        .unwrap()
        .iter()
        .map(|rule| rule.field("id").as_str().unwrap())
        .collect::<BTreeSet<_>>();
    let facts = result
        .document
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .map(|fact| fact.field("id").as_str().unwrap())
        .collect::<BTreeSet<_>>();
    for statement in result.document.field("statements").as_array().unwrap() {
        assert!(!reachable_evidence(&result.document, statement.field("evidence")).is_empty());
        for id in ids(statement.field("rule_ids")) {
            assert!(rules.contains(id.as_str()), "unknown rule {id}");
        }
        for field in ["produced_fact_ids", "cited_fact_ids"] {
            for id in ids(statement.field(field)) {
                assert!(facts.contains(id.as_str()), "unknown fact {id}");
            }
        }
    }
}

trait ReadingFields {
    fn field(&self, key: &str) -> &JsonValue;
}

fn reachable_evidence(bundle: &JsonValue, root: &JsonValue) -> String {
    let nodes = bundle
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| (entry.field("id").as_str().unwrap(), entry.field("node")))
        .collect::<std::collections::BTreeMap<_, _>>();
    let statements = bundle
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| (entry.field("id").as_str().unwrap(), entry.field("evidence")))
        .collect::<std::collections::BTreeMap<_, _>>();
    let mut visited = BTreeSet::new();
    let mut pending = vec![root];
    let mut output = String::new();
    while let Some(value) = pending.pop() {
        output.push_str(&value.stringify());
        match value {
            JsonValue::Object(fields) => {
                match fields.get("kind").and_then(|value| value.as_str().ok()) {
                    Some("evidence_reference") => {
                        let id = value.field("evidence_id").as_str().unwrap();
                        if visited.insert(format!("node:{id}")) {
                            pending.push(nodes[id]);
                        }
                    }
                    Some("statement_reference") => {
                        let id = value.field("statement_id").as_str().unwrap();
                        if visited.insert(format!("stmt:{id}")) {
                            pending.push(statements[id]);
                        }
                    }
                    _ => pending.extend(fields.iter().map(|(_, value)| value)),
                }
            }
            JsonValue::Array(values) => pending.extend(values),
            _ => {}
        }
    }
    output
}

impl ReadingFields for JsonValue {
    fn field(&self, key: &str) -> &JsonValue {
        self.as_object()
            .unwrap()
            .get(key)
            .unwrap_or_else(|| panic!("missing {key}"))
    }
}

fn ids(value: &JsonValue) -> BTreeSet<String> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|id| id.as_str().unwrap().into())
        .collect()
}
