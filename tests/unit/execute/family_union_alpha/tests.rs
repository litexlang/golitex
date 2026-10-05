use super::*;
use crate::ast::stmt::Stmt;
use crate::launch_command::{LaunchCommand, OutputLanguage};

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true,
        language: OutputLanguage::English,
    })
}

const SOURCE: &str = "have fn singleton_family(index Z) power_set(Z) = {index}\nfn(member_index Z) power_set(Z) {singleton_family(member_index)}(0) $in fn_range(fn(member_index Z) power_set(Z) {singleton_family(member_index)})\nfn(member_index Z) power_set(Z) {singleton_family(member_index)}(0) = singleton_family(0)\nsingleton_family(0) $in fn_range(fn(member_index Z) power_set(Z) {singleton_family(member_index)})\n0 $in singleton_family(0)\n";
const GOAL: &str = "0 $in family_union(fn_range(fn(renamed_index Z) power_set(Z) {singleton_family(renamed_index)}))\n";

fn parse_in(rt: &mut Runtime, code: &str) -> InFact {
    let tokens = crate::tokenize::Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::InFact(fact))) = statements.remove(0) else { panic!("membership goal") };
    fact
}

#[test]
fn family_union_alpha_uses_real_member_citation_and_inherited_premise() {
    let mut rt = runtime();
    let setup = rt.run_litex_code(SOURCE).unwrap();
    assert!(setup.success && setup.session_error.is_none(), "real five-root setup");
    let goal = parse_in(&mut rt, GOAL);
    let Obj::SetOperator(SetOperator::FamilyUnion(union)) = &goal.set else { panic!("family union") };
    let family = union.left.as_ref();
    let mut same_family = Vec::new();
    for env in rt.execution_environments_stack.iter().rev() {
        if let Some(knowns) = env.facts.known_atomic_except_equality_facts.by_prop.get(&(AtomicName::Plain { name: IN.into() }, true)) {
            for known in knowns {
                if let AtomicFact::InFact(known) = known {
                    if compound_objs_alpha_equal(&known.set, family) {
                        eprintln!("family candidate: rawIR={}, structuralalpha=true, member={}", known.set.ir()==family.ir(), known.element.readable_string());
                        same_family.push((known.fact_id, known.element.clone()));
                    }
                }
            }
        }
    }
    assert!(!same_family.is_empty());
    let mut legitimate_cites = Vec::new();
    for (id, member) in &same_family {
        let element = Fact::AtomicFact(AtomicFact::InFact(InFact { fact_id: rt.global_ids.allocate_fact_id(), element: goal.element.clone(), set: member.clone(), line_file: None }));
        if !rt.verify_builtin_rule_premise(&element, VerifyState::top_level()).unwrap().is_failed() {
            legitimate_cites.push(*id);
        }
    }
    assert!(!legitimate_cites.is_empty(), "a real member premise succeeds without changing permission");
    let proof = rt.family_union_membership_proof(&goal, VerifyState::top_level()).unwrap();
    let Some(InFactSearchProofByBuiltinRule::FamilyUnionMembershipFromMember(proof)) = proof else { panic!("alpha-equivalent family must retain the same union rule") };
    assert!(legitimate_cites.contains(&proof.cite_member_set_in_family_fact_id));
    assert!(!proof.element_in_member_set_proof.is_failed());
    let run = rt.run_litex_code(GOAL).unwrap();
    assert!(run.success && run.session_error.is_none());
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(detail.contains("FamilyUnionMembershipFromMember"), "{detail}");
    assert!(detail.contains("cite_fact_id") && detail.contains("element_in_member_set_proof"));
}

#[test]
fn family_union_alpha_maintained_public_and_generic_tracers_pass() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/in_family_union_from_member_alpha.lit")).unwrap();
    assert!(run.success && run.session_error.is_none());
    let source = "claim:\n    ? forall X set, opens power_set(power_set(X)), Index set, cover fn(slot Index) opens, chosen Index, point cover(chosen):\n        point $in family_union(fn_range(fn(j Index) opens {cover(j)}))\n    cover $in fn(slot Index) opens\n    fn(member_index Index) opens {cover(member_index)}(chosen) $in fn_range(fn(member_index Index) opens {cover(member_index)})\n    fn(member_index Index) opens {cover(member_index)}(chosen) = cover(chosen)\n    cover(chosen) $in fn_range(fn(member_index Index) opens {cover(member_index)})\n    point $in cover(chosen)\n    point $in family_union(fn_range(fn(j Index) opens {cover(j)}))\n";
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn family_union_alpha_rejects_different_free_function_body_or_guard() {
    for (extra, goal) in [
        ("", "0 $in family_union(fn_range(fn(renamed_index Z) power_set(Z) {{1}}))"),
        ("", "0 $in family_union(fn_range(fn(renamed_index Z: renamed_index>0) power_set(Z) {singleton_family(renamed_index)}))"),
        ("have fn ones(index Z) power_set(Z) = {1}\n", "0 $in family_union(fn_range(fn(renamed_index Z) power_set(Z) {ones(renamed_index)}))"),
    ] {
        let mut rt = runtime();
        let setup = rt.run_litex_code(&format!("{SOURCE}{GOAL}{extra}")).unwrap();
        assert!(setup.success && setup.session_error.is_none(), "valid positive prefix");
        let parsed = parse_in(&mut rt, &format!("{goal}\n"));
        assert!(rt.family_union_membership_proof(&parsed, VerifyState::top_level()).unwrap().is_none(), "cannot reuse a different family");
        let run = rt.run_litex_code(&format!("{goal}\n")).unwrap();
        assert!(!run.success && run.session_error.is_none(), "false membership must reject: {goal}");
        assert!(rt.run_litex_code("1=1\n").unwrap().success);
    }
}

#[test]
fn family_union_alpha_still_requires_both_membership_premises() {
    // A constant family makes the wrong-element control mathematically false.
    let mut rt = runtime();
    let source = SOURCE.replace("{index}", "{0}");
    let setup = rt.run_litex_code(&format!("{source}{GOAL}")).unwrap();
    assert!(setup.success && setup.session_error.is_none());
    let run = rt.run_litex_code(&GOAL.replacen("0 $in", "1 $in", 1)).unwrap();
    assert!(!run.success && run.session_error.is_none());
    for hypothesis in ["", "        not A $in F\n"] {
        let mut rt = runtime();
        let source = format!("claim:\n    ? forall X set, F power_set(power_set(X)), A power_set(X), point A:\n{hypothesis}{}point $in family_union(F)\n    point $in A\n    point $in family_union(F)\n", if hypothesis.is_empty() { "        " } else { "        =>:\n            " });
        let run = rt.run_litex_code(&source).unwrap();
        assert!(!run.success && run.session_error.is_none(), "positive A in F is missing: {source}");
        assert!(rt.run_litex_code("1=1\n").unwrap().success);
    }
}

#[test]
fn family_union_alpha_keeps_signature_structure_rigid_and_parent_wd() {
    let mut rt = runtime();
    assert!(rt.run_litex_code(SOURCE).unwrap().success);
    let original = parse_in(&mut rt, GOAL);
    let Obj::SetOperator(SetOperator::FamilyUnion(original)) = original.set else { panic!("union") };
    for changed in [
        GOAL.replace("renamed_index Z", "renamed_index N"),
        GOAL.replace("power_set(Z)", "power_set(R)"),
        GOAL.replace("renamed_index Z", "renamed_index, another_index Z"),
    ] {
        let changed = parse_in(&mut rt, &changed);
        let Obj::SetOperator(SetOperator::FamilyUnion(changed)) = changed.set else { panic!("union") };
        assert!(!compound_objs_alpha_equal(&original.left, &changed.left), "only bound renaming, not domain/codomain/arity changes");
    }
    assert!(rt.run_litex_code(GOAL).unwrap().success, "valid whole parent before WD control");
    let invalid = GOAL.replace("power_set(Z)", "power_set(N)");
    let run = rt.run_litex_code(&invalid).unwrap();
    assert!(!run.success && run.session_error.is_none(), "arbitrary integer singleton cannot claim natural codomain");
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(detail.contains("well_defined"), "parent WD must reject: {detail}");
}
