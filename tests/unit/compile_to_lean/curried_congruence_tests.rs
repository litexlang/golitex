use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProofByMatchingOneArgByOne;
use crate::prelude::*;

const SOURCES: &[(&str, &str, &[usize])] = &[
    (
        "unary",
        r#"# Equal arguments preserve a curried function value.
forall f fn(x R) fn(y R) R, a,b,c,d R:
    a = b
    c = d
    =>:
        f(a)(c) = f(b)(d)
"#,
        &[1, 1],
    ),
    (
        "binary",
        r#"# Equal functions and both argument groups give equal binary returned values.
forall f,g fn(t R) fn(x,y R) R, a,b,c,d,p,q R:
    f = g
    a = b
    c = d
    p = q
    =>:
        f(a)(c,p) = g(b)(d,q)
"#,
        &[2, 1],
    ),
    (
        "three_groups",
        r#"# Three applications preserve equality with a ternary final argument group.
forall f,g fn(t R) fn(u R) fn(x,y,z R) R, a,b,c,d,p,q,r,s,v,w R:
    f = g
    a = b
    c = d
    p = q
    r = s
    v = w
    =>:
        f(a)(c)(p,r,v) = g(b)(d)(q,s,w)
"#,
        &[3, 1, 1],
    ),
    (
        "generic",
        r#"# Curried function equality preserves arbitrary source carriers.
forall sc67_A,sc67_B,sc67_T set, f,g fn(t sc67_A) fn(x sc67_B) sc67_T, a,b sc67_A, c,d sc67_B:
    f = g
    a = b
    c = d
    =>:
        f(a)(c) = g(b)(d)
"#,
        &[1, 1],
    ),
    (
        "unequal_prefixes",
        r#"# A returned function and an equal named function agree on equal arguments.
forall f fn(t R) fn(x R) R, g fn(x R) R, a,b,c R:
    f(a) = g
    b = c
    =>:
        f(a)(b) = g(c)
"#,
        &[1],
    ),
    (
        "guarded",
        r#"# Curried value equality retains both original nonzero and positive call guards.
forall f,g fn(t R: t != 0) fn(x R: x > 0) R, a,b,c,d R:
    f = g
    a = b
    a != 0
    b != 0
    c = d
    c > 0
    d > 0
    =>:
        f(a)(c) = g(b)(d)
"#,
        &[1, 1],
    ),
];

fn equality(run: &RunLitexCodeResult) -> &VerifyEqualitySuccess {
    let outer = super::forall_proof(&run.statement_results[0]);
    super::equality_proof(&outer.proved_then_facts[0].verify_result)
}

fn matching_mut(run: &mut RunLitexCodeResult) -> &mut EqualFactSearchedProofByMatchingOneArgByOne {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(proof) = &mut equality.searched_proof else {
        panic!("the original flattened constructor certificate")
    };
    proof
}

fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "CurriedCorruptEvidence")
        .expect_err("changed original evidence must reject");
}

#[test]
fn curried_matching_replays_original_outer_first_groups_and_prefix() {
    for (name, source, arities) in SOURCES {
        let (run, compiler) = super::execute(source);
        let equality = equality(&run);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(proof) = &equality.searched_proof else {
            panic!("{name}: retain actual matching rather than replace it with a strategy")
        };
        let (Obj::FnObj(left), Obj::FnObj(right)) = (&equality.fact.left, &equality.fact.right)
        else {
            panic!()
        };
        let groups = left
            .body
            .iter()
            .rev()
            .zip(right.body.iter().rev())
            .map(|(l, r)| {
                assert_eq!(l.len(), r.len());
                l.len()
            })
            .collect::<Vec<_>>();
        assert_eq!(groups, *arities);
        let pairs = corresponding_arg_pairs(&equality.fact.left, &equality.fact.right).unwrap();
        assert_eq!(
            proof.corresponding_arg_equal_proofs.len(),
            arities.iter().sum::<usize>() + 1
        );
        for (checked, (left, right)) in proof.corresponding_arg_equal_proofs.iter().zip(pairs) {
            let Fact::AtomicFact(AtomicFact::EqualFact(subject)) = source_subject(checked).unwrap()
            else {
                panic!()
            };
            assert_eq!(subject.left.ir(), left.ir());
            assert_eq!(subject.right.ir(), right.ir());
        }
        let output = compiler
            .compile_run(&run, "CurriedOriginalCertificate")
            .unwrap();
        assert!(output.contains("congrArg₂ (Litex.FunctionSemantics.callValue"));
        assert!(!output.contains("sorry") && !output.contains("admit"));
        eprintln!(
            "ORIGINAL {name}: groups={groups:?} checked_children={}",
            proof.corresponding_arg_equal_proofs.len()
        );
    }
}

#[test]
fn curried_matching_requires_every_recorded_child_without_extras() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        matching_mut(&mut run).corresponding_arg_equal_proofs.pop();
        reject(&run, &compiler);
        let (mut run, compiler) = super::execute(source);
        let (mut extra, _) = super::execute("0 = 0\n");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(extra)) =
            extra.statement_results.remove(0)
        else {
            panic!()
        };
        matching_mut(&mut run)
            .corresponding_arg_equal_proofs
            .push(extra.verify_result);
        reject(&run, &compiler);
    }
}

#[test]
fn curried_matching_preserves_the_boundary_between_outer_and_inner_groups() {
    for (_, source, arities) in SOURCES {
        if arities.len() < 2 {
            continue;
        }
        let (mut run, compiler) = super::execute(source);
        matching_mut(&mut run)
            .corresponding_arg_equal_proofs
            .swap(0, arities[0]);
        reject(&run, &compiler);
    }
}

#[test]
fn curried_matching_preserves_the_recorded_callable_prefix_child() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let p = matching_mut(&mut run);
        let last = p.corresponding_arg_equal_proofs.len() - 1;
        p.corresponding_arg_equal_proofs.swap(0, last);
        reject(&run, &compiler);
    }
}

#[test]
fn curried_matching_rejects_a_reversed_argument_equality_subject() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let p = super::equality_proof_mut(
            &mut matching_mut(&mut run).corresponding_arg_equal_proofs[0],
        );
        std::mem::swap(&mut p.fact.left, &mut p.fact.right);
        reject(&run, &compiler);
    }
}

#[test]
fn curried_matching_rejects_an_unknown_original_premise_citation() {
    for (_, source, _) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let p = super::equality_proof_mut(
            &mut matching_mut(&mut run).corresponding_arg_equal_proofs[0],
        );
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut p.searched_proof
        else {
            panic!("actual premise equality path")
        };
        assert!(!path.path.is_empty());
        path.path[0].2 = FactId::new(u64::MAX);
        reject(&run, &compiler);
    }
}

#[test]
fn curried_matching_child_facts_do_not_escape_the_original_forall() {
    for (_, source, _) in SOURCES {
        let (run, compiler) = super::execute(source);
        let equality = equality(&run);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equality.searched_proof else {
            panic!()
        };
        let outer = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        for child in &p.corresponding_arg_equal_proofs {
            assert!(compiler
                .cited_fact_reference(source_subject(child).unwrap().fact_id(), &outer)
                .is_err());
        }
        compiler.compile_run(&run, "CurriedClosedEvidence").unwrap();
    }
}
