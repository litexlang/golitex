use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less::LessFactSearchProofByBuiltinRule as Lt,less_equal::LessEqualFactSearchProofByBuiltinRule as Le};
use crate::prelude::*;
const SOURCES: [(&str, &str); 8] = [
    (
        r#"forall x R:
    -1<=x
    x<=1
    =>:
        (-pi)/2<=arcsin(x)
"#,
        "arcsinePrincipalLowerValue",
    ),
    (
        r#"forall x R:
    -1<=x
    x<=1
    =>:
        arcsin(x)<=pi/2
"#,
        "arcsinePrincipalUpperValue",
    ),
    (
        r#"forall x R:
    -1<=x
    x<=1
    =>:
        0<=arccos(x)
"#,
        "arccosinePrincipalLowerValue",
    ),
    (
        r#"forall x R:
    -1<=x
    x<=1
    =>:
        arccos(x)<=pi
"#,
        "arccosinePrincipalUpperValue",
    ),
    (
        r#"forall x R => (-pi)/2<arctan(x)
"#,
        "arctangentPrincipalLowerValue",
    ),
    (
        r#"forall x R => arctan(x)<pi/2
"#,
        "arctangentPrincipalUpperValue",
    ),
    (
        r#"forall x R => 0<arccot(x)
"#,
        "arccotangentPrincipalLowerValue",
    ),
    (
        r#"forall x R => arccot(x)<pi
"#,
        "arccotangentPrincipalUpperValue",
    ),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn selected(proof: &VerifyAtomicExceptEqualityFactSuccess, index: usize) {
    use AtomicExceptEqualityFactSearchProofByBuiltinRule as Rule;
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &proof.searched_proof else {
        panic!("selected principal bound builtin")
    };
    assert!(matches!(
        (rule, index),
        (Rule::LessEqualFact(Le::ArcsinPrincipalLowerBound(_)), 0)
            | (Rule::LessEqualFact(Le::ArcsinPrincipalUpperBound(_)), 1)
            | (Rule::LessEqualFact(Le::ArccosPrincipalLowerBound(_)), 2)
            | (Rule::LessEqualFact(Le::ArccosPrincipalUpperBound(_)), 3)
            | (Rule::LessFact(Lt::ArctanPrincipalLowerBound(_)), 4)
            | (Rule::LessFact(Lt::ArctanPrincipalUpperBound(_)), 5)
            | (Rule::LessFact(Lt::ArccotPrincipalLowerBound(_)), 6)
            | (Rule::LessFact(Lt::ArccotPrincipalUpperBound(_)), 7)
    ));
}
#[test]
fn all_eight_inverse_principal_bounds_replay_the_original_typed_constructor() {
    for (index, (source, law)) in SOURCES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        selected(target(&mut run), index);
        let output = compiler
            .compile_run(&run, "inverse_principal_bound")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler
                .compile_run(&run, "inverse_principal_bound")
                .unwrap()
        );
    }
}
#[test]
fn inverse_principal_bounds_require_original_endpoint_direction_and_wd() {
    for (index, (source, _)) in SOURCES.into_iter().enumerate() {
        for change in ["endpoint", "direction", "wd"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            selected(p, index);
            if change == "wd" {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .swap(0, 1)
            } else {
                let (left, right) = match &mut p.fact {
                    AtomicFact::LessFact(f) => (&mut f.left, &mut f.right),
                    AtomicFact::LessEqualFact(f) => (&mut f.left, &mut f.right),
                    _ => panic!(),
                };
                if change == "direction" {
                    std::mem::swap(left, right)
                } else {
                    let bound = if index % 2 == 0 { left } else { right };
                    *bound = Obj::Literal(Literal::Number(Number::new("7".into())))
                };
            }
            compiler.compile_run(&run,change).expect_err("the original principal bound direction, exact pi endpoint and constructor evidence are required");
        }
    }
}
#[test]
fn inverse_principal_bounds_keep_weak_and_strict_interval_endpoints_distinct() {
    for (index, (source, _)) in SOURCES.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let p = target(&mut run);
        selected(p, index);
        p.fact = match &p.fact {
            AtomicFact::LessFact(f) => AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: f.fact_id,
                left: f.left.clone(),
                right: f.right.clone(),
                line_file: f.line_file.clone(),
            }),
            AtomicFact::LessEqualFact(f) => AtomicFact::LessFact(LessFact {
                fact_id: f.fact_id,
                left: f.left.clone(),
                right: f.right.clone(),
                line_file: f.line_file.clone(),
            }),
            _ => panic!(),
        };
        compiler
            .compile_run(&run, "strictness")
            .expect_err("the selected range rule cannot change strictness");
    }
}
