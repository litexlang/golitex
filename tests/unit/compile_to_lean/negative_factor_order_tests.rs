use crate::compile_to_lean::helper::SourceOrderKind;
use crate::compile_to_lean::LitexToLeanCompiler;
use crate::prelude::*;

#[test]
fn all_sixteen_selected_negative_factor_variants_compile() {
    for (source, kind, left, right) in [
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    b<a
    =>:
        c*a<c*b
"#,
            SourceOrderKind::Less,
            true,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    b<a
    =>:
        a*c<b*c
"#,
            SourceOrderKind::Less,
            false,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    b<a
    =>:
        c*a<b*c
"#,
            SourceOrderKind::Less,
            true,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    b<a
    =>:
        a*c<c*b
"#,
            SourceOrderKind::Less,
            false,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    a<b
    =>:
        c*a>c*b
"#,
            SourceOrderKind::Greater,
            true,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    a<b
    =>:
        a*c>b*c
"#,
            SourceOrderKind::Greater,
            false,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    a<b
    =>:
        c*a>b*c
"#,
            SourceOrderKind::Greater,
            true,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    a<b
    =>:
        a*c>c*b
"#,
            SourceOrderKind::Greater,
            false,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    b<=a
    =>:
        c*a<=c*b
"#,
            SourceOrderKind::LessEqual,
            true,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    b<=a
    =>:
        a*c<=b*c
"#,
            SourceOrderKind::LessEqual,
            false,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    b<=a
    =>:
        c*a<=b*c
"#,
            SourceOrderKind::LessEqual,
            true,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    b<=a
    =>:
        a*c<=c*b
"#,
            SourceOrderKind::LessEqual,
            false,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    a<=b
    =>:
        c*a>=c*b
"#,
            SourceOrderKind::GreaterEqual,
            true,
            true,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    a<=b
    =>:
        a*c>=b*c
"#,
            SourceOrderKind::GreaterEqual,
            false,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    a<=b
    =>:
        c*a>=b*c
"#,
            SourceOrderKind::GreaterEqual,
            true,
            false,
        ),
        (
            r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<=0
    a<=b
    =>:
        a*c>=c*b
"#,
            SourceOrderKind::GreaterEqual,
            false,
            true,
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(top)) = &run.statement_results[0]
        else {
            panic!("source fact");
        };
        let VerifyFactResult::ForallFact(universal) = &top.verify_result else {
            panic!("universal");
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(universal)) =
            universal.as_ref()
        else {
            panic!("local universal");
        };
        let proof = super::phase2_atomic(&universal.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &proof.searched_proof
        else {
            panic!("selected builtin");
        };
        let (actual, actual_left, actual_right, _, _) =
            LitexToLeanCompiler::negative_factor_evidence(rule)
                .expect("actual negative-factor variant");
        assert!(
            actual == kind && actual_left == left && actual_right == right,
            "{source}"
        );
        let output = compiler.compile_run(&run, "negative_factor").unwrap();
        assert!(output.contains(if source.contains("c<=0") {
            "Litex.mulStructuralLeNonpositiveLeft"
        } else {
            "Litex.mulStructuralLtNegativeLeft"
        }));
        assert_eq!(
            output,
            compiler.compile_run(&run, "negative_factor").unwrap()
        );
    }
}

#[test]
fn negative_factor_children_cannot_be_swapped() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule;
    let source = r#"# Multiplication by a negative or nonpositive real factor reverses the operand order.
forall a,b,c R:
    c<0
    b<a
    =>:
        c*a<c*b
"#;
    let (mut run, compiler) = super::execute(source);
    let universal = super::forall_proof_mut(&mut run.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut universal.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictLess(p),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("original negative-factor leaf");
    };
    std::mem::swap(&mut p.factor_sign_proof, &mut p.reversed_order_proof);
    compiler
        .compile_run(&run, "swapped_negative_children")
        .expect_err("factor sign and operand order are distinct original evidence");
}

#[test]
fn strict_children_can_support_the_selected_weak_rule() {
    for (sign, order) in [("c<0", "b<a"), ("0>c", "a>b"), ("c<=0", "a>=b")] {
        let source =
            format!("forall a,b,c R:\n    {sign}\n    {order}\n    =>:\n        c*a<=c*b\n");
        let (run, compiler) = super::execute(&source);
        let output = compiler
            .compile_run(&run, "negative_factor_stronger_premises")
            .unwrap();
        assert!(output.contains("Litex.mulStructuralLeNonpositiveLeft"));
    }
}

#[test]
fn nonpositive_factor_does_not_justify_strict_order() {
    for source in [
        "forall a,b,c R:\n    c<=0\n    b<a\n    =>:\n        c*a<c*b\n",
        "forall a,b,c R:\n    c<0\n    b<=a\n    =>:\n        c*a<c*b\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        assert!(
            !Runtime::new(command)
                .run_litex_code(source)
                .unwrap()
                .success
        );
    }
}
