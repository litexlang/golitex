use crate::prelude::*;

#[test]
fn native_symdiff_original_ten_selected_payloads() {
    for (name, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let proof = selected(&mut run);
        assert_eq!(
            proof.rule_id(),
            match *name {
                "commutative" => "SymDiffCommutative",
                "empty" => "SymDiffEmpty",
                "empty_left" => "SymDiffEmptyLeft",
                "cancel" => "SymDiffCancel",
                "union_minus_intersection" => "SymDiffUnionMinusIntersection",
                "associative" => "SymDiffAssociative",
                "intersection_distributes" => "IntersectionDistributesSymDiff",
                "finite_rationals" => "SymDiffFiniteRationals",
                "self" => "SymDiffSelf",
                "definition" => "SymDiffDefinition",
                _ => panic!(),
            }
        );
        if let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymmetricDifferenceEqualityProof::SymDiffFiniteRationals(p)=proof {
            assert_eq!(p.left_values,vec![EvalRational::new(1,1).unwrap(),EvalRational::new(2,1).unwrap()]);
            assert_eq!(p.right_values,vec![EvalRational::new(2,1).unwrap(),EvalRational::new(3,1).unwrap()]);
            assert_eq!(p.result_values,vec![EvalRational::new(1,1).unwrap(),EvalRational::new(3,1).unwrap()]);
            let wd=last_equality(&mut run).well_defined_proof.as_detailed_mut().unwrap();
            let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::SymmetricDifference(p)),..}=wd.left.as_detailed_mut().unwrap() else{panic!()};
            assert_eq!(p.child_obj_well_defined.len(),2);
            for child in &p.child_obj_well_defined {
                let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::ListSet(p)),..}=child.detailed_ref() else{panic!()};
                assert_eq!(p.child_obj_well_defined.len(),2);assert_eq!(p.requirement_fact_verified.len(),1);
            }
        }
        let result = super::compile_run(&run, &compiler, "native_symdiff_tree");
        let output = result.unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "native_symdiff_tree").unwrap()
        );
    }
}

#[test]
fn native_symdiff_replays_all_original_profile_routes() {
    for (name, source, expected) in PROFILES {
        let (mut run, compiler) = super::execute(source);
        if *name == "distribution_returned_bound" {
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) =
                &mut run.statement_results[0]
            else {
                panic!()
            };
            let VerifyFactResult::ForallFact(p) = &mut s.verify_result else {
                panic!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!()
            };
            let p = super::equality_proof_mut(
                &mut p.proved_then_facts.last_mut().unwrap().verify_result,
            );
            let EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SymmetricDifference(p),
            ) = &p.searched_proof
            else {
                panic!()
            };
            assert_eq!(p.rule_id(), *expected);
            assert!(matches!(
                &last_equality(&mut run).searched_proof,
                EqualFactSearchedProof::ByKnownForallFact(_)
            ));
        } else {
            assert_eq!(selected(&mut run).rule_id(), *expected, "{name}");
        }
        let output = super::compile_run(&run, &compiler, "native_symdiff_profiles").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "native_symdiff_profiles").unwrap()
        );
    }
}
#[test]
fn native_symdiff_keeps_the_actual_selected_variant() {
    for (name, source) in SOURCES {
        if ["self", "definition"].contains(name) {
            continue;
        }
        let (mut run, compiler) = super::execute(source);
        let (mut donor, _) = super::execute(SELF);
        std::mem::swap(selected(&mut run), selected(&mut donor));
        reject(&run, &compiler, "selected_variant");
    }
}
#[test]
fn native_symdiff_validates_both_exact_equation_endpoints() {
    for (_, source) in SOURCES {
        for right_side in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let p = last_equality(&mut run);
            if right_side {
                p.fact.right = Obj::StandardSet(StandardSet::C)
            } else {
                p.fact.left = Obj::StandardSet(StandardSet::C)
            };
            reject(&run, &compiler, "equation_endpoint");
        }
    }
}
#[test]
fn native_symdiff_keeps_both_original_endpoint_wd() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let wd = last_equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject(&run, &compiler, "endpoint_wd");
    }
}
#[test]
fn native_symdiff_keeps_original_constructor_children() {
    for (_, source) in SOURCES {
        let (mut run, compiler) = super::execute(source);
        let wd = last_equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetOperator(p),..}=wd.left.as_detailed_mut().unwrap() else{panic!()};
        match p {crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::SymmetricDifference(p)=>p.child_obj_well_defined.clear(),crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::Intersect(p)=>p.child_obj_well_defined.clear(),_=>panic!()};
        reject(&run, &compiler, "constructor_children");
    }
}
#[test]
fn native_symdiff_keeps_nested_schema_operands() {
    for source in [CANCEL, ASSOCIATE, DISTRIBUTE] {
        let (mut run, compiler) = super::execute(source);
        let Obj::SetOperator(p) = &mut last_equality(&mut run).fact.left else {
            panic!()
        };
        match p {
            SetOperator::SymmetricDifference(p) => {
                p.left = Box::new(Obj::StandardSet(StandardSet::C))
            }
            SetOperator::Intersect(p) => p.right = Box::new(Obj::StandardSet(StandardSet::C)),
            _ => panic!(),
        };
        reject(&run, &compiler, "nested_schema");
    }
}
#[test]
fn native_symdiff_requires_all_three_retained_value_vectors() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        values(&mut run, slot).pop();
        reject(&run, &compiler, "value_arity");
    }
}
#[test]
fn native_symdiff_binds_each_retained_value_to_its_source() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        values(&mut run, slot)[0] = EvalRational::new(99, 1).unwrap();
        reject(&run, &compiler, "retained_value");
    }
}
#[test]
fn native_symdiff_preserves_order_within_all_retained_vectors() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        values(&mut run, slot).swap(0, 1);
        reject(&run, &compiler, "value_order");
    }
}
#[test]
fn native_symdiff_does_not_duplicate_retained_values() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        let v = values(&mut run, slot);
        v[1] = v[0].clone();
        reject(&run, &compiler, "duplicate_value");
    }
}
#[test]
fn native_symdiff_preserves_left_and_right_value_ownership() {
    let (mut run, compiler) = super::execute(FINITE);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymmetricDifferenceEqualityProof::SymDiffFiniteRationals(p)=selected(&mut run) else{panic!()};
    std::mem::swap(&mut p.left_values, &mut p.right_values);
    reject(&run, &compiler, "value_operand_ownership");
}
#[test]
fn native_symdiff_checks_the_finite_membership_certificate() {
    let (mut run, compiler) = super::execute(FINITE);
    values(&mut run, 2)[0] = EvalRational::new(2, 1).unwrap();
    let e = super::compile_run(&run, &compiler, "finite_certificate").unwrap_err();
    assert_eq!(e.route, "SymDiff/FiniteCertificate");
}
#[test]
fn native_symdiff_requires_literal_distinctness_for_each_list() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        literal_wd(&mut run, slot).requirement_fact_verified.clear();
        reject(&run, &compiler, "distinctness");
    }
}
#[test]
fn native_symdiff_keeps_each_literal_distinctness_subject() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        let p = literal_wd(&mut run, slot);
        let AtomicFact::NotEqualFact(f) =
            &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[0]).fact
        else {
            panic!()
        };
        f.left = Obj::StandardSet(StandardSet::C);
        reject(&run, &compiler, "distinctness_subject");
    }
}
#[test]
fn native_symdiff_requires_every_literal_child_wd() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        literal_wd(&mut run, slot).child_obj_well_defined.pop();
        reject(&run, &compiler, "literal_child_count");
    }
}
#[test]
fn native_symdiff_preserves_literal_child_wd_order() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        literal_wd(&mut run, slot).child_obj_well_defined.swap(0, 1);
        reject(&run, &compiler, "literal_child_order");
    }
}
#[test]
fn native_symdiff_keeps_literal_numeric_wd_subjects() {
    for slot in 0..3 {
        let (mut run, compiler) = super::execute(FINITE);
        let p = literal_wd(&mut run, slot);
        let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{obj,..}=p.child_obj_well_defined[0].as_detailed_mut().unwrap() else{panic!()};
        *obj = Obj::StandardSet(StandardSet::C);
        reject(&run, &compiler, "numeric_wd_subject");
    }
}
#[test]
fn native_symdiff_requires_empty_operand_and_result_shapes() {
    for source in [EMPTY, EMPTY_LEFT, SELF] {
        let (mut run, compiler) = super::execute(source);
        let p = last_equality(&mut run);
        let Obj::SetOperator(SetOperator::SymmetricDifference(s)) = &mut p.fact.left else {
            panic!()
        };
        if std::ptr::eq(source, EMPTY) {
            s.right = Box::new(Obj::StandardSet(StandardSet::C));
        } else if std::ptr::eq(source, EMPTY_LEFT) {
            s.left = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            p.fact.right = Obj::StandardSet(StandardSet::C);
        }
        reject(&run, &compiler, "empty_shape");
    }
}

fn last_verify(run: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    fn last(p: &mut VerifyFactResult) -> &mut VerifyFactResult {
        if matches!(p, VerifyFactResult::ForallFact(_)) {
            let VerifyFactResult::ForallFact(p) = p else {
                unreachable!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!()
            };
            return last(&mut p.proved_then_facts.last_mut().unwrap().verify_result);
        }
        p
    }
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    last(&mut p.verify_result)
}
fn last_equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    super::equality_proof_mut(last_verify(run))
}
fn selected(run:&mut RunLitexCodeResult)->&mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymmetricDifferenceEqualityProof{
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::SymmetricDifference(p),
    ) = &mut last_equality(run).searched_proof
    else {
        panic!("original native selected rule")
    };
    p
}
fn values(run: &mut RunLitexCodeResult, slot: usize) -> &mut Vec<EvalRational> {
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_symmetric_difference::SymmetricDifferenceEqualityProof::SymDiffFiniteRationals(p)=selected(run) else{panic!()};
    match slot {
        0 => &mut p.left_values,
        1 => &mut p.right_values,
        2 => &mut p.result_values,
        _ => panic!(),
    }
}
fn literal_wd(run:&mut RunLitexCodeResult,slot:usize)->&mut crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ListSetObjWellDefinedProof{
    let wd = last_equality(run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    let object = if slot == 2 {
        &mut wd.right
    } else {
        let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::SymmetricDifference(p)),..}=wd.left.as_detailed_mut().unwrap() else{panic!()};
        p.child_obj_well_defined[slot].as_mut()
    };
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::ListSet(p)),..}=object.as_detailed_mut().unwrap() else{panic!()};
    p
}
fn reject(
    run: &RunLitexCodeResult,
    compiler: &crate::compile_to_lean::LitexToLeanCompiler,
    name: &str,
) {
    assert!(
        super::compile_run(run, compiler, name).is_err(),
        "altered native evidence accepted: {name}"
    );
}
const SOURCES:&[(&str,&str)]=&[
("commutative","forall replay40_CA,replay40_CB set:\n    set_diff(replay40_CA,replay40_CB)=set_diff(replay40_CB,replay40_CA)\n"),
("empty","forall replay40_EA set:\n    set_diff(replay40_EA,{})=replay40_EA\n"),
("empty_left","forall replay40_LA set:\n    set_diff({},replay40_LA)=replay40_LA\n"),
("cancel","forall replay40_XA,replay40_XB set:\n    set_diff(set_diff(replay40_XA,replay40_XB),replay40_XB)=replay40_XA\n"),
("union_minus_intersection","forall replay40_UA,replay40_UB set:\n    set_diff(replay40_UA,replay40_UB)=set_minus(union(replay40_UA,replay40_UB),intersect(replay40_UA,replay40_UB))\n"),
("associative","forall replay40_AA,replay40_AB,replay40_AC set:\n    set_diff(set_diff(replay40_AA,replay40_AB),replay40_AC)=set_diff(replay40_AA,set_diff(replay40_AB,replay40_AC))\n"),
("intersection_distributes","forall replay40_IA,replay40_IB,replay40_IC set:\n    intersect(replay40_IA,set_diff(replay40_IB,replay40_IC))=set_diff(intersect(replay40_IA,replay40_IB),intersect(replay40_IA,replay40_IC))\n"),
("finite_rationals","set_diff({1,2},{2,3})={1,3}\n"),
("self","forall tree40_A set:\n    set_diff(tree40_A,tree40_A)={}\n"),
("definition","forall tree40_A,tree40_B set:\n    set_diff(tree40_A,tree40_B)=union(set_minus(tree40_A,tree40_B),set_minus(tree40_B,tree40_A))\n"),
];
const PROFILES:&[(&str,&str,&str)]=&[
("commutative","# Native symmetric-difference commutativity consumes its selected rule.\n# Former source (strict source success,compiler rejection):\n# forall replay40_CA,replay40_CB set:\n#     set_diff(replay40_CA,replay40_CB)=set_diff(replay40_CB,replay40_CA)\n# Former compiler result: SymDiff/SelectedIdentity.\n# Current replay validates the exact equation and original constructor WD.\nforall replay40_CA,replay40_CB set:\n    set_diff(replay40_CA,replay40_CB)=set_diff(replay40_CB,replay40_CA)\n# Check: litex -lean -strict -f lean/examples/native_symdiff_commutative/statement.lit\n","SymDiffCommutative"),
("empty","forall replay40_EA set:\n    set_diff(replay40_EA,{})=replay40_EA\n","SymDiffEmpty"),
("empty_left","forall replay40_LA set:\n    set_diff({},replay40_LA)=replay40_LA\n","SymDiffEmptyLeft"),
("cancel","forall replay40_XA,replay40_XB set:\n    set_diff(set_diff(replay40_XA,replay40_XB),replay40_XB)=replay40_XA\n","SymDiffCancel"),
("union_minus_intersection","forall replay40_UA,replay40_UB set:\n    set_diff(replay40_UA,replay40_UB)=set_minus(union(replay40_UA,replay40_UB),intersect(replay40_UA,replay40_UB))\n","SymDiffUnionMinusIntersection"),
("associative","forall replay40_AA,replay40_AB,replay40_AC set:\n    set_diff(set_diff(replay40_AA,replay40_AB),replay40_AC)=set_diff(replay40_AA,set_diff(replay40_AB,replay40_AC))\n","SymDiffAssociative"),
("intersection_distributes","forall replay40_IA,replay40_IB,replay40_IC set:\n    intersect(replay40_IA,set_diff(replay40_IB,replay40_IC))=set_diff(intersect(replay40_IA,replay40_IB),intersect(replay40_IA,replay40_IC))\n","IntersectionDistributesSymDiff"),
("finite_rationals","set_diff({1,2},{2,3})={1,3}\n","SymDiffFiniteRationals"),
("self","forall tree40_A set:\n    set_diff(tree40_A,tree40_A)={}\n","SymDiffSelf"),
("definition","forall tree40_A,tree40_B set:\n    set_diff(tree40_A,tree40_B)=union(set_minus(tree40_A,tree40_B),set_minus(tree40_B,tree40_A))\n","SymDiffDefinition"),
("commutative_reversed","forall reverse40_CA,reverse40_CB set:\n    set_diff(reverse40_CB,reverse40_CA)=set_diff(reverse40_CA,reverse40_CB)\n","SymDiffCommutative"),
("empty_reversed","forall reverse40_EA set:\n    reverse40_EA=set_diff(reverse40_EA,{})\n","SymDiffEmpty"),
("empty_left_reversed","forall reverse40_LA set:\n    reverse40_LA=set_diff({},reverse40_LA)\n","SymDiffEmptyLeft"),
("cancel_reversed","forall reverse40_XA,reverse40_XB set:\n    reverse40_XA=set_diff(set_diff(reverse40_XA,reverse40_XB),reverse40_XB)\n","SymDiffCancel"),
("union_minus_intersection_reversed","forall reverse40_UA,reverse40_UB set:\n    set_minus(union(reverse40_UA,reverse40_UB),intersect(reverse40_UA,reverse40_UB))=set_diff(reverse40_UA,reverse40_UB)\n","SymDiffUnionMinusIntersection"),
("associative_reversed","forall reverse40_AA,reverse40_AB,reverse40_AC set:\n    set_diff(reverse40_AA,set_diff(reverse40_AB,reverse40_AC))=set_diff(set_diff(reverse40_AA,reverse40_AB),reverse40_AC)\n","SymDiffAssociative"),
("intersection_distributes_reversed","forall reverse40_IA,reverse40_IB,reverse40_IC set:\n    set_diff(intersect(reverse40_IA,reverse40_IB),intersect(reverse40_IA,reverse40_IC))=intersect(reverse40_IA,set_diff(reverse40_IB,reverse40_IC))\n","IntersectionDistributesSymDiff"),
("self_reversed","forall reverse40_control_A set:\n    {}=set_diff(reverse40_control_A,reverse40_control_A)\n","SymDiffSelf"),
("definition_reversed","forall reverse40_control_A,reverse40_control_B set:\n    union(set_minus(reverse40_control_A,reverse40_control_B),set_minus(reverse40_control_B,reverse40_control_A))=set_diff(reverse40_control_A,reverse40_control_B)\n","SymDiffDefinition"),
("commutative_guard","have native40_guard set = fn(native40_gv R:native40_gv>0) R\nset_diff(native40_guard,C)=set_diff(C,native40_guard)\n","SymDiffCommutative"),
("commutative_groups","have native40_groups set = fn(native40_mv R,native40_mu C) C\nset_diff(native40_groups,R)=set_diff(R,native40_groups)\n","SymDiffCommutative"),
("commutative_nested","forall native40_na,native40_nb,native40_nc set:\n    set_diff(power_set(native40_na),union(native40_nb,native40_nc))=set_diff(union(native40_nb,native40_nc),power_set(native40_na))\n","SymDiffCommutative"),
("associative_nested","forall native40_aa,native40_ab,native40_ac set:\n    set_diff(set_diff(power_set(native40_aa),{native40_ab}),union(native40_ac,{}))=set_diff(power_set(native40_aa),set_diff({native40_ab},union(native40_ac,{})))\n","SymDiffAssociative"),
("cancel_guard","have native40_cancel set = fn(native40_cv R:native40_cv>0) R\nset_diff(set_diff(native40_cancel,C),C)=native40_cancel\n","SymDiffCancel"),
("distribution_returned_bound","forall replay40_IA,replay40_IB,replay40_IC set:\n    intersect(replay40_IA,set_diff(replay40_IB,replay40_IC))=set_diff(intersect(replay40_IA,replay40_IB),intersect(replay40_IA,replay40_IC))\nforall native40_h fn(native40_t R) N,native40_a R:\n    native40_h(native40_a) $in N\n    intersect(fn(native40_rv closed_range(1,native40_h(native40_a))) R,set_diff(R,C))=set_diff(intersect(fn(native40_rv closed_range(1,native40_h(native40_a))) R,R),intersect(fn(native40_rv closed_range(1,native40_h(native40_a))) R,C))\n","IntersectionDistributesSymDiff"),
("finite_reversed","{1,3}=set_diff({1,2},{2,3})\n","SymDiffFiniteRationals"),
("finite_permuted","set_diff({3,1},{2,3})={2,1}\n","SymDiffFiniteRationals"),
("finite_empty","set_diff({},{})={}\n","SymDiffFiniteRationals"),
("finite_empty_left","set_diff({},{1,2})={2,1}\n","SymDiffFiniteRationals"),
("finite_empty_right","set_diff({1,2},{})={2,1}\n","SymDiffFiniteRationals"),
("finite_equal_sets","set_diff({1,2},{2,1})={}\n","SymDiffFiniteRationals"),
("finite_disjoint","set_diff({1,2},{3,4})={4,2,1,3}\n","SymDiffFiniteRationals"),
("finite_signed_fractions","set_diff({-1,1/2},{1/2,2/3})={2/3,-1}\n","SymDiffFiniteRationals"),
("finite_closed_arithmetic","set_diff({1+1,3^2},{4/2,abs(-3)})={9,3}\n","SymDiffFiniteRationals"),
("finite_decimal","set_diff({0.5,1},{1/2,2})={2,1}\n","SymDiffFiniteRationals"),
("finite_exact_power","set_diff({2^(-1),3},{1/2,4})={4,3}\n","SymDiffFiniteRationals"),
("finite_real_observations","set_diff({floor(3/2),ceil(3/2)},{min(1,2),max(2,3)})={3,2}\n","SymDiffFiniteRationals"),
("finite_exact_sqrt_log","set_diff({sqrt(4),log(2,8)},{2,4})={4,3}\n","SymDiffFiniteRationals"),
("finite_integer_operations","set_diff({gcd(6,4),7%3},{1,lcm(2,3)})={6,2}\n","SymDiffFiniteRationals"),
("finite_hyperbolic_values","set_diff({sinh(0),cosh(0)},{1,2})={2,0}\n","SymDiffFiniteRationals"),
];
const SELF: &str = "forall tree40_A set:\n    set_diff(tree40_A,tree40_A)={}\n";
const FINITE: &str = "set_diff({1,2},{2,3})={1,3}\n";
const CANCEL:&str="forall replay40_XA,replay40_XB set:\n    set_diff(set_diff(replay40_XA,replay40_XB),replay40_XB)=replay40_XA\n";
const ASSOCIATE:&str="forall replay40_AA,replay40_AB,replay40_AC set:\n    set_diff(set_diff(replay40_AA,replay40_AB),replay40_AC)=set_diff(replay40_AA,set_diff(replay40_AB,replay40_AC))\n";
const DISTRIBUTE:&str="forall replay40_IA,replay40_IB,replay40_IC set:\n    intersect(replay40_IA,set_diff(replay40_IB,replay40_IC))=set_diff(intersect(replay40_IA,replay40_IB),intersect(replay40_IA,replay40_IC))\n";
const EMPTY: &str = "forall replay40_EA set:\n    set_diff(replay40_EA,{})=replay40_EA\n";
const EMPTY_LEFT: &str = "forall replay40_LA set:\n    set_diff({},replay40_LA)=replay40_LA\n";
