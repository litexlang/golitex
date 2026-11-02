use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

const SOURCE: &str = "forall p,q cart(R,R):\n    p(1)=q(1)\n    p(2)=q(2)\n    =>:\n        p=q\n";

#[test]
fn cartesian_coordinate_compiles_original_binary_strategy() {
    let (run, compiler) = super::execute(SOURCE);
    let generated = compiler.compile_run(&run, "OriginalCoordinate49").unwrap();
    assert!(generated.contains("Litex.FiniteFunction.cart_ext"));
    assert!(!generated.contains("sorry") && !generated.contains("admit"));
}

fn selected49(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_composed_structure::CartesianCoordinateEqualityProof{
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::CartesianCoordinateEquality(proof),
    ) = &mut equal.searched_proof
    else {
        panic!("original strategy")
    };
    proof
}

#[test]
fn cartesian_coordinate_rejects_missing_and_reordered_requirements() {
    for change in [0, 1, 2] {
        let (mut run, compiler) = super::execute(SOURCE);
        let proof = selected49(&mut run);
        match change {
            0 => {
                proof.requirement_facts.pop();
            }
            1 => {
                proof.proof_of_requirement_facts.pop();
            }
            _ => {
                proof.requirement_facts.swap(0, 1);
                proof.proof_of_requirement_facts.swap(0, 1);
            }
        }
        let error = compiler.compile_run(&run, "BadCoordinate49").unwrap_err();
        assert_eq!(
            error.route,
            if change == 2 {
                "CartesianCoordinateEquality/RequirementSubject"
            } else {
                "CartesianCoordinateEquality/Requirements"
            }
        );
    }
}

#[test]
fn cartesian_coordinate_requires_original_membership_citation() {
    let (mut run, compiler) = super::execute(SOURCE);
    let outer = super::forall_proof(run.statement_results.last().unwrap());
    let wrong = outer.fact.dom_facts[0].fact_id();
    let proof = selected49(&mut run);
    let KnownTupleShapeProof::CartesianMembership(p) = &mut proof.left_shape else {
        panic!()
    };
    p.membership.fact_id = wrong;
    assert_eq!(
        compiler
            .compile_run(&run, "BadCoordinateMember49")
            .unwrap_err()
            .route,
        "FiniteFunction/MembershipCitation"
    );
}

#[test]
fn cartesian_coordinate_original_shapes_and_ordered_children() {
    for (name, source, dimension) in [
        ("binary", SOURCE, 2),
        ("ternary", "forall p,q cart(R,R,R):\n    p(1)=q(1)\n    p(2)=q(2)\n    p(3)=q(3)\n    =>:\n        p=q\n", 3),
        ("generic", "forall X,Y set,p,q cart(X,Y):\n    p(1)=q(1)\n    p(2)=q(2)\n    =>:\n        p=q\n", 2),
    ] {
        let (run, _compiler) = super::execute(source);
        let outer = super::forall_proof(run.statement_results.last().unwrap());
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::CartesianCoordinateEquality(proof),
        ) = &equal.searched_proof else { panic!("actual selected coordinate strategy") };
        assert_eq!(proof.left_shape.dimension(), dimension);
        assert_eq!(proof.right_shape.dimension(), dimension);
        assert_eq!(proof.requirement_facts.len(), dimension);
        assert_eq!(proof.proof_of_requirement_facts.len(), dimension);
        for (side, object, shape) in [
            ("left", &equal.fact.left, &proof.left_shape),
            ("right", &equal.fact.right, &proof.right_shape),
        ] {
            let KnownTupleShapeProof::CartesianMembership(shape) = shape else {
                panic!("these original sources have direct Cartesian membership")
            };
            assert_eq!(shape.membership.element.ir(), object.ir());
            assert!(shape.subject_equal.path.is_empty() && shape.carrier_equal.path.is_empty());
            assert_eq!(shape.cart.args.len(), dimension);
            eprintln!("ORIGINAL49 {name} {side} membership:{} subject:{} carrier:{} subject_edges:{} carrier_edges:{}",
                shape.membership.fact_id.value(), shape.membership.element.ir(), shape.membership.set.ir(),
                shape.subject_equal.path.len(), shape.carrier_equal.path.len());
        }
        for (index, (requirement, child)) in proof.requirement_facts.iter()
            .zip(&proof.proof_of_requirement_facts).enumerate()
        {
            let Fact::AtomicFact(AtomicFact::EqualFact(coordinate)) = requirement else {
                panic!("original equality requirement")
            };
            assert_eq!(coordinate.left.ir(), finite_function_coordinate(&equal.fact.left,index).unwrap().ir());
            assert_eq!(coordinate.right.ir(), finite_function_coordinate(&equal.fact.right,index).unwrap().ir());
            assert_eq!(source_subject(child).unwrap(), *requirement);
            let child = super::equality_proof(child);
            let route = match &child.searched_proof {
                EqualFactSearchedProof::ByEquivalenceClass(EqualFactSearchedProofByEquivalenceClass::KnownPath(path)) => {
                    assert_eq!(path.path.len(), 1);
                    assert_eq!(path.path[0].2, outer.fact.dom_facts[index].fact_id());
                    eprintln!("ORIGINAL49 {name} coordinate:{} requirement:{} original_cite:{} edges:{} subject:{}",
                        index+1, requirement.fact_id().value(), path.path[0].2.value(), path.path.len(), requirement.ir());
                    "KnownPath"
                }
                _ => "other selected child",
            };
            eprintln!("ORIGINAL49 {name} coordinate:{} route:{route}",index+1);
        }
    }
}

#[test]
fn cartesian_coordinate_original_returned_and_nested_shapes() {
    for (name, source, expected_shape) in [
        (
            "heterogeneous",
            r##"forall sc49_X,sc49_Y,sc49_U,sc49_V set,sc49_p cart(sc49_X,sc49_Y),sc49_q cart(sc49_U,sc49_V):
    sc49_p(1)=sc49_q(1)
    sc49_p(2)=sc49_q(2)
    =>:
        sc49_p=sc49_q
"##,
            "CartesianMembership",
        ),
        (
            "returned",
            r##"forall sc49_S set,sc49_f fn(sc49_t sc49_S) cart(R,R),sc49_a,sc49_b sc49_S:
    sc49_f(sc49_a)(1)=sc49_f(sc49_b)(1)
    sc49_f(sc49_a)(2)=sc49_f(sc49_b)(2)
    =>:
        sc49_f(sc49_a)=sc49_f(sc49_b)
"##,
            "FunctionCodomain",
        ),
        (
            "returned_nested",
            r##"forall sc49_S set,sc49_f fn(sc49_t sc49_S) cart(cart(R,R),R),sc49_a,sc49_b sc49_S:
    sc49_f(sc49_a)(1)(1)=sc49_f(sc49_b)(1)(1)
    sc49_f(sc49_a)(1)(2)=sc49_f(sc49_b)(1)(2)
    =>:
        sc49_f(sc49_a)(1)=sc49_f(sc49_b)(1)
"##,
            "CartesianCoordinate",
        ),
    ] {
        let (run, _compiler) = super::execute(source);
        let outer = super::forall_proof(run.statement_results.last().unwrap());
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::CartesianCoordinateEquality(proof),
        ) = &equal.searched_proof
        else {
            panic!("actual selected coordinate strategy:{name}")
        };
        for (side, shape) in [("left", &proof.left_shape), ("right", &proof.right_shape)] {
            let kind = match shape {
                KnownTupleShapeProof::CartesianMembership(_) => "CartesianMembership",
                KnownTupleShapeProof::TupleEquality(_) => "TupleEquality",
                KnownTupleShapeProof::FunctionCodomain(_) => "FunctionCodomain",
                KnownTupleShapeProof::CartesianCoordinate(_) => "CartesianCoordinate",
            };
            eprintln!(
                "ORIGINAL49 {name} {side} shape:{kind} dimension:{}",
                shape.dimension()
            );
            assert_eq!(kind, expected_shape);
            assert_eq!(shape.dimension(), 2);
        }
        assert_eq!(proof.requirement_facts.len(), 2);
        assert_eq!(proof.proof_of_requirement_facts.len(), 2);
        for (index, (requirement, child)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = requirement else {
                panic!()
            };
            assert_eq!(
                f.left.ir(),
                finite_function_coordinate(&equal.fact.left, index)
                    .unwrap()
                    .ir()
            );
            assert_eq!(
                f.right.ir(),
                finite_function_coordinate(&equal.fact.right, index)
                    .unwrap()
                    .ir()
            );
            assert_eq!(source_subject(child).unwrap(), *requirement);
            let child = super::equality_proof(child);
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &child.searched_proof
            else {
                panic!("original direct coordinate citation")
            };
            assert_eq!(path.path.len(), 1);
            assert_eq!(path.path[0].2, outer.fact.dom_facts[index].fact_id());
            eprintln!(
                "ORIGINAL49 {name} coordinate:{} original_cite:{} subject:{}",
                index + 1,
                path.path[0].2.value(),
                requirement.ir()
            );
        }
    }
}

#[test]
fn cartesian_coordinate_original_nested_call_wd_stages() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, FnObjDomainFnSetEvidence, ObjWellDefinedProofByDef,
    };
    let (run, _compiler) = super::execute(
        r##"forall sc49_S set,sc49_f fn(sc49_t sc49_S) cart(cart(R,R),R),sc49_a,sc49_b sc49_S:
    sc49_f(sc49_a)(1)(1)=sc49_f(sc49_b)(1)(1)
    sc49_f(sc49_a)(1)(2)=sc49_f(sc49_b)(1)(2)
    =>:
        sc49_f(sc49_a)(1)=sc49_f(sc49_b)(1)
"##,
    );
    let outer = super::forall_proof(run.statement_results.last().unwrap());
    let FactWellDefinedProof::Equality(wd) = &outer.assumed_dom_facts[0].well_defined else {
        panic!("original domain equality WD")
    };
    for (side, wd) in [
        ("left", &wd.detailed_ref().left),
        ("right", &wd.detailed_ref().right),
    ] {
        let DetailedObjWellDefinedProof::ByDef {
            obj: Obj::FnObj(app),
            proof: ObjWellDefinedProofByDef::FnObj(call),
        } = wd.detailed_ref()
        else {
            panic!("original complete flat call WD")
        };
        assert_eq!(app.body.len(), 3);
        assert!(app.body.iter().all(|g| g.len() == 1));
        let (kind, signature) = match call.domain_fn_set.as_ref().unwrap() {
            FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. } => ("InFunctionSet", fn_set),
            FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => ("AnonymousLiteral", fn_set),
            FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. } => {
                ("TemplateDefinition", fn_set)
            }
            FnObjDomainFnSetEvidence::FiniteFunction(p) => ("FiniteFunction", &p.signature),
            FnObjDomainFnSetEvidence::Matrix(p) => ("Matrix", &p.function.body),
            FnObjDomainFnSetEvidence::Composition(p) => ("Composition", &p.function.body),
            FnObjDomainFnSetEvidence::MultivariableSelector(p) => {
                ("MultivariableSelector", &p.signature)
            }
        };
        eprintln!("ORIGINAL49 nested WD {side} kind:{kind} application:{} groups:{} children:{} requirements:{} original_return:{}",wd.obj().ir(),app.body.len(),call.child_obj_well_defined.len(),call.requirement_fact_verified.len(),signature.ret_set.ir());
        for (i, child) in call.child_obj_well_defined.iter().enumerate() {
            eprintln!("ORIGINAL49 nested WD {side} child{i}:{}", child.obj().ir());
        }
        for (i, requirement) in call.requirement_fact_verified.iter().enumerate() {
            eprintln!(
                "ORIGINAL49 nested WD {side} requirement{i}:{}",
                source_subject(requirement).unwrap().ir()
            );
        }
        assert!(
            !call.child_obj_well_defined.is_empty() && !call.requirement_fact_verified.is_empty()
        );
    }
}

const NESTED_SOURCE: &str = "forall S set,f fn(t S) cart(cart(R,R),R),a,b S:\n    f(a)(1)(1)=f(b)(1)(1)\n    f(a)(1)(2)=f(b)(1)(2)\n    =>:\n        f(a)(1)=f(b)(1)\n";

fn nested_call49(run: &mut RunLitexCodeResult) -> &mut FnObjObjWellDefinedProof {
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let FactWellDefinedProof::Equality(wd) = &mut outer.assumed_dom_facts[0].well_defined else {
        panic!()
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = wd
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!()
    };
    call
}

#[test]
fn cartesian_coordinate_compiles_original_nested_prefix_verification() {
    let (run, compiler) = super::execute(NESTED_SOURCE);
    let generated = compiler
        .compile_run(&run, "OriginalNestedCoordinate49")
        .unwrap();
    assert!(generated.contains("Litex.FiniteFunction.cart_ext"));
    assert!(generated.contains("Litex.cartCall"));
}

#[test]
fn cartesian_coordinate_rejects_missing_reordered_or_wrong_prefix_verification() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(NESTED_SOURCE);
        let call = nested_call49(&mut run);
        assert_eq!(call.requirement_fact_verified.len(), 4);
        match change {
            0 => {
                call.requirement_fact_verified.remove(2);
            }
            1 => {
                call.requirement_fact_verified.swap(2, 3);
            }
            2 | 3 => {
                let atomic = super::atomic_proof_mut(&mut call.requirement_fact_verified[2]);
                let AtomicFact::InFact(member) = &mut atomic.fact else {
                    panic!()
                };
                if change == 2 {
                    member.element = Obj::StandardSet(StandardSet::R);
                } else {
                    member.set = Obj::StandardSet(StandardSet::R);
                }
            }
            _ => unreachable!(),
        }
        assert_eq!(
            compiler.compile_run(&run, "BadPrefix49").unwrap_err().route,
            "ReturnedFunction/PrefixMembership"
        );
    }
}

#[test]
fn cartesian_coordinate_rejects_missing_nested_argument_wd() {
    let (mut run, compiler) = super::execute(NESTED_SOURCE);
    nested_call49(&mut run).child_obj_well_defined.pop();
    assert_eq!(
        compiler
            .compile_run(&run, "MissingNestedChild49")
            .unwrap_err()
            .route,
        "WD/FnObj/StageArity"
    );
}

#[test]
fn cartesian_coordinate_replays_the_prefix_membership_original_citation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
        InFactSearchProofByKnownSpecialProperty,
    };
    let (mut run, compiler) = super::execute(NESTED_SOURCE);
    let call = nested_call49(&mut run);
    let atomic = super::atomic_proof_mut(&mut call.requirement_fact_verified[2]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::TupleCoordinate(prefix),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("original prefix coordinate membership")
    };
    let KnownTupleShapeProof::FunctionCodomain(shape) = &mut prefix.shape else {
        panic!()
    };
    shape.membership_proof.cite_property_fact_id = FactId::new(u64::MAX);
    compiler
        .compile_run(&run, "ForeignPrefixCitation49")
        .expect_err("the original prefix proof must be consumed");
}

#[test]
fn cartesian_coordinate_rejects_an_exact_citation_from_a_later_sibling_scope() {
    let later_source = "forall r,s cart(R,R,R):\n    r(1)=s(1)\n    r(2)=s(2)\n    r(3)=s(3)\n    =>:\n        r=s\n";
    let (mut run, compiler) = super::execute(&format!("{SOURCE}{later_source}"));
    let later = super::forall_proof(&run.statement_results[1]);
    let later_id = later
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut first.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::CartesianCoordinateEquality(p),
    ) = &mut equal.searched_proof
    else {
        panic!()
    };
    let KnownTupleShapeProof::CartesianMembership(shape) = &mut p.left_shape else {
        panic!()
    };
    shape.membership.fact_id = later_id;
    compiler
        .compile_run(&run, "SiblingCoordinateCitation49")
        .expect_err("a later sibling declaration is not visible");
}
