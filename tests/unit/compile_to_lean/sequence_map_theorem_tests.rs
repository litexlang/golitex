use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;
const NEG: &str = r#"# Negating every term negates the limit of a real sequence.
thm checked_sequence_limit_negation:
    ? forall a seq(R), L R:
        $has_seq_limit(a, L)
        =>:
            $has_seq_limit(fn(n N+) R{-a(n)}, -L)
    release thm seq_limit_neg(a, L)
"#;
const ABS: &str = r#"# Taking real absolute values preserves a sequence limit.
thm checked_sequence_limit_absolute:
    ? forall a seq(R), L R:
        $has_seq_limit(a, L)
        =>:
            $has_seq_limit(fn(n N+) R{abs(a(n))}, abs(L))
    release thm seq_limit_abs(a, L)
"#;
const SCALE: &str = r#"# Multiplication by a fixed real scalar preserves a sequence limit.
thm checked_sequence_limit_scale:
    ? forall a seq(R), L, c R:
        $has_seq_limit(a, L)
        =>:
            $has_seq_limit(fn(n N+) R{c * a(n)}, c * L)
    release thm seq_limit_scale(a, L, c)
"#;
const POWER: &str = r#"# Every fixed natural power preserves a real sequence limit.
thm checked_sequence_limit_natural_power:
    ? forall a seq(R), L R, p N:
        $has_seq_limit(a, L)
        =>:
            $has_seq_limit(fn(n N+) R{a(n) ^ p}, L ^ p)
    release thm seq_limit_power(a, L, p)
"#;
const NEGATIVE_SCALE: &str = r#"# A fixed negative scalar also scales the limit of a real sequence.
thm checked_sequence_limit_negative_scale_selected:
    ? forall a seq(R), L R:
        $has_seq_limit(a, L)
        =>:
            $has_seq_limit(fn(n N+) R{(-2) * a(n)}, (-2) * L)
    by thm seq_limit_scale(a, L, (-2)) => $has_seq_limit(fn(n N+) R{(-2) * a(n)}, (-2) * L)
"#;
const ZERO_POWER: &str = r#"# Select the limit law for the zeroth power, including sequences with zero terms.
thm checked_sequence_limit_zero_power_selected:
    ? forall a seq(R), L R:
        $has_seq_limit(a, L)
        =>:
            $has_seq_limit(fn(n N+) R{a(n) ^ 0}, L ^ 0)
    by thm seq_limit_power(a, L, 0) => $has_seq_limit(fn(n N+) R{a(n) ^ 0}, L ^ 0)
"#;

#[test]
fn sequence_map_replays_all_four_selected_operations_and_literal_profiles() {
    for (source, id) in [
        (NEG, BuiltinTheoremId::SequenceLimitNeg),
        (ABS, BuiltinTheoremId::SequenceLimitAbs),
        (SCALE, BuiltinTheoremId::SequenceLimitScale),
        (POWER, BuiltinTheoremId::SequenceLimitPower),
        (NEGATIVE_SCALE, BuiltinTheoremId::SequenceLimitScale),
        (ZERO_POWER, BuiltinTheoremId::SequenceLimitPower),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "map").unwrap();
        assert!(output.contains("Litex.sequenceLimitMap"));
        assert_eq!(output, compiler.compile_run(&run, "map").unwrap());
        let (mut run, _) = super::execute(source);
        let actual = if source == NEGATIVE_SCALE || source == ZERO_POWER {
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(named),
            )) = &run.statement_results[0]
            else {
                panic!()
            };
            let ExecDefThmBodyProof::Forall(body) = &named.body else {
                panic!()
            };
            super::by_theorem(&body.proof_steps[0])
                .builtin
                .as_ref()
                .unwrap()
                .theorem
        } else {
            invocation(&mut run).builtin.as_ref().unwrap().theorem
        };
        assert_eq!(actual, id);
    }
}
#[test]
fn sequence_map_retains_original_stage_order_stores_and_constructor_wd() {
    for source in [NEG, ABS, SCALE, POWER] {
        for change in [
            "args",
            "proof",
            "proof_order",
            "store",
            "store_order",
            "wd",
            "nested_wd",
            "types",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                "proof" => p.dom_proofs.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store" => p.dom_stores.clear(),
                "store_order" => p.dom_stores.swap(0, 1),
                "wd" => p.conclusions_wd.clear(),
                "nested_wd" => {
                    let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                    else {
                        panic!()
                    };
                    wd.as_detailed_mut()
                        .unwrap()
                        .well_defined_of_each_parameter
                        .clear();
                }
                _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
            }
            compiler
                .compile_run(&run, change)
                .expect_err("no map can replace missing or reordered original evidence");
        }
    }
}
#[test]
fn sequence_map_rejects_changed_body_limit_carriers_guards_and_capture() {
    for source in [NEG, ABS, SCALE, POWER] {
        for change in [
            "body", "limit", "domain", "output", "guards", "binder", "capture",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run).builtin.as_mut().unwrap();
            let guard = p.requirements[0].clone();
            let a = p.arguments[0].clone();
            let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(goal)) = &mut p.conclusions[0]
            else {
                panic!()
            };
            if change == "limit" {
                goal.value = super::number_object("1");
            } else {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut goal.sequence else {
                    panic!()
                };
                match change {
                    "body" => f.equal_to = Box::new(super::number_object("1")),
                    "domain" => {
                        f.body.set_bound_parameters.groups[0].param_type =
                            Box::new(Obj::StandardSet(StandardSet::N))
                    }
                    "output" => f.body.ret_set = Box::new(Obj::StandardSet(StandardSet::RPos)),
                    "guards" => {
                        let Fact::AtomicFact(guard) = guard else {
                            panic!()
                        };
                        f.body.dom_facts.push(QuantifierFreeFact::AtomicFact(guard));
                    }
                    "binder" => f.body.set_bound_parameters.groups[0].params.clear(),
                    "capture" => {
                        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = a else {
                            panic!()
                        };
                        f.body.set_bound_parameters.groups[0].params[0].id = id;
                    }
                    _ => panic!(),
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "a selected operation cannot certify another positive-index function or value",
            );
        }
    }
    for source in [SCALE, POWER] {
        let (mut run, compiler) = super::execute(source);
        let Fact::AtomicFact(AtomicFact::InFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[2]
        else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::RPos);
        compiler
            .compile_run(&run, "scalar_domain")
            .expect_err("real coefficients and natural exponents retain distinct exact carriers");
    }
}
#[test]
fn sequence_map_cannot_cite_future_mapped_limits_as_input_function_membership() {
    for source in [NEG, ABS, SCALE, POWER] {
        let (mut run, compiler) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                    cite_fact_id: future,
                    why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                },
            );
        compiler
            .compile_run(&run, "future")
            .expect_err("the mapped limit is not visible in the original function domain stage");
    }
}
