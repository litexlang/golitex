//! Builtin predicate definitions for ambient / `by def` search.
//!
//! Each positive builtin predicate expands to obligation facts (its definition).
//! Prove every obligation → accept the predicate.
//! One predicate ↔ one proof struct under `BuiltinPropDefinitionProof`.

use crate::ast::fact::{
    AndChainAtomicFact, AtomicFact, BijectiveFact, CoprimeFact, DvdFact, EqualFact,
    ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, InjectiveFact, IsChoiceFunctionForFact,
    LessEqualFact, NotEqualFact, OrFact, PlainExistFact, ProperSubsetFact,
    ProperSupersetFact, QuantifierFreeFact, SubsetFact, SupersetFact, SurjectiveFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{
    ArithmeticOperator, FnObj, FnObjHead, FunctionSpace, Gcd, IdentifierObj, IntegerOperator,
    Literal, Mod, Mul, Number, Obj, Range, SetFormer, StandardSet, StructAndFieldAccessObj,
};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    BuiltinBijectiveDefinitionProof, BuiltinCoprimeDefinitionProof, BuiltinDvdDefinitionProof,
    BuiltinInjectiveDefinitionProof, BuiltinIsChoiceFunctionForDefinitionProof,
    BuiltinPrimeDefinitionProof, BuiltinProperSubsetDefinitionProof,
    BuiltinProperSupersetDefinitionProof, BuiltinPropDefinitionProof,
    BuiltinSubsetDefinitionProof, BuiltinSupersetDefinitionProof,
    BuiltinSurjectiveDefinitionProof,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Try builtin definition expansion for dedicated AtomicFact variants.
    // Soft miss → Ok(None).
    pub(super) fn search_builtin_prop_definition_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        match fact {
            AtomicFact::SubsetFact(f) => self.prove_subset_by_definition(f, verify_state),
            AtomicFact::SupersetFact(f) => self.prove_superset_by_definition(f, verify_state),
            AtomicFact::ProperSubsetFact(f) => {
                self.prove_proper_subset_by_definition(f, verify_state)
            }
            AtomicFact::ProperSupersetFact(f) => {
                self.prove_proper_superset_by_definition(f, verify_state)
            }
            AtomicFact::InjectiveFact(f) => self.prove_injective_by_definition(f, verify_state),
            AtomicFact::SurjectiveFact(f) => self.prove_surjective_by_definition(f, verify_state),
            AtomicFact::BijectiveFact(f) => self.prove_bijective_by_definition(f, verify_state),
            AtomicFact::IsChoiceFunctionForFact(f) => {
                self.prove_is_choice_function_for_by_definition(f, verify_state)
            }
            AtomicFact::PrimeFact(f) => self.prove_prime_by_definition(f, verify_state),
            AtomicFact::CoprimeFact(f) => self.prove_coprime_by_definition(f, verify_state),
            AtomicFact::DvdFact(f) => self.prove_dvd_by_definition(f, verify_state),
            _ => Ok(None),
        }
    }

    // A $subset B  ⇔  forall x A: x $in B
    fn prove_subset_by_definition(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let x = self.fresh_internal_param();
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let forall = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![x], fact.left.clone()),
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: x_obj,
                    set: fact.right.clone(),
                    line_file: None,
                },
            ))],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![forall], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Subset(
            BuiltinSubsetDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // A $superset B  ⇔  forall x B: x $in A
    fn prove_superset_by_definition(
        &mut self,
        fact: &SupersetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let x = self.fresh_internal_param();
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let forall = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![x], fact.right.clone()),
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: x_obj,
                    set: fact.left.clone(),
                    line_file: None,
                },
            ))],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![forall], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Superset(
            BuiltinSupersetDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $proper_subset(A, B)  ⇔  A $subset B  and  A != B
    fn prove_proper_subset_by_definition(
        &mut self,
        fact: &ProperSubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let left = fact.left.clone();
        let right = fact.right.clone();
        let requirements = vec![
            Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: left.clone(),
                right: right.clone(),
                line_file: None,
            })),
            Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left,
                right,
                line_file: None,
            })),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::ProperSubset(
            BuiltinProperSubsetDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $proper_superset(A, B)  ⇔  B $subset A  and  A != B
    fn prove_proper_superset_by_definition(
        &mut self,
        fact: &ProperSupersetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let left = fact.left.clone();
        let right = fact.right.clone();
        let requirements = vec![
            Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: right.clone(),
                right: left.clone(),
                line_file: None,
            })),
            Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left,
                right,
                line_file: None,
            })),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::ProperSuperset(
            BuiltinProperSupersetDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $injective(A, B, f)  ⇔  forall x1, x2 A: f(x1)=f(x2) => x1=x2
    fn prove_injective_by_definition(
        &mut self,
        fact: &InjectiveFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let domain = fact.domain.clone();
        let function = fact.function.clone();
        let x1 = self.fresh_internal_param();
        let x2 = self.fresh_internal_param();
        let x1_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x1));
        let x2_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x2));
        let Some(fx1) = apply_fn_one_arg(&function, x1_obj.clone()) else {
            return Ok(None);
        };
        let Some(fx2) = apply_fn_one_arg(&function, x2_obj.clone()) else {
            return Ok(None);
        };
        let forall = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![x1, x2], domain),
            dom_facts: vec![Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fx1,
                right: fx2,
                line_file: None,
            }))],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(
                AtomicFact::EqualFact(EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: x1_obj,
                    right: x2_obj,
                    line_file: None,
                }),
            )],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![forall], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Injective(
            BuiltinInjectiveDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $surjective(A, B, f)  ⇔  forall y B: exist x A: y = f(x)
    fn prove_surjective_by_definition(
        &mut self,
        fact: &SurjectiveFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let domain = fact.domain.clone();
        let codomain = fact.codomain.clone();
        let function = fact.function.clone();
        let y = self.fresh_internal_param();
        let x = self.fresh_internal_param();
        let y_obj = Obj::Identifier(IdentifierObj::from_bound_name(&y));
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
        let Some(fx) = apply_fn_one_arg(&function, x_obj) else {
            return Ok(None);
        };
        let exist = PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![x], domain),
            facts: vec![QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: y_obj,
                    right: fx,
                    line_file: None,
                },
            ))],
            line_file: None,
        };
        let forall = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![y], codomain),
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(exist)],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![forall], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Surjective(
            BuiltinSurjectiveDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $bijective(A, B, f)  ⇔  $injective(A,B,f) and $surjective(A,B,f)
    fn prove_bijective_by_definition(
        &mut self,
        fact: &BijectiveFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let requirements = vec![
            Fact::AtomicFact(AtomicFact::InjectiveFact(InjectiveFact {
                fact_id: self.global_ids.allocate_fact_id(),
                domain: fact.domain.clone(),
                codomain: fact.codomain.clone(),
                function: fact.function.clone(),
                line_file: None,
            })),
            Fact::AtomicFact(AtomicFact::SurjectiveFact(SurjectiveFact {
                fact_id: self.global_ids.allocate_fact_id(),
                domain: fact.domain.clone(),
                codomain: fact.codomain.clone(),
                function: fact.function.clone(),
                line_file: None,
            })),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Bijective(
            BuiltinBijectiveDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $is_choice_function_for(I, S, g, f)  ⇔  forall alpha I: f(alpha) $in g(alpha)
    fn prove_is_choice_function_for_by_definition(
        &mut self,
        fact: &IsChoiceFunctionForFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let index = fact.index.clone();
        let family_fn = fact.family.clone();
        let choice_fn = fact.choice.clone();
        let alpha = self.fresh_internal_param();
        let alpha_obj = Obj::Identifier(IdentifierObj::from_bound_name(&alpha));
        let Some(f_alpha) = apply_fn_one_arg(&choice_fn, alpha_obj.clone()) else {
            return Ok(None);
        };
        let Some(g_alpha) = apply_fn_one_arg(&family_fn, alpha_obj) else {
            return Ok(None);
        };
        let forall = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![alpha], index),
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: f_alpha,
                    set: g_alpha,
                    line_file: None,
                },
            ))],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![forall], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::IsChoiceFunctionFor(
            BuiltinIsChoiceFunctionForDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $prime(p)  ⇔  2 <= p  and  forall d range(2, p): p % d != 0
    fn prove_prime_by_definition(
        &mut self,
        fact: &crate::ast::fact::PrimeFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let p = fact.value.clone();
        let two = number_literal("2");
        let zero = number_literal("0");
        let lower = Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: two.clone(),
            right: p.clone(),
            line_file: None,
        }));
        let d = self.fresh_internal_param();
        let d_obj = Obj::Identifier(IdentifierObj::from_bound_name(&d));
        let range = Obj::SetFormer(SetFormer::Range(Range {
            start: Box::new(two),
            end: Box::new(p.clone()),
        }));
        let rem = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
            left: Box::new(p),
            right: Box::new(d_obj),
        }));
        let trial = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![d], range),
            dom_facts: vec![],
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(
                AtomicFact::NotEqualFact(NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: rem,
                    right: zero,
                    line_file: None,
                }),
            )],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![lower, trial], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Prime(
            BuiltinPrimeDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $coprime(a, b)  ⇔  (a != 0 or b != 0)  and  gcd(a, b) = 1
    fn prove_coprime_by_definition(
        &mut self,
        fact: &CoprimeFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let a = fact.left.clone();
        let b = fact.right.clone();
        let zero = number_literal("0");
        let one = number_literal("1");
        let non_all_zero = Fact::OrFact(OrFact {
            fact_id: self.global_ids.allocate_fact_id(),
            facts: vec![
                AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: a.clone(),
                    right: zero.clone(),
                    line_file: None,
                })),
                AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: b.clone(),
                    right: zero,
                    line_file: None,
                })),
            ],
            line_file: None,
        });
        let gcd_one = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::IntegerOperator(IntegerOperator::Gcd(Gcd {
                left: Box::new(a),
                right: Box::new(b),
            })),
            right: one,
            line_file: None,
        }));
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![non_all_zero, gcd_one], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Coprime(
            BuiltinCoprimeDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    // $dvd(x, y)  ⇔  x % y = 0  and  exist a Z: x = a * y
    fn prove_dvd_by_definition(
        &mut self,
        fact: &DvdFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<BuiltinPropDefinitionProof>> {
        let x = fact.left.clone();
        let y = fact.right.clone();
        let zero = number_literal("0");
        let rem_zero = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                left: Box::new(x.clone()),
                right: Box::new(y.clone()),
            })),
            right: zero,
            line_file: None,
        }));
        let a = self.fresh_internal_param();
        let a_obj = Obj::Identifier(IdentifierObj::from_bound_name(&a));
        let multiple = Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: typed_obj_params(vec![a], Obj::StandardSet(StandardSet::Z)),
            facts: vec![QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: x,
                    right: Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                        left: Box::new(a_obj),
                        right: Box::new(y),
                    })),
                    line_file: None,
                },
            ))],
            line_file: None,
        });
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_definition_requirements(vec![rem_zero, multiple], verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(BuiltinPropDefinitionProof::Dvd(
            BuiltinDvdDefinitionProof {
                requirement_facts,
                proof_of_requirement_facts,
            },
        )))
    }

    fn verify_definition_requirements(
        &mut self,
        requirement_facts: Vec<Fact>,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(Vec<Fact>, Vec<VerifyFactResult>)>> {
        let mut proofs = Vec::with_capacity(requirement_facts.len());
        for requirement in &requirement_facts {
            let proof = self.verify_fact(requirement, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some((requirement_facts, proofs)))
    }
}

fn typed_obj_params(params: Vec<BoundName>, domain: Obj) -> TypedParameterList {
    TypedParameterList {
        groups: vec![TypedParameterGroup {
            params,
            param_type: ParamType::Obj(domain),
        }],
    }
}

fn number_literal(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: value.to_string(),
    }))
}

fn apply_fn_one_arg(f: &Obj, arg: Obj) -> Option<Obj> {
    match f {
        Obj::Identifier(id) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(id.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::FnObj(existing) => {
            let mut body = existing.body.clone();
            body.push(vec![Box::new(arg)]);
            Some(Obj::FnObj(FnObj {
                head: existing.head.clone(),
                body,
            }))
        }
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(af.clone()))),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(fa)) => {
            Some(Obj::FnObj(FnObj {
                head: Box::new(FnObjHead::FieldAccess(fa.clone())),
                body: vec![vec![Box::new(arg)]],
            }))
        }
        Obj::InstantiatedTemplateObj(t) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::InstantiatedTemplateObj(t.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        _ => None,
    }
}
