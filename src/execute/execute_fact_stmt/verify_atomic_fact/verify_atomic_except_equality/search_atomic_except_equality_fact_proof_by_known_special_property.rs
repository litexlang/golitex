use crate::ast::fact::{AtomicFact, InFact};
use crate::ast::obj::{FnObjHead, FunctionSpace, Obj, StructAndFieldAccessObj};
use crate::exec_env::SpecialObjectPropertyByDefinition;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::runtime::{FactId, Runtime};

pub enum AtomicExceptEqualityFactSearchProofByKnownSpecialProperty {
    InFact(InFactSearchProofByKnownSpecialProperty),
}

impl AtomicExceptEqualityFactSearchProofByKnownSpecialProperty {
    pub fn cite_definition_fact_id(&self) -> FactId {
        match self {
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(p)) => {
                p.cite_definition_fact_id
            }
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(p)) => {
                p.cite_definition_fact_id
            }
        }
    }
}

pub enum InFactSearchProofByKnownSpecialProperty {
    FnApplicationInCodomain(FnApplicationInCodomainKnownSpecialPropertyProof),
    FnApplicationInFnRange(FnApplicationInFnRangeKnownSpecialPropertyProof),
}

pub struct FnApplicationInCodomainKnownSpecialPropertyProof {
    pub cite_definition_fact_id: FactId,
    pub signature_return_matches: Vec<SignatureReturnMatchProof>,
}

pub struct SignatureReturnMatchProof {
    pub cite_signature_fact_id: FactId,
    pub return_set_match: EqualFactSearchedProof,
}

pub struct FnApplicationInFnRangeKnownSpecialPropertyProof {
    pub cite_definition_fact_id: FactId,
    pub signature_matches: Vec<SignatureMatchProof>,
}

pub struct SignatureMatchProof {
    pub cite_signature_fact_id: FactId,
    pub signature_match: EqualFactSearchedProof,
}

impl Runtime {
    // The caller established WD. This leaf only matches definition-time rows
    // and cites stored equalities; it never verifies a new premise.
    pub(in crate::execute) fn search_atomic_except_equality_fact_proof_by_known_special_property(
        &mut self,
        fact: &AtomicFact,
    ) -> Option<AtomicExceptEqualityFactSearchProofByKnownSpecialProperty> {
        match fact {
            AtomicFact::EqualFact(_) => unreachable!("equality uses its own known search"),
            AtomicFact::InFact(fact) => self
                .search_in_fact_proof_by_known_special_property(fact)
                .map(AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact),
            AtomicFact::NormalAtomicFact(_)
            | AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_)
            | AtomicFact::NotEqualFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::IsSetFact(_)
            | AtomicFact::IsNonemptySetFact(_)
            | AtomicFact::IsFiniteSetFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::IsCartFact(_)
            | AtomicFact::IsTupleFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
            | AtomicFact::SubsetFact(_)
            | AtomicFact::SupersetFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
            | AtomicFact::ProperSubsetFact(_)
            | AtomicFact::ProperSupersetFact(_)
            | AtomicFact::NotProperSubsetFact(_)
            | AtomicFact::NotProperSupersetFact(_)
            | AtomicFact::PrimeFact(_)
            | AtomicFact::NotPrimeFact(_)
            | AtomicFact::CoprimeFact(_)
            | AtomicFact::NotCoprimeFact(_)
            | AtomicFact::DvdFact(_)
            | AtomicFact::NotDvdFact(_)
            | AtomicFact::InjectiveFact(_)
            | AtomicFact::NotInjectiveFact(_)
            | AtomicFact::SurjectiveFact(_)
            | AtomicFact::NotSurjectiveFact(_)
            | AtomicFact::BijectiveFact(_)
            | AtomicFact::NotBijectiveFact(_)
            | AtomicFact::IsChoiceFunctionForFact(_)
            | AtomicFact::NotIsChoiceFunctionForFact(_) => None,
        }
    }

    fn search_in_fact_proof_by_known_special_property(
        &mut self,
        fact: &InFact,
    ) -> Option<InFactSearchProofByKnownSpecialProperty> {
        let Obj::FnObj(application) = &fact.element else {
            return None;
        };
        if application.body.is_empty() {
            return None;
        }
        let head = match application.head.as_ref() {
            FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
            FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
            FnObjHead::FieldAccess(access) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()))
            }
            FnObjHead::AnonymousFnLiteral(_) => return None,
        };
        let properties = self.known_special_properties_of(&head);
        for property in properties {
            let SpecialObjectPropertyByDefinition::InFunctionSet((signature, definition_id)) =
                property
            else {
                continue;
            };
            if let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &fact.set {
                if head.ir() != range.function.ir() || application.body.len() != 1 {
                    continue;
                }
                let arity: usize = signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .map(|group| group.params.len())
                    .sum();
                if application.body[0].len() != arity {
                    continue;
                }
                let signature_obj = Obj::FunctionSpace(FunctionSpace::FnSet(signature));
                let mut matches = Vec::new();
                for (candidate, id) in self.collect_in_function_set_candidates(&head) {
                    let candidate_obj = Obj::FunctionSpace(FunctionSpace::FnSet(candidate));
                    let Some(proof) =
                        self.lookup_known_obj_equality(&candidate_obj, &signature_obj)
                    else {
                        return None;
                    };
                    matches.push(SignatureMatchProof {
                        cite_signature_fact_id: id,
                        signature_match: proof,
                    });
                }
                return Some(
                    InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(
                        FnApplicationInFnRangeKnownSpecialPropertyProof {
                            cite_definition_fact_id: definition_id,
                            signature_matches: matches,
                        },
                    ),
                );
            }
            let applied_return = self.applied_fn_set_return_set(application, &signature)?;
            self.lookup_known_obj_equality(&applied_return, &fact.set)?;
            // Cached WD cites the application, not its selected signature. All
            // signatures that could supply that WD must have the target return.
            // This preserves cache behavior without rerunning domain proof search.
            let mut matches = Vec::new();
            for (candidate, id) in self.collect_in_function_set_candidates(&head) {
                let Some(ret) = self.applied_fn_set_return_set(application, &candidate) else {
                    continue;
                };
                let Some(proof) = self.lookup_known_obj_equality(&ret, &fact.set) else {
                    return None;
                };
                matches.push(SignatureReturnMatchProof {
                    cite_signature_fact_id: id,
                    return_set_match: proof,
                });
            }
            if !matches.is_empty() {
                return Some(
                    InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(
                        FnApplicationInCodomainKnownSpecialPropertyProof {
                            cite_definition_fact_id: definition_id,
                            signature_return_matches: matches,
                        },
                    ),
                );
            }
        }
        None
    }

    pub(in crate::execute) fn known_special_properties_of(
        &self,
        obj: &Obj,
    ) -> Vec<SpecialObjectPropertyByDefinition> {
        let key = obj.ir();
        let mut properties = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(rows) = env.special_object_properties_by_def.get(&key) {
                properties.extend(rows.iter().cloned());
            }
        }
        properties
    }
}
