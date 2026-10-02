use crate::ast::fact::{AtomicFact, InFact};
use crate::ast::obj::{FnObjHead, FunctionSpace, Obj, StructAndFieldAccessObj};
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::runtime::{FactId, Runtime};
use crate::ast::obj::ProductShape;
use crate::execute::execute_fact_stmt::known_tuple::{literal_positive_usize, KnownTupleShapeProof};

pub enum AtomicExceptEqualityFactSearchProofByKnownSpecialProperty {
    InFact(InFactSearchProofByKnownSpecialProperty),
    IsTuple(TupleIsTupleKnownProof),
    TupleIndexBound(TupleIndexBoundKnownProof),
}

impl AtomicExceptEqualityFactSearchProofByKnownSpecialProperty {
    pub fn cite_property_fact_id(&self) -> Option<FactId> {
        match self {
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(p)) => {
                Some(p.cite_property_fact_id)
            }
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(p)) => {
                Some(p.cite_property_fact_id)
            }
            Self::InFact(InFactSearchProofByKnownSpecialProperty::TupleCoordinate(p)) => p.shape.cite_fact_id(),
            Self::IsTuple(p) => p.shape.cite_fact_id(),
            Self::TupleIndexBound(p) => p.shape.cite_fact_id(),
        }
    }
}

pub enum InFactSearchProofByKnownSpecialProperty {
    FnApplicationInCodomain(FnApplicationInCodomainKnownSpecialPropertyProof),
    FnApplicationInFnRange(FnApplicationInFnRangeKnownSpecialPropertyProof),
    TupleCoordinate(TupleCoordinateKnownProof),
}

pub struct TupleIsTupleKnownProof {
    pub shape: KnownTupleShapeProof,
}

pub struct TupleIndexBoundKnownProof {
    pub index: usize,
    pub shape: KnownTupleShapeProof,
}

pub struct TupleCoordinateKnownProof {
    pub index: usize,
    pub shape: KnownTupleShapeProof,
    pub carrier_equal: Box<EqualFactSearchedProof>,
}

pub struct FnApplicationInCodomainKnownSpecialPropertyProof {
    pub cite_property_fact_id: FactId,
    pub signature_return_matches: Vec<SignatureReturnMatchProof>,
}

pub struct SignatureReturnMatchProof {
    pub cite_signature_fact_id: FactId,
    pub return_set_match: EqualFactSearchedProof,
}

pub struct FnApplicationInFnRangeKnownSpecialPropertyProof {
    pub cite_property_fact_id: FactId,
    pub signature_matches: Vec<SignatureMatchProof>,
}

pub struct SignatureMatchProof {
    pub cite_signature_fact_id: FactId,
    pub signature_match: EqualFactSearchedProof,
}

impl Runtime {
    // The caller established WD. This leaf only matches registered rows in the
    // special-property index and cites stored equalities; it never verifies a new premise.
    pub(in crate::execute) fn search_atomic_except_equality_fact_proof_by_known_special_property(
        &mut self,
        fact: &AtomicFact,
    ) -> Option<AtomicExceptEqualityFactSearchProofByKnownSpecialProperty> {
        match fact {
            AtomicFact::EqualFact(_) => unreachable!("equality uses its own known search"),
            AtomicFact::InFact(fact) => self
                .search_in_fact_proof_by_known_special_property(fact)
                .map(AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact),
            AtomicFact::IsTupleFact(fact) => self.lookup_known_tuple_shape(&fact.set)
                .map(|shape| AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::IsTuple(
                    TupleIsTupleKnownProof { shape })),
            AtomicFact::LessEqualFact(fact) => {
                let Obj::ProductShape(ProductShape::TupleDim(dim)) = &fact.right else { return None };
                let index = literal_positive_usize(&fact.left)?;
                let shape = self.lookup_known_tuple_shape(dim.arg.as_ref())?;
                (index <= shape.dimension()).then_some(
                    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::TupleIndexBound(
                        TupleIndexBoundKnownProof { index, shape }))
            }
            AtomicFact::NormalAtomicFact(_)
            | AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
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

    pub(in crate::execute) fn search_in_fact_proof_by_known_special_property(
        &mut self,
        fact: &InFact,
    ) -> Option<InFactSearchProofByKnownSpecialProperty> {
        if let Obj::ProductShape(ProductShape::ObjAtIndex(at)) = &fact.element {
            let index = literal_positive_usize(at.index.as_ref())?;
            let shape = self.lookup_known_tuple_shape(at.obj.as_ref())?;
            let carrier = shape.cart()?.args.get(index - 1)?.as_ref().clone();
            let carrier_equal = self.lookup_known_obj_equality(&carrier, &fact.set)?;
            return Some(InFactSearchProofByKnownSpecialProperty::TupleCoordinate(
                TupleCoordinateKnownProof { index, shape, carrier_equal: Box::new(carrier_equal) }));
        }
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
            let Some(signature) = property.function_signature() else {
                continue;
            };
            let definition_id = property.fact_id();
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
                    if self
                        .applied_fn_set_return_set(application, &candidate)
                        .is_none()
                    {
                        continue;
                    }
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
                            cite_property_fact_id: definition_id,
                            signature_matches: matches,
                        },
                    ),
                );
            }
            let Some(applied_return) = self.applied_fn_set_return_set(application, &signature) else {
                continue;
            };
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
                            cite_property_fact_id: definition_id,
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
    ) -> Vec<SpecialProperty> {
        let key = obj.ir();
        let mut properties = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(rows) = env.special_properties.get(&key) {
                properties.extend(rows.iter().cloned());
            }
        }
        properties
    }
}
