use super::known_fn_standard_return::FnApplicationInStandardSupersetProof;
use crate::ast::fact::{AtomicFact, InFact};
use crate::ast::obj::{FnObjHead, FnSet, FunctionSpace, InstantiatedTemplateObj, IteratedOperator, Obj, StandardSet, StructAndFieldAccessObj};
use super::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::proper_subsets_in_membership_proof_order;
use super::result::AtomicExceptEqualityFactKnownProof;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
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
            Self::InFact(InFactSearchProofByKnownSpecialProperty::StandardNumericSuperset(p)) => p.source_membership_proof.cite_fact_id(),
            Self::InFact(InFactSearchProofByKnownSpecialProperty::AnonymousFnApplicationInCodomain(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FieldApplicationInDeclaredCodomain(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::TemplateApplicationInDeclaredCodomain(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FieldInDeclaredSet(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FoldInCarrier(p)) => match &p.operation_signature {
                FoldOperationSignatureProof::Literal(_) => None,
                FoldOperationSignatureProof::Known(p)=>p.cite_fact_id(),
            },
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(p)) => {
                p.signature_returns.first().map(|p| p.cite_signature_fact_id)
            }
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
    StandardNumericSuperset(StandardNumericSupersetKnownProof),
    FoldInCarrier(FoldInCarrierProof),
    AnonymousFnApplicationInCodomain(AnonymousFnApplicationInCodomainProof),
    FieldApplicationInDeclaredCodomain(FieldApplicationInDeclaredCodomainProof),
    TemplateApplicationInDeclaredCodomain(TemplateApplicationInDeclaredCodomainProof),
    FieldInDeclaredSet(FieldInDeclaredSetProof),
    FnApplicationInCodomain(FnApplicationInCodomainKnownSpecialPropertyProof),
    FnApplicationInStandardSuperset(FnApplicationInStandardSupersetProof),
    FnApplicationInFnRange(FnApplicationInFnRangeKnownSpecialPropertyProof),
    TupleCoordinate(TupleCoordinateKnownProof),
}

pub struct StandardNumericSupersetKnownProof {
    pub source_set: StandardSet,
    pub target_set: StandardSet,
    pub source_membership_proof: AtomicExceptEqualityFactKnownProof,
}
pub struct FoldInCarrierProof {
    pub operation_signature:FoldOperationSignatureProof,
    pub carrier:Obj,
    pub carrier_match:Box<EqualFactSearchedProof>,
}
pub enum FoldOperationSignatureProof {
    Literal(FnSet),
    Known(super::result::AtomicExceptEqualityFactKnownProof),
}
pub struct AnonymousFnApplicationInCodomainProof {
    pub signature:FnSet,
    pub applied_return_set:Obj,
    pub return_set_match:Box<EqualFactSearchedProof>,
}

// The enclosing application WD carries the receiver/field and domain checks.
// Cached WD does not identify which signature was selected, so every visible
// alternative must agree on the instantiated return carrier as well.
pub struct FieldApplicationInDeclaredCodomainProof {
    pub declared_signature: FnSet,
    pub applied_return_set: Obj,
    pub return_set_match: EqualFactSearchedProof,
    pub alternative_signature_matches: Vec<SignatureReturnMatchProof>,
}

pub struct TemplateApplicationInDeclaredCodomainProof {
    pub instance: InstantiatedTemplateObj,
    pub function_equal: KnownEqualityPathProof,
    pub declared_signature: FnSet,
    pub applied_return_set: Obj,
    pub return_set_match: EqualFactSearchedProof,
    pub alternative_signature_matches: Vec<SignatureReturnMatchProof>,
    pub alternative_template_signature_matches: Vec<TemplateSignatureReturnMatchProof>,
}

pub struct TemplateSignatureReturnMatchProof {
    pub instance: InstantiatedTemplateObj,
    pub function_equal: KnownEqualityPathProof,
    pub return_set_match: EqualFactSearchedProof,
}

pub struct FieldInDeclaredSetProof {
    pub declared_set: Obj,
    pub set_match: EqualFactSearchedProof,
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
    // special-property index or a stored standard-carrier membership, and cites
    // stored equalities; it never verifies a new premise.
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
        // A stored numeric carrier supplies its intrinsic standard supersets.
        // Example: known x in Z establishes x in R without a new child search.
        if let Obj::StandardSet(target) = &fact.set {
            for source_set in proper_subsets_in_membership_proof_order(target) {
                let source = AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: fact.element.clone(),
                    set: Obj::StandardSet(source_set.clone()),
                    line_file: fact.line_file.clone(),
                });
                if let Some(source_membership_proof) = self.lookup_known_atomic_premise(source) {
                    return Some(InFactSearchProofByKnownSpecialProperty::StandardNumericSuperset(
                        StandardNumericSupersetKnownProof {
                            source_set,
                            target_set: target.clone(),
                            source_membership_proof,
                        },
                    ));
                }
            }
        }
        // Field WD selected a definition-owned struct carrier. Its instantiated
        // field type also applies in read-only nested WD, before explicit release.
        if let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) = &fact.element {
            if let Some(declared_set) = self.resolve_field_access_field_type(access) {
                if let Some(set_match) = self.lookup_known_obj_equality(&declared_set, &fact.set) {
                    return Some(InFactSearchProofByKnownSpecialProperty::FieldInDeclaredSet(
                        FieldInDeclaredSetProof { declared_set, set_match },
                    ));
                }
            }
        }
        // Fold WD already checked homogeneous closure, seed, and iterand.
        // Read the operation's declared carrier without reopening builtin
        // search. This also permits a fold as the argument of a typed op.
        let operation=match &fact.element {
            Obj::IteratedOperator(IteratedOperator::Reduce(r))=>Some(&*r.op),
            Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(r))=>Some(&*r.op),_=>None,
        };
        if let Some(operation)=operation {
            let signature=self.resolve_callable_fn_set(operation)?;
            let carrier=*signature.ret_set.clone();
            let carrier_match=self.lookup_known_obj_equality(&carrier,&fact.set)?;
            let operation_signature=if matches!(operation,Obj::FunctionSpace(FunctionSpace::AnonymousFn(_))) {
                FoldOperationSignatureProof::Literal(signature)
            } else {
                let membership=AtomicFact::InFact(InFact {fact_id:self.global_ids.allocate_fact_id(),element:operation.clone(),set:Obj::FunctionSpace(FunctionSpace::FnSet(signature)),line_file:None});
                FoldOperationSignatureProof::Known(self.lookup_known_atomic_premise(membership)?)
            };
            return Some(InFactSearchProofByKnownSpecialProperty::FoldInCarrier(FoldInCarrierProof {operation_signature,carrier,carrier_match:Box::new(carrier_match)}));
        }
        if let Obj::ProductShape(ProductShape::ObjAtIndex(at)) = &fact.element {
            let index = literal_positive_usize(at.index.as_ref())?;
            let shape = self.lookup_known_tuple_shape(at.obj.as_ref())?;
            let carrier = shape.cart()?.args.get(index - 1)?.as_ref().clone();
            let carrier_equal = self.lookup_known_obj_equality(&carrier, &fact.set)?;
            return Some(InFactSearchProofByKnownSpecialProperty::TupleCoordinate(
                TupleCoordinateKnownProof { index, shape, carrier_equal: Box::new(carrier_equal) }));
        }
        if let Some(proof) = self.known_fn_application_standard_superset(fact) {
            return Some(InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(proof));
        }
        let Obj::FnObj(application) = &fact.element else {
            return None;
        };
        if application.body.is_empty() {
            return None;
        }
        let template_head = crate::execute::execute_fact_stmt::known_tuple::tuple_function_head(application);
        let template_peers = equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(), &template_head,
        );
        for (peer, path) in &template_peers {
            let Obj::InstantiatedTemplateObj(instance) = peer else { continue; };
            let Some(signature) = self.instantiated_template_function_signature(instance) else { continue; };
            let Some(applied_return_set) = self.applied_fn_set_return_set(application, &signature) else { continue; };
            let Some(return_set_match) = self.lookup_known_obj_equality(&applied_return_set, &fact.set) else { continue; };
            let alternative_signature_matches = self.known_alternative_signature_returns(application, &template_head, &fact.set)?;
            let mut alternative_template_signature_matches = Vec::new();
            for (alternative, alternative_path) in &template_peers {
                let Obj::InstantiatedTemplateObj(alternative) = alternative else { continue; };
                let Some(signature) = self.instantiated_template_function_signature(alternative) else { continue; };
                let Some(ret) = self.applied_fn_set_return_set(application, &signature) else { continue; };
                let return_set_match = self.lookup_known_obj_equality(&ret, &fact.set)?;
                alternative_template_signature_matches.push(TemplateSignatureReturnMatchProof {
                    instance: alternative.clone(), function_equal: KnownEqualityPathProof::new(alternative_path.clone()), return_set_match,
                });
            }
            return Some(InFactSearchProofByKnownSpecialProperty::TemplateApplicationInDeclaredCodomain(
                TemplateApplicationInDeclaredCodomainProof {
                    instance: instance.clone(), function_equal: KnownEqualityPathProof::new(path.clone()),
                    declared_signature: signature, applied_return_set, return_set_match,
                    alternative_signature_matches, alternative_template_signature_matches,
                },
            ));
        }
        if let FnObjHead::FieldAccess(access) = application.head.as_ref() {
            if let Some(Obj::FunctionSpace(FunctionSpace::FnSet(signature))) =
                self.resolve_field_access_field_type(access)
            {
                if let Some(applied_return_set) = self.applied_fn_set_return_set(application, &signature) {
                    if let Some(return_set_match) = self.lookup_known_obj_equality(&applied_return_set, &fact.set) {
                        let head = Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()));
                        let alternative_signature_matches = self.known_alternative_signature_returns(application, &head, &fact.set)?;
                        return Some(InFactSearchProofByKnownSpecialProperty::FieldApplicationInDeclaredCodomain(
                            FieldApplicationInDeclaredCodomainProof {
                                declared_signature: signature,
                                applied_return_set,
                                return_set_match,
                                alternative_signature_matches,
                            },
                        ));
                    }
                }
            }
        }
        let head = match application.head.as_ref() {
            FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
            FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
            FnObjHead::FieldAccess(access) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()))
            }
            // Anonymous functions carry their signature intrinsically. The
            // caller checked the body, arguments and domain in application WD;
            // this leaf reads that signature and cites only stored equality.
            // Example: fn(a,b R) R {a+b}(x,y) $in R, including nested calls.
            FnObjHead::AnonymousFnLiteral(anonymous) => {
                let applied_return_set=self.applied_fn_set_return_set(application,&anonymous.body)?;
                let return_set_match=self.lookup_known_obj_equality(&applied_return_set,&fact.set)?;
                return Some(InFactSearchProofByKnownSpecialProperty::AnonymousFnApplicationInCodomain(AnonymousFnApplicationInCodomainProof {
                    signature:anonymous.body.clone(),applied_return_set,return_set_match:Box::new(return_set_match),
                }));
            },
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

    fn known_alternative_signature_returns(
        &mut self,
        application: &crate::ast::obj::FnObj,
        head: &Obj,
        target: &Obj,
    ) -> Option<Vec<SignatureReturnMatchProof>> {
        let mut matches = Vec::new();
        for (candidate, id) in self.collect_in_function_set_candidates(head) {
            let Some(ret) = self.applied_fn_set_return_set(application, &candidate) else { continue; };
            let return_set_match = self.lookup_known_obj_equality(&ret, target)?;
            matches.push(SignatureReturnMatchProof { cite_signature_fact_id: id, return_set_match });
        }
        Some(matches)
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

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/known_numeric_carrier/tests.rs"]
mod known_numeric_carrier_tests;
