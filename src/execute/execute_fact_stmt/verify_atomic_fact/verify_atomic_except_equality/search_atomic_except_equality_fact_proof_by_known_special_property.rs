use super::known_fn_standard_return::FnApplicationInStandardSupersetProof;
use crate::ast::fact::{AtomicFact, EqualFact, InFact, LessEqualFact};
use crate::ast::obj::{FnObjHead, FnSet, FunctionSpace, InstantiatedTemplateObj, IteratedOperator, Obj, StandardSet, StructAndFieldAccessObj};
use super::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::proper_subsets_in_membership_proof_order;
use super::result::AtomicExceptEqualityFactKnownProof;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::runtime::{FactId, Runtime};
use crate::ast::obj::{ProductShape, Literal, Number};
use crate::execute::execute_fact_stmt::known_tuple::{literal_positive_usize, KnownTupleShapeProof};

pub enum AtomicExceptEqualityFactSearchProofByKnownSpecialProperty {
    InFact(InFactSearchProofByKnownSpecialProperty),



}

impl AtomicExceptEqualityFactSearchProofByKnownSpecialProperty {
    pub fn cite_property_fact_id(&self) -> Option<FactId> {
        match self {
            Self::InFact(InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(p)) => p.positive_order.cite_fact_id(),
            Self::InFact(InFactSearchProofByKnownSpecialProperty::StandardNumericSuperset(p)) => p.source_membership_proof.cite_fact_id(),
            Self::InFact(InFactSearchProofByKnownSpecialProperty::AnonymousFnApplicationInCodomain(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::FieldApplicationInDeclaredCodomain(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::TemplateApplicationInDeclaredCodomain(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::TemplateFunctionInDeclaredFnSet(_)) => None,
            Self::InFact(InFactSearchProofByKnownSpecialProperty::AnonymousFnInFiniteSeq(_)) => None,
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
            Self::InFact(InFactSearchProofByKnownSpecialProperty::HomogeneousTupleCoordinate(p)) => p.shape.cite_fact_id(),
        }
    }
}

pub enum InFactSearchProofByKnownSpecialProperty {
    PositiveRealFromKnownStrictOrder(PositiveRealFromKnownStrictOrderProof),
    StandardNumericSuperset(StandardNumericSupersetKnownProof),
    FoldInCarrier(FoldInCarrierProof),
    AnonymousFnApplicationInCodomain(AnonymousFnApplicationInCodomainProof),
    FieldApplicationInDeclaredCodomain(FieldApplicationInDeclaredCodomainProof),
    TemplateApplicationInDeclaredCodomain(TemplateApplicationInDeclaredCodomainProof),
    TemplateFunctionInDeclaredFnSet(TemplateFunctionInDeclaredFnSetProof),
    AnonymousFnInFiniteSeq(AnonymousFnInFiniteSeqProof),
    FieldInDeclaredSet(FieldInDeclaredSetProof),
    FnApplicationInCodomain(FnApplicationInCodomainKnownSpecialPropertyProof),
    FnApplicationInStandardSuperset(FnApplicationInStandardSupersetProof),
    FnApplicationInFnRange(FnApplicationInFnRangeKnownSpecialPropertyProof),
    TupleCoordinate(TupleCoordinateKnownProof),
    HomogeneousTupleCoordinate(HomogeneousTupleCoordinateKnownProof),
}

// The enclosing atomic WD has checked every template argument and guard.
// The declared complete FnSet must match the target by identity/alpha only;
// no domain widening, return coercion, or equality-graph search is performed.
pub struct TemplateFunctionInDeclaredFnSetProof {
    pub instance: InstantiatedTemplateObj,
    pub declared_signature: FnSet,
    pub signature_match: EqualFactSearchedProof,
}

// Object WD checks the literal's body and the finite-sequence carrier first.
// The complete declared signature must then match by alpha identity only.
pub struct AnonymousFnInFiniteSeqProof {
    pub declared_signature: FnSet,
    pub signature_match: EqualFactSearchedProof,
}

pub struct PositiveRealFromKnownStrictOrderProof { pub positive_order: AtomicExceptEqualityFactKnownProof }

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


pub struct TupleCoordinateKnownProof {
    pub index: usize,
    pub shape: KnownTupleShapeProof,
    pub carrier_equal: Box<EqualFactSearchedProof>,
}

// Ordinary call WD supplies the index positivity and upper bound. Every factor
// must match the target using only stored equality; no new premise search.
pub struct HomogeneousTupleCoordinateKnownProof {
    pub shape: KnownTupleShapeProof,
    pub carrier_equals: Vec<EqualFactSearchedProof>,
}

pub struct FnApplicationInCodomainKnownSpecialPropertyProof {
    pub cite_property_fact_id: FactId,
    pub function_equal: KnownEqualityPathProof,
    pub signature_uses: Vec<SignatureCodomainUseProof>,
}

pub enum SignatureCodomainUseProof {
    ReturnSetMatch(SignatureReturnMatchProof),
    SameCallDomains {
        cite_signature_fact_id: FactId,
        function_equal: KnownEqualityPathProof,
        domains: crate::execute::execute_fact_stmt::function_domain::FunctionCallDomainsAlphaMatchProof,
    },
}

pub struct SignatureReturnMatchProof {
    pub cite_signature_fact_id: FactId,
    pub return_set_match: EqualFactSearchedProof,
}

pub struct FnApplicationInFnRangeKnownSpecialPropertyProof {
    pub cite_property_fact_id: FactId,
    pub function_equal: KnownEqualityPathProof,
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
            AtomicFact::NormalAtomicFact(_)
            | AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::LessEqualFact(_)
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
        // A stored strict real comparison already owns its endpoint domains.
        // This is a fixed refinement consumer, with no recursive proof search.
        if matches!(fact.set,Obj::StandardSet(StandardSet::RPos)) {
            let zero=Obj::Literal(Literal::Number(Number::new("0".into())));
            if let Some(positive_order)=self.known_less_proof(&zero,&fact.element)
                .or_else(||self.known_greater_proof(&fact.element,&zero)) {
                return Some(InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(PositiveRealFromKnownStrictOrderProof::new(positive_order)));
            }
        }
        if let (Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)),
                Obj::SetFormer(crate::ast::obj::SetFormer::FiniteSeqSet(_))) =
            (&fact.element, &fact.set)
        {
            let target_signature = self.function_space_signature(&fact.set)?;
            let comparison = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::FunctionSpace(FunctionSpace::FnSet(function.body.clone())),
                right: Obj::FunctionSpace(FunctionSpace::FnSet(target_signature)),
                line_file: fact.line_file.clone(),
            };
            if let Some(signature_match) = search_equal_fact_proof_by_they_are_the_same(&comparison) {
                return Some(InFactSearchProofByKnownSpecialProperty::AnonymousFnInFiniteSeq(
                    AnonymousFnInFiniteSeqProof {
                        declared_signature: function.body.clone(),
                        signature_match: signature_match.into(),
                    },
                ));
            }
        }
        if let (Obj::InstantiatedTemplateObj(instance), Obj::FunctionSpace(FunctionSpace::FnSet(_))) =
            (&fact.element, &fact.set)
        {
            if let Some(declared_signature) = self.instantiated_template_function_signature(instance) {
                let comparison = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: Obj::FunctionSpace(FunctionSpace::FnSet(declared_signature.clone())),
                    right: fact.set.clone(),
                    line_file: fact.line_file.clone(),
                };
                if let Some(signature_match) = search_equal_fact_proof_by_they_are_the_same(&comparison) {
                    return Some(InFactSearchProofByKnownSpecialProperty::TemplateFunctionInDeclaredFnSet(
                        TemplateFunctionInDeclaredFnSetProof {
                            instance: instance.clone(), declared_signature,
                            signature_match: signature_match.into(),
                        },
                    ));
                }
            }
        }
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
                if let Some(set_match) = self.lookup_exact_property_obj_equality(&declared_set, &fact.set) {
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
            let carrier_match=self.lookup_exact_property_obj_equality(&carrier,&fact.set)?;
            let operation_signature=if matches!(operation,Obj::FunctionSpace(FunctionSpace::AnonymousFn(_))) {
                FoldOperationSignatureProof::Literal(signature)
            } else {
                let membership=AtomicFact::InFact(InFact {fact_id:self.global_ids.allocate_fact_id(),element:operation.clone(),set:Obj::FunctionSpace(FunctionSpace::FnSet(signature)),line_file:None});
                FoldOperationSignatureProof::Known(self.lookup_known_atomic_premise(membership)?)
            };
            return Some(InFactSearchProofByKnownSpecialProperty::FoldInCarrier(FoldInCarrierProof {operation_signature,carrier,carrier_match:Box::new(carrier_match)}));
        }
        // Ordinary call WD has already established that this last input lies
        // in the receiver's complete domain. Match its actual Cartesian member
        // source; a miss must fall through to the general codomain readers.
        if let Obj::FnObj(application) = &fact.element {
            if let Some(receiver) = self.finite_function_application_receiver(application) {
                if let Some(shape) = self.lookup_known_tuple_shape(&receiver) {
                    if let Some(cart) = shape.cart() {
                        let argument = application.body.last().unwrap()[0].as_ref();
                        if let Some(index) = literal_positive_usize(argument) {
                            if let Some(carrier) = cart.args.get(index - 1) {
                                if let Some(carrier_equal) = self.lookup_exact_property_obj_equality(carrier, &fact.set) {
                                    return Some(InFactSearchProofByKnownSpecialProperty::TupleCoordinate(
                                        TupleCoordinateKnownProof { index, shape, carrier_equal: Box::new(carrier_equal) }));
                                }
                            }
                        }
                        if !cart.args.is_empty() {
                            let carrier_equals: Option<Vec<_>> = cart.args.iter()
                                .map(|carrier| self.lookup_exact_property_obj_equality(carrier, &fact.set)).collect();
                            if let Some(carrier_equals) = carrier_equals {
                                return Some(InFactSearchProofByKnownSpecialProperty::HomogeneousTupleCoordinate(
                                    HomogeneousTupleCoordinateKnownProof { shape, carrier_equals }));
                            }
                        }
                    }
                }
            }
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
        let template_peers = self.exact_property_object_values(&template_head);
        for (peer, path) in &template_peers {
            let Obj::InstantiatedTemplateObj(instance) = peer else { continue; };
            let Some(signature) = self.instantiated_template_function_signature(instance) else { continue; };
            let Some(applied_return_set) = self.applied_fn_set_return_set(application, &signature) else { continue; };
            let Some(return_set_match) = self.lookup_exact_property_obj_equality(&applied_return_set, &fact.set) else { continue; };
            let alternative_signature_matches = self.known_alternative_signature_returns(application, &template_head, &fact.set)?;
            let mut alternative_template_signature_matches = Vec::new();
            for (alternative, alternative_path) in &template_peers {
                let Obj::InstantiatedTemplateObj(alternative) = alternative else { continue; };
                let Some(signature) = self.instantiated_template_function_signature(alternative) else { continue; };
                let Some(ret) = self.applied_fn_set_return_set(application, &signature) else { continue; };
                let return_set_match = self.lookup_exact_property_obj_equality(&ret, &fact.set)?;
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
            if let Some(field_type) = self.resolve_field_access_field_type(access) {
                if let Some(signature) = self.function_space_signature(&field_type) {
                if let Some(applied_return_set) = self.applied_fn_set_return_set(application, &signature) {
                    if let Some(return_set_match) = self.lookup_exact_property_obj_equality(&applied_return_set, &fact.set) {
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
        }
        let head = match application.head.as_ref() {
            FnObjHead::Object(obj) => obj.as_ref().clone(),
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
                let return_set_match=self.lookup_exact_property_obj_equality(&applied_return_set,&fact.set)?;
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
            let Some(subject) = property.function_subject() else { continue; };
            let Some(function_path) = self.exact_property_equality_path(&head, subject) else { continue; };
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
                        self.lookup_exact_property_obj_equality(&candidate_obj, &signature_obj)
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
                            function_equal: KnownEqualityPathProof::new(function_path),
                            signature_matches: matches,
                        },
                    ),
                );
            }
            let Some(applied_return) = self.applied_fn_set_return_set(application, &signature) else {
                continue;
            };
            if self.lookup_exact_property_obj_equality(&applied_return, &fact.set).is_none() {
                continue;
            }
            // Cached WD cites the application, not its selected signature. All
            // signatures that could supply that WD must either have the target
            // return or the same complete call domains as this selected source.
            // Thus a weaker return upper bound cannot erase a stronger one,
            // while a different or missing guard never inherits cached WD.
            let mut matches = Vec::new();
            for (candidate, id) in self.collect_in_function_set_candidates(&head) {
                let Some(ret) = self.applied_fn_set_return_set(application, &candidate) else {
                    continue;
                };
                if let Some(proof) = self.lookup_exact_property_obj_equality(&ret, &fact.set) {
                    matches.push(SignatureCodomainUseProof::ReturnSetMatch(SignatureReturnMatchProof {
                        cite_signature_fact_id: id, return_set_match: proof,
                    }));
                } else if let Some(domains) = self.function_call_domains_alpha_match(application, &signature, &candidate) {
                    let property = match self.fact_by_id_in_stack(id) {
                        Some(crate::ast::fact::Fact::AtomicFact(AtomicFact::InFact(fact))) => SpecialProperty::Membership(fact.clone()),
                        Some(crate::ast::fact::Fact::AtomicFact(AtomicFact::EqualFact(fact))) => SpecialProperty::Equality(fact.clone()),
                        _ => return None,
                    };
                    let path = self.exact_property_equality_path(&head, property.function_subject()?)?;
                    matches.push(SignatureCodomainUseProof::SameCallDomains {
                        cite_signature_fact_id: id, function_equal: KnownEqualityPathProof::new(path), domains,
                    });
                } else {
                    return None;
                }
            }
            if !matches.is_empty() {
                return Some(
                    InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(
                        FnApplicationInCodomainKnownSpecialPropertyProof {
                            cite_property_fact_id: definition_id,
                            function_equal: KnownEqualityPathProof::new(function_path),
                            signature_uses: matches,
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
            let return_set_match = self.lookup_exact_property_obj_equality(&ret, target)?;
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

#[cfg(test)]
mod template_function_declared_type_tests {
    use crate::launch_command::{LaunchCommand, OutputLanguage};
    use crate::runtime::Runtime;

    fn runtime() -> Runtime {
        Runtime::new(LaunchCommand::Eval {
            code: String::new(), session: false, strict: true,
            language: OutputLanguage::English,
        })
    }

    const PIECEWISE: &str = "template<a R>:\n    have fn identity(x R) R by cases:\n        case x < a: x\n        case x >= a: x\n";

    #[test]
    fn template_function_declared_type_accepts_bound_parameter_renaming_with_evidence() {
        let mut rt = runtime();
        assert!(rt.run_litex_code(PIECEWISE).unwrap().success);
        let code = "\\identity<0> $in fn(renamed R) R";
        let tokens = crate::tokenize::Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
        let crate::ast::stmt::Stmt::Fact(crate::ast::fact::Fact::AtomicFact(crate::ast::fact::AtomicFact::InFact(goal))) = rt.parse(&tokens).unwrap().remove(0)
        else { panic!("function-space membership") };
        assert!(!rt.verify_obj_well_definedness(&goal.element, crate::execute::execute_fact_stmt::VerifyState::top_level()).unwrap().is_failed());
        assert!(!rt.verify_obj_well_definedness(&goal.set, crate::execute::execute_fact_stmt::VerifyState::top_level()).unwrap().is_failed());
        let Some(super::InFactSearchProofByKnownSpecialProperty::TemplateFunctionInDeclaredFnSet(proof)) = rt.search_in_fact_proof_by_known_special_property(&goal)
        else { panic!("declared template type evidence") };
        assert!(matches!(proof.signature_match, super::EqualFactSearchedProof::ByTheyAreTheSame(_)));
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none());
    }

    #[test]
    fn template_function_declared_type_rejects_different_domain_and_return_set() {
        for target in ["fn(renamed N) R", "fn(renamed R) N"] {
            let run = runtime().run_litex_code(&format!("{PIECEWISE}\\identity<0> $in {target}\n")).unwrap();
            assert!(!run.success && run.session_error.is_none(), "{target}");
        }
    }

    #[test]
    fn template_function_declared_type_preserves_domain_conditions_and_free_values() {
        let definition = "template<a R>:\n    have fn above(x R: x > a) R = x\n";
        let run = runtime().run_litex_code(&format!("{definition}\\above<0> $in fn(renamed R: renamed > 0) R\n")).unwrap();
        assert!(run.success && run.session_error.is_none());
        for target in ["fn(renamed R) R", "fn(renamed R: renamed > 1) R"] {
            let run = runtime().run_litex_code(&format!("{definition}\\above<0> $in {target}\n")).unwrap();
            assert!(!run.success && run.session_error.is_none(), "{target}");
        }
    }

    #[test]
    fn template_function_declared_type_requires_template_argument_wd_and_function_witness() {
        let guarded = "template<Guard set, marker Guard>:\n    have fn identity(n N) N = n\n";
        let run = runtime().run_litex_code(&format!("{guarded}\\identity<{{1}}, 1> $in fn(renamed N) N\n")).unwrap();
        assert!(run.success && run.session_error.is_none());
        let run = runtime().run_litex_code(&format!("{guarded}\\identity<{{1}}, 2> $in fn(renamed N) N\n")).unwrap();
        assert!(!run.success && run.session_error.is_none());
        let run = runtime().run_litex_code("template<a R>:\n    have scalar R = a\n\\scalar<0> $in fn(renamed R) R\n").unwrap();
        assert!(!run.success && run.session_error.is_none());
    }
}

impl PositiveRealFromKnownStrictOrderProof { pub fn new(positive_order:AtomicExceptEqualityFactKnownProof)->Self {Self {positive_order}} }
