//! Read tuple structure from stored facts. No verifier, inference, or WD writes.
//! Callers establish subject WD before consuming these local certificates.

use crate::ast::fact::InFact;
use crate::ast::obj::{Cart, FnObj, FnObjHead, FnSet, FunctionSpace, InstantiatedTemplateObj, Literal, Number, Obj, ProductShape, Tuple};
use crate::exec_env::SpecialProperty;
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    FnApplicationInCodomainKnownSpecialPropertyProof, InFactSearchProofByKnownSpecialProperty,
    SignatureMatchProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::helper::{
    set_bound_parameter_count, set_bound_params_to_arg_map,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::{FactId, Runtime};

pub enum KnownTupleShapeProof {
    CartesianMembership(KnownCartesianTupleProof),
    TupleEquality(KnownTupleValueProof),
    FunctionCodomain(KnownFunctionCartesianTupleProof),
    CartesianCoordinate(KnownCartesianCoordinateTupleProof),
}

pub struct KnownCartesianCoordinateTupleProof {
    pub receiver: Box<KnownTupleShapeProof>,
    pub index: usize,
    pub carrier_equal: KnownEqualityPathProof,
    pub cart: Cart,
}

pub struct KnownCartesianTupleProof {
    pub subject_equal: KnownEqualityPathProof,
    pub membership: InFact,
    pub carrier_equal: KnownEqualityPathProof,
    pub cart: Cart,
}

pub struct KnownTupleValueProof {
    pub tuple_equal: KnownEqualityPathProof,
    pub value: Tuple,
}

pub struct KnownFunctionCartesianTupleProof {
    pub function_equal: KnownEqualityPathProof,
    pub membership: InFact,
    pub membership_proof: FnApplicationInCodomainKnownSpecialPropertyProof,
    pub carrier_equal: KnownEqualityPathProof,
    pub cart: Cart,
}

pub struct KnownFunctionTupleValueProof {
    pub function_equal: KnownEqualityPathProof,
    pub applicability: KnownFunctionTupleApplicability,
    pub value: Tuple,
}

// Cached application WD does not identify its chosen signature. Only unfold
// when every possible WD signature agrees with the selected function's domain.
pub enum KnownFunctionTupleApplicability {
    AnonymousLiteral,
    AllSignaturesMatch {
        signatures: Vec<SignatureMatchProof>,
        template_signatures: Vec<KnownTemplateSignatureMatchProof>,
    },
    TemplateDefinition {
        instance: InstantiatedTemplateObj,
        signature: FnSet,
        alternative_signatures: Vec<SignatureMatchProof>,
        alternative_template_signatures: Vec<KnownTemplateSignatureMatchProof>,
    },
}

pub struct KnownTemplateSignatureMatchProof {
    pub function_equal: KnownEqualityPathProof,
    pub instance: InstantiatedTemplateObj,
    pub signature_match:
        crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof,
}

impl KnownTupleShapeProof {
    pub fn dimension(&self) -> usize {
        match self {
            Self::CartesianMembership(p) => p.cart.args.len(),
            Self::TupleEquality(p) => p.value.args.len(),
            Self::FunctionCodomain(p) => p.cart.args.len(),
            Self::CartesianCoordinate(p) => p.cart.args.len(),
        }
    }

    pub fn cart(&self) -> Option<&Cart> {
        match self {
            Self::CartesianMembership(p) => Some(&p.cart),
            Self::FunctionCodomain(p) => Some(&p.cart),
            Self::CartesianCoordinate(p) => Some(&p.cart),
            Self::TupleEquality(_) => None,
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::CartesianMembership(p) => Some(p.membership.fact_id),
            Self::FunctionCodomain(p) => Some(p.membership_proof.cite_property_fact_id),
            Self::TupleEquality(p) => p.tuple_equal.path.first().map(|edge| edge.2),
            Self::CartesianCoordinate(p) => p.receiver.cite_fact_id(),
        }
    }
}

impl Runtime {
    pub(in crate::execute) fn lookup_known_tuple_shape(
        &mut self,
        subject: &Obj,
    ) -> Option<KnownTupleShapeProof> {
        // Prefer membership published on this exact subject. Only a checked
        // equality path may transport another value's Cartesian membership.
        for property in self.known_special_properties_of(subject) {
            let SpecialProperty::Membership(membership) = property else {
                continue;
            };
            let Some((cart, carrier_equal)) = self.known_cart_carrier(&membership.set) else {
                continue;
            };
            return Some(KnownTupleShapeProof::CartesianMembership(
                KnownCartesianTupleProof {
                    subject_equal: KnownEqualityPathProof::new(vec![]),
                    membership,
                    carrier_equal,
                    cart,
                },
            ));
        }
        for (candidate, path) in self.exact_property_object_values(subject) {
            if path.is_empty() {
                continue;
            }
            for property in self.known_special_properties_of(&candidate) {
                let SpecialProperty::Membership(membership) = property else {
                    continue;
                };
                let Some((cart, carrier_equal)) = self.known_cart_carrier(&membership.set) else {
                    continue;
                };
                return Some(KnownTupleShapeProof::CartesianMembership(
                    KnownCartesianTupleProof {
                        subject_equal: KnownEqualityPathProof::new(path),
                        membership,
                        carrier_equal,
                        cart,
                    },
                ));
            }
        }
        if let Obj::FnObj(app) = subject {
            // The checked call selects one declared Cartesian coordinate.
            // Descend only through the strictly shorter receiver, preserving
            // the original membership and carrier-equality certificates.
            if let Some(receiver) = self.finite_function_application_receiver(app) {
                if let Some(index) = literal_positive_usize(&app.body.last().unwrap()[0]) {
                    if let Some(shape) = self.lookup_known_tuple_shape(&receiver) {
                        if let Some(factor) = shape.cart().and_then(|cart| cart.args.get(index - 1))
                        {
                            if let Some((cart, carrier_equal)) = self.known_cart_carrier(factor) {
                                return Some(KnownTupleShapeProof::CartesianCoordinate(
                                    KnownCartesianCoordinateTupleProof {
                                        receiver: Box::new(shape),
                                        index,
                                        carrier_equal,
                                        cart,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
            for (signature, _) in self.collect_in_function_set_candidates(&tuple_function_head(app))
            {
                let Some(return_set) = self.applied_fn_set_return_set(app, &signature) else {
                    continue;
                };
                let Some((cart, carrier_equal)) = self.known_cart_carrier(&return_set) else {
                    continue;
                };
                let membership = InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: subject.clone(),
                    set: return_set,
                    line_file: None,
                };
                let Some(InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(proof)) =
                    self.search_in_fact_proof_by_known_special_property(&membership)
                else {
                    continue;
                };
                return Some(KnownTupleShapeProof::FunctionCodomain(
                    KnownFunctionCartesianTupleProof {
                        function_equal: KnownEqualityPathProof::new(vec![]),
                        membership,
                        membership_proof: proof,
                        carrier_equal,
                        cart,
                    },
                ));
            }
        }
        self.known_literal_tuple_candidates(subject)
            .into_iter()
            .next()
            .map(KnownTupleShapeProof::TupleEquality)
    }

    pub(in crate::execute) fn known_literal_tuple_candidates(
        &self,
        subject: &Obj,
    ) -> Vec<KnownTupleValueProof> {
        self.exact_property_object_values(subject)
            .into_iter()
            .filter_map(|(obj, path)| {
                let Obj::ProductShape(ProductShape::Tuple(value)) = obj else {
                    return None;
                };
                Some(KnownTupleValueProof {
                    tuple_equal: KnownEqualityPathProof::new(path),
                    value,
                })
            })
            .collect()
    }

    // One checked beta substitution, only after application WD. No residual
    // equality search: a non-tuple body simply misses this route.
    pub(in crate::execute) fn lookup_known_function_tuple_value(
        &mut self,
        app: &FnObj,
    ) -> Option<KnownFunctionTupleValueProof> {
        if app.body.len() != 1 {
            return None;
        }
        let head = tuple_function_head(app);
        let args: Vec<Obj> = app.body[0].iter().map(|x| x.as_ref().clone()).collect();
        for (candidate, path) in self.exact_property_object_values(&head) {
            let (anon, template_instance) = match candidate {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => (anon, None),
                Obj::InstantiatedTemplateObj(instance) => {
                    let Some(def) = self.def_template_visible(&instance.template_name).cloned()
                    else {
                        continue;
                    };
                    let TemplateDefEnum::HaveFnEqualStmt(stmt) = &def.template_def_stmt else {
                        continue;
                    };
                    let ids = def.template_arg_def.ordered_param_ids();
                    if ids.len() != instance.args.len() {
                        continue;
                    }
                    let subst = ids.into_iter().zip(instance.args.iter().cloned()).collect();
                    let Ok(Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon))) = self.inst_obj(
                        &Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                            stmt.equal_to_anonymous_fn.clone(),
                        )),
                        &subst,
                    ) else {
                        continue;
                    };
                    (anon, Some(instance))
                }
                _ => continue,
            };
            if args.len() != set_bound_parameter_count(&anon.body.set_bound_parameters) {
                continue;
            }
            let signature_obj = Obj::FunctionSpace(FunctionSpace::FnSet(anon.body.clone()));
            let applicability = if matches!(app.head.as_ref(), FnObjHead::AnonymousFnLiteral(_)) {
                // The literal head itself is the WD-selected definition.
                if !path.is_empty() {
                    continue;
                }
                KnownFunctionTupleApplicability::AnonymousLiteral
            } else {
                let candidates = self.collect_in_function_set_candidates(&head);
                let mut matches = Vec::new();
                let mut compatible = true;
                for (signature, id) in candidates {
                    if self.applied_fn_set_return_set(app, &signature).is_none() {
                        continue;
                    }
                    let candidate_obj = Obj::FunctionSpace(FunctionSpace::FnSet(signature));
                    let Some(proof) =
                        self.lookup_exact_property_obj_equality(&candidate_obj, &signature_obj)
                    else {
                        compatible = false;
                        break;
                    };
                    matches.push(SignatureMatchProof {
                        cite_signature_fact_id: id,
                        signature_match: proof,
                    });
                }
                let mut template_matches = Vec::new();
                for (peer, peer_path) in self.exact_property_object_values(&head) {
                    let Obj::InstantiatedTemplateObj(instance) = peer else {
                        continue;
                    };
                    let Some(signature) = self.instantiated_template_function_signature(&instance)
                    else {
                        continue;
                    };
                    if self.applied_fn_set_return_set(app, &signature).is_none() {
                        continue;
                    }
                    let candidate_obj = Obj::FunctionSpace(FunctionSpace::FnSet(signature));
                    let Some(signature_match) =
                        self.lookup_exact_property_obj_equality(&candidate_obj, &signature_obj)
                    else {
                        compatible = false;
                        break;
                    };
                    template_matches.push(KnownTemplateSignatureMatchProof {
                        function_equal: KnownEqualityPathProof::new(peer_path),
                        instance,
                        signature_match,
                    });
                }
                if !compatible {
                    continue;
                }
                if let Some(instance) = template_instance {
                    // Application WD already checks this declaration's arguments
                    // and guards. Competing stored signatures must agree too.
                    KnownFunctionTupleApplicability::TemplateDefinition {
                        instance,
                        signature: anon.body.clone(),
                        alternative_signatures: matches,
                        alternative_template_signatures: template_matches,
                    }
                } else {
                    if matches.is_empty() && template_matches.is_empty() {
                        continue;
                    }
                    KnownFunctionTupleApplicability::AllSignaturesMatch {
                        signatures: matches,
                        template_signatures: template_matches,
                    }
                }
            };
            let subst = set_bound_params_to_arg_map(&anon.body.set_bound_parameters, &args);
            let Ok(Obj::ProductShape(ProductShape::Tuple(value))) =
                self.inst_obj(anon.equal_to.as_ref(), &subst)
            else {
                continue;
            };
            return Some(KnownFunctionTupleValueProof {
                function_equal: KnownEqualityPathProof::new(path),
                applicability,
                value,
            });
        }
        None
    }

    pub(in crate::execute) fn known_function_tuple_candidates(
        &mut self,
        subject: &Obj,
    ) -> Vec<(KnownEqualityPathProof, KnownFunctionTupleValueProof)> {
        let mut candidates = Vec::new();
        for (peer, path) in self.exact_property_object_values(subject) {
            let Obj::FnObj(app) = peer else {
                continue;
            };
            if let Some(function) = self.lookup_known_function_tuple_value(&app) {
                candidates.push((KnownEqualityPathProof::new(path), function));
            }
        }
        candidates
    }

    fn known_cart_carrier(&self, carrier: &Obj) -> Option<(Cart, KnownEqualityPathProof)> {
        self.exact_property_object_values(carrier)
            .into_iter()
            .find_map(|(obj, path)| {
                let Obj::ProductShape(ProductShape::Cart(cart)) = obj else {
                    return None;
                };
                Some((cart, KnownEqualityPathProof::new(path)))
            })
    }
}

pub(crate) fn literal_positive_usize(obj: &Obj) -> Option<usize> {
    let Obj::Literal(Literal::Number(Number { normalized_value })) = obj else {
        return None;
    };
    let n: usize = normalized_value.parse().ok()?;
    (n > 0).then_some(n)
}

pub(in crate::execute) fn tuple_function_head(app: &FnObj) -> Obj {
    match app.head.as_ref() {
        FnObjHead::Object(obj) => obj.as_ref().clone(),
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(anon) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon.as_ref().clone()))
        }
        FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
        FnObjHead::FieldAccess(access) => Obj::StructAndFieldAccessObj(
            crate::ast::obj::StructAndFieldAccessObj::FieldAccess(access.clone()),
        ),
    }
}
