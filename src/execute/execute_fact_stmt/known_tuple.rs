//! Read tuple structure from stored facts. No verifier, inference, or WD writes.
//! Callers establish subject WD before consuming these local certificates.

use crate::ast::fact::InFact;
use crate::ast::obj::{Cart, FnObj, FnObjHead, FunctionSpace, Literal, Number, Obj, ProductShape, Tuple};
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    FnApplicationInCodomainKnownSpecialPropertyProof, InFactSearchProofByKnownSpecialProperty,
    SignatureMatchProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::helper::{
    set_bound_parameter_count, set_bound_params_to_arg_map,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::{FactId, Runtime};

pub enum KnownTupleShapeProof {
    CartesianMembership(KnownCartesianTupleProof),
    TupleEquality(KnownTupleValueProof),
    FunctionCodomain(KnownFunctionCartesianTupleProof),
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
    AllSignaturesMatch(Vec<SignatureMatchProof>),
}

impl KnownTupleShapeProof {
    pub fn dimension(&self) -> usize {
        match self {
            Self::CartesianMembership(p) => p.cart.args.len(),
            Self::TupleEquality(p) => p.value.args.len(),
            Self::FunctionCodomain(p) => p.cart.args.len(),
        }
    }

    pub fn cart(&self) -> Option<&Cart> {
        match self {
            Self::CartesianMembership(p) => Some(&p.cart),
            Self::FunctionCodomain(p) => Some(&p.cart),
            Self::TupleEquality(_) => None,
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::CartesianMembership(p) => Some(p.membership.fact_id),
            Self::FunctionCodomain(p) => Some(p.membership_proof.cite_property_fact_id),
            Self::TupleEquality(p) => p.tuple_equal.path.first().map(|edge| edge.2),
        }
    }
}

impl Runtime {
    pub(in crate::execute) fn lookup_known_tuple_shape(
        &mut self,
        subject: &Obj,
    ) -> Option<KnownTupleShapeProof> {
        // Prefer a carrier: it supplies coordinate types as well as dimension.
        for (candidate, path) in self.known_tuple_object_peers(subject) {
            for property in self.known_special_properties_of(&candidate) {
                let SpecialProperty::Membership(membership) = property else {
                    continue;
                };
                let Some((cart, carrier_equal)) = self.known_cart_carrier(&membership.set) else {
                    continue;
                };
                return Some(KnownTupleShapeProof::CartesianMembership(
                    KnownCartesianTupleProof {
                        subject_equal: KnownEqualityPathProof::new(path.clone()),
                        membership,
                        carrier_equal,
                        cart,
                    },
                ));
            }
        }
        if let Some(value) = self
            .known_literal_tuple_candidates(subject)
            .into_iter()
            .next()
        {
            return Some(KnownTupleShapeProof::TupleEquality(value));
        }
        let Obj::FnObj(app) = subject else {
            return None;
        };
        let head = tuple_function_head(app);
        for (source_head, path) in self.known_tuple_object_peers(&head) {
            let mut source_app = app.clone();
            source_app.head = Box::new(match source_head {
                Obj::Identifier(id) => FnObjHead::Identifier(id),
                Obj::InstantiatedTemplateObj(inst) => FnObjHead::InstantiatedTemplateObj(inst),
                Obj::StructAndFieldAccessObj(
                    crate::ast::obj::StructAndFieldAccessObj::FieldAccess(access),
                ) => FnObjHead::FieldAccess(access),
                _ => continue,
            });
            for (signature, _) in
                self.collect_in_function_set_candidates(&tuple_function_head(&source_app))
            {
                let Some(return_set) = self.applied_fn_set_return_set(&source_app, &signature)
                else {
                    continue;
                };
                let Some((cart, carrier_equal)) = self.known_cart_carrier(&return_set) else {
                    continue;
                };
                let membership = InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: Obj::FnObj(source_app.clone()),
                    set: return_set,
                    line_file: None,
                };
                // Reuse the codomain reader's all-signatures guard; never claim an
                // arbitrary signature supplied the enclosing application's WD.
                let Some(InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(proof)) =
                    self.search_in_fact_proof_by_known_special_property(&membership)
                else {
                    continue;
                };
                return Some(KnownTupleShapeProof::FunctionCodomain(
                    KnownFunctionCartesianTupleProof {
                        function_equal: KnownEqualityPathProof::new(path.clone()),
                        membership,
                        membership_proof: proof,
                        carrier_equal,
                        cart,
                    },
                ));
            }
        }
        None
    }

    pub(in crate::execute) fn known_literal_tuple_candidates(
        &self,
        subject: &Obj,
    ) -> Vec<KnownTupleValueProof> {
        self.known_tuple_object_peers(subject)
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
        for (candidate, path) in self.known_tuple_object_peers(&head) {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = candidate else {
                continue;
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
                        self.lookup_known_obj_equality(&candidate_obj, &signature_obj)
                    else {
                        compatible = false;
                        break;
                    };
                    matches.push(SignatureMatchProof {
                        cite_signature_fact_id: id,
                        signature_match: proof,
                    });
                }
                if !compatible || matches.is_empty() {
                    continue;
                }
                KnownFunctionTupleApplicability::AllSignaturesMatch(matches)
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

    fn known_cart_carrier(&self, carrier: &Obj) -> Option<(Cart, KnownEqualityPathProof)> {
        self.known_tuple_object_peers(carrier)
            .into_iter()
            .find_map(|(obj, path)| {
                let Obj::ProductShape(ProductShape::Cart(cart)) = obj else {
                    return None;
                };
                Some((cart, KnownEqualityPathProof::new(path)))
            })
    }

    fn known_tuple_object_peers(&self, subject: &Obj) -> Vec<(Obj, Vec<(Obj, Obj, FactId)>)> {
        equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(),
            subject,
        )
    }
}

pub(crate) fn literal_positive_usize(obj: &Obj) -> Option<usize> {
    let Obj::Literal(Literal::Number(Number { normalized_value })) = obj else {
        return None;
    };
    let n: usize = normalized_value.parse().ok()?;
    (n > 0).then_some(n)
}

fn tuple_function_head(app: &FnObj) -> Obj {
    match app.head.as_ref() {
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
