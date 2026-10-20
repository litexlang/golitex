//! Fixed laws for strict, already well-defined compositions. In particular,
//! associativity never supplies WD for an invalid intermediate composition.
use crate::prelude::*;

pub enum CompositionEqualityProof {
    Associativity(CompositionAssociativityProof),
    LeftIdentity(CompositionLeftIdentityProof),
    RightIdentity(CompositionRightIdentityProof),
    Definition(CompositionDefinitionProof),
}
pub struct CompositionAssociativityProof {
    pub left: Composition,
    pub right: Composition,
}
pub struct CompositionLeftIdentityProof {
    pub identity: AnonymousFn,
    pub identity_equal: KnownEqualityPathProof,
}
pub struct CompositionRightIdentityProof {
    pub identity: AnonymousFn,
    pub identity_equal: KnownEqualityPathProof,
    pub full_domain: crate::execute::execute_fact_stmt::function_domain::FunctionDomainMatchProof,
}
pub struct CompositionDefinitionProof {
    pub callable: Box<CompositionCallableProof>,
    pub function: AnonymousFn,
    pub function_equal: KnownEqualityPathProof,
}

impl Runtime {
    pub(super) fn search_composition_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<CompositionEqualityProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::FunctionSpace(FunctionSpace::Composition(composition)) = left else {
                continue;
            };
            // (f ∘ g) ∘ h = f ∘ (g ∘ h), with both sides' WD checked by the parent.
            if let (
                Obj::FunctionSpace(FunctionSpace::Composition(fg)),
                Obj::FunctionSpace(FunctionSpace::Composition(rhs)),
            ) = (composition.outer.as_ref(), right)
            {
                if let Obj::FunctionSpace(FunctionSpace::Composition(gh)) = rhs.inner.as_ref() {
                    if same(&fg.outer, &rhs.outer)
                        && same(&fg.inner, &gh.outer)
                        && same(&composition.inner, &gh.inner)
                    {
                        return Ok(Some(CompositionEqualityProof::Associativity(
                            CompositionAssociativityProof {
                                left: composition.clone(),
                                right: rhs.clone(),
                            },
                        )));
                    }
                }
            }
            // id ∘ g = g, including multivariate g; compatibility is in parent WD.
            if same(&composition.inner, right) {
                for (value, path) in self.exact_property_object_values_of_shapes(
                    &composition.outer,
                    &[EqualToObjShape::AnonymousFn],
                ) {
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(identity)) = value else {
                        continue;
                    };
                    if is_identity(&identity) {
                        return Ok(Some(CompositionEqualityProof::LeftIdentity(
                            CompositionLeftIdentityProof {
                                identity,
                                identity_equal: KnownEqualityPathProof::new(path),
                            },
                        )));
                    }
                }
            }
            // f ∘ id_D = f requires the SAME COMPLETE domain, including guards.
            if same(&composition.outer, right) {
                for (value, path) in self.exact_property_object_values_of_shapes(
                    &composition.inner,
                    &[EqualToObjShape::AnonymousFn],
                ) {
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(identity)) = value else {
                        continue;
                    };
                    if !is_identity(&identity) {
                        continue;
                    }
                    if let Ok(full_domain) =
                        self.verify_complete_function_domain(right, &identity.body, state)?
                    {
                        return Ok(Some(CompositionEqualityProof::RightIdentity(
                            CompositionRightIdentityProof {
                                identity,
                                identity_equal: KnownEqualityPathProof::new(path),
                                full_domain,
                            },
                        )));
                    }
                }
            }
            // The defining lambda has the same graph even with a different
            // verified return upper bound. No arbitrary extensional search.
            for (value, path) in
                self.exact_property_object_values_of_shapes(right, &[EqualToObjShape::AnonymousFn])
            {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = value else {
                    continue;
                };
                for callable in self.parent_checked_composition_callables(left, state)? {
                    let mut a = callable.function.clone();
                    let mut b = function.clone();
                    a.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
                    b.body.ret_set = a.body.ret_set.clone();
                    if crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::anonymous_fns_alpha_equal(&a, &b) {
                        return Ok(Some(CompositionEqualityProof::Definition(CompositionDefinitionProof { callable: Box::new(callable), function, function_equal: KnownEqualityPathProof::new(path) })));
                    }
                }
            }
        }
        Ok(None)
    }
}

impl CompositionEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::Associativity(_) => "CompositionAssociativity",
            Self::LeftIdentity(_) => "CompositionLeftIdentity",
            Self::RightIdentity(_) => "CompositionRightIdentity",
            Self::Definition(_) => "CompositionDefinition",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::Associativity(_) => {
                "(f ∘ g) ∘ h = f ∘ (g ∘ h), with both constructions well-defined"
            }
            Self::LeftIdentity(_) => "id ∘ g = g on the complete domain of g",
            Self::RightIdentity(_) => "f ∘ id = f when the complete input domains agree",
            Self::Definition(_) => "compose(f,g) is the checked lambda with body f(g(args))",
        }
    }
}
fn same(a: &Obj, b: &Obj) -> bool {
    a == b || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a,b)
}
fn is_identity(function: &AnonymousFn) -> bool {
    let params: Vec<_> = function
        .body
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .collect();
    params.len() == 1
        && function.equal_to.as_ref() == &Obj::Identifier(IdentifierObj::from_bound_name(params[0]))
}
