//! Matrix values are ordinary exact finite-domain functions. No shape state.
use crate::prelude::*;
use super::function_domain::function_application;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::helper::set_bound_params_to_arg_map;

pub struct MatrixCallableProof {
    pub operator: MatrixOperator,
    pub function_equal: KnownEqualityPathProof,
    pub well_defined: MatrixCallableWellDefinedProof,
    pub scalar_carrier: MatrixFunctionScalarCarrierProof,
    pub function: AnonymousFn,
}
pub enum MatrixCallableWellDefinedProof {
    Checked(Box<ObjWellDefinedProof>),
    // Only truth rules after the parent atomic WD; never construction WD.
    ParentAtomic,
}
pub enum MatrixFunctionScalarCarrierProof {
    RealConstants,
    RealOperands(Vec<super::matrix_operations::MatrixRealOperandProof>),
    RealInput(Box<VerifyFactResult>),
    RealReturnedFunction(Box<super::function_domain::CompleteFunctionDomainProof>),
    ComplexInput,
}

pub(crate) fn matrix_number(value: i64) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: value.to_string(),
    }))
}
pub(crate) fn matrix_space(set: Obj, rows: Obj, cols: Obj) -> Obj {
    Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
        set: Box::new(set),
        rows: Box::new(rows),
        cols: Box::new(cols),
    }))
}
pub(crate) fn matrix_call(function: &Obj, args: Vec<Obj>) -> Obj {
    function_application(function, args.into_iter().map(Box::new).collect())
        .expect("ordinary matrix application has an object head")
}
pub(crate) fn matrix_identifier(binding: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(binding))
}
fn index_range(end: &Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(matrix_number(1)),
        end: Box::new(end.clone()),
    }))
}

impl Runtime {
    pub(crate) fn matrix_fn_signature(&mut self, set: &Obj, rows: &Obj, cols: &Obj) -> FnSet {
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![
                    SetBoundParameterGroup {
                        params: vec![self.fresh_internal_param()],
                        param_type: Box::new(index_range(rows)),
                    },
                    SetBoundParameterGroup {
                        params: vec![self.fresh_internal_param()],
                        param_type: Box::new(index_range(cols)),
                    },
                ],
            },
            dom_facts: vec![],
            ret_set: Box::new(set.clone()),
        }
    }

    pub(crate) fn native_matrix_membership(
        &mut self,
        matrix: &Obj,
        scalar: StandardSet,
        rows: &Obj,
        cols: &Obj,
    ) -> AtomicFact {
        AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: matrix.clone(),
            set: matrix_space(Obj::StandardSet(scalar), rows.clone(), cols.clone()),
            line_file: None,
        })
    }

    pub(crate) fn matrix_callables(
        &mut self,
        subject: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<MatrixCallableProof>> {
        self.matrix_callables_inner(subject, state, false)
    }

    pub(crate) fn parent_checked_matrix_callables(
        &mut self,
        subject: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Vec<MatrixCallableProof>> {
        self.matrix_callables_inner(subject, state, true)
    }

    fn matrix_callables_inner(
        &mut self,
        subject: &Obj,
        state: VerifyState,
        parent_atomic: bool,
    ) -> RuntimeResult<Vec<MatrixCallableProof>> {
        let mut proofs = Vec::new();
        for (peer, path) in
            self.exact_property_object_values_of_shapes(subject, &[EqualToObjShape::Other])
        {
            let Obj::MatrixOperator(operator) = peer else {
                continue;
            };
            if let Some(proof) = self.extended_matrix_callable(
                &operator,
                KnownEqualityPathProof::new(path.clone()),
                state,
                parent_atomic,
            )? {
                proofs.push(proof);
                continue;
            }
            let (input, rows, cols) = match &operator {
                MatrixOperator::ZeroMatrix(x) => (None, x.rows.as_ref(), x.cols.as_ref()),
                MatrixOperator::IdentityMatrix(x) => (None, x.order.as_ref(), x.order.as_ref()),
                MatrixOperator::Transpose(x) => {
                    (Some(x.matrix.as_ref()), x.cols.as_ref(), x.rows.as_ref())
                }
                MatrixOperator::ConjugateTranspose(x) => {
                    (Some(x.matrix.as_ref()), x.cols.as_ref(), x.rows.as_ref())
                }
                MatrixOperator::Determinant(_) | MatrixOperator::Trace(_) => continue,
                MatrixOperator::Add(_)
                | MatrixOperator::Subtract(_)
                | MatrixOperator::Scale(_)
                | MatrixOperator::Multiply(_)
                | MatrixOperator::Apply(_)
                | MatrixOperator::Power(_)
                | MatrixOperator::Inverse(_)
                | MatrixOperator::Rank(_)
                | MatrixOperator::Minor(_)
                | MatrixOperator::Cofactor(_)
                | MatrixOperator::Adjugate(_)
                | MatrixOperator::Diagonal(_)
                | MatrixOperator::OuterProduct(_)
                | MatrixOperator::InnerProduct(_)
                | MatrixOperator::EuclideanNorm(_)
                | MatrixOperator::FrobeniusNorm(_) => continue,
            };
            let root = Obj::MatrixOperator(operator.clone());
            let well_defined = if parent_atomic {
                MatrixCallableWellDefinedProof::ParentAtomic
            } else {
                let VerifyObjWellDefinedResult::Success(proof) =
                    self.verify_obj_well_definedness(&root, state)?
                else {
                    continue;
                };
                MatrixCallableWellDefinedProof::Checked(Box::new(proof))
            };
            let carrier = if let Some(input) = input {
                // Source dimensions are reversed for a transpose's output.
                let signature =
                    self.matrix_fn_signature(&Obj::StandardSet(StandardSet::R), cols, rows);
                let fact: Fact = AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: input.clone(),
                    set: Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
                    line_file: None,
                })
                .into();
                let proof = self.verify_fact(&fact, state)?;
                if proof.is_failed() {
                    let mut returned_real = None;
                    if let Obj::FnObj(application) = input {
                        for domain in
                            self.complete_application_return_domains(application, &[], state)?
                        {
                            if matches!(
                                domain.signature.ret_set.as_ref(),
                                Obj::StandardSet(StandardSet::R)
                            ) && super::function_domain::function_domains_alpha_equal(
                                &domain.signature,
                                &signature,
                            ) {
                                returned_real = Some(domain);
                                break;
                            }
                        }
                    }
                    match returned_real {
                        Some(domain) => {
                            MatrixFunctionScalarCarrierProof::RealReturnedFunction(Box::new(domain))
                        }
                        None => MatrixFunctionScalarCarrierProof::ComplexInput,
                    }
                } else {
                    MatrixFunctionScalarCarrierProof::RealInput(Box::new(proof))
                }
            } else {
                MatrixFunctionScalarCarrierProof::RealConstants
            };
            let scalar = match &carrier {
                MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
                MatrixFunctionScalarCarrierProof::RealConstants
                | MatrixFunctionScalarCarrierProof::RealOperands(_)
                | MatrixFunctionScalarCarrierProof::RealInput(_)
                | MatrixFunctionScalarCarrierProof::RealReturnedFunction(_) => StandardSet::R,
            };
            let signature = self.matrix_fn_signature(&Obj::StandardSet(scalar), rows, cols);
            let r = matrix_identifier(&signature.set_bound_parameters.groups[0].params[0]);
            let c = matrix_identifier(&signature.set_bound_parameters.groups[1].params[0]);
            let body = match &operator {
                MatrixOperator::ZeroMatrix(_) => matrix_number(0),
                MatrixOperator::IdentityMatrix(_) => {
                    Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                        set: Box::new(Obj::SetOperator(SetOperator::Intersect(Intersect {
                            left: Box::new(Obj::SetFormer(SetFormer::ListSet(ListSet {
                                list: vec![Box::new(r)],
                            }))),
                            right: Box::new(Obj::SetFormer(SetFormer::ListSet(ListSet {
                                list: vec![Box::new(c)],
                            }))),
                        }))),
                    }))
                }
                MatrixOperator::Transpose(x) => matrix_call(&x.matrix, vec![c, r]),
                MatrixOperator::ConjugateTranspose(x) => {
                    Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate {
                        arg: Box::new(matrix_call(&x.matrix, vec![c, r])),
                    }))
                }
                MatrixOperator::Determinant(_) | MatrixOperator::Trace(_) => unreachable!(),
                MatrixOperator::Add(_)
                | MatrixOperator::Subtract(_)
                | MatrixOperator::Scale(_)
                | MatrixOperator::Multiply(_)
                | MatrixOperator::Apply(_)
                | MatrixOperator::Power(_)
                | MatrixOperator::Inverse(_)
                | MatrixOperator::Rank(_)
                | MatrixOperator::Minor(_)
                | MatrixOperator::Cofactor(_)
                | MatrixOperator::Adjugate(_)
                | MatrixOperator::Diagonal(_)
                | MatrixOperator::OuterProduct(_)
                | MatrixOperator::InnerProduct(_)
                | MatrixOperator::EuclideanNorm(_)
                | MatrixOperator::FrobeniusNorm(_) => {
                    unreachable!("extended callable is built separately")
                }
            };
            proofs.push(MatrixCallableProof {
                operator,
                function_equal: KnownEqualityPathProof::new(path),
                well_defined,
                scalar_carrier: carrier,
                function: AnonymousFn {
                    body: signature,
                    equal_to: Box::new(body),
                },
            });
        }
        Ok(proofs)
    }

    pub(crate) fn matrix_component_body(
        &mut self,
        call: &FnObj,
        callable: &MatrixCallableProof,
    ) -> Option<Obj> {
        if call.body.len() != 1 {
            return None;
        }
        let args: Vec<_> = call.body[0].iter().map(|x| x.as_ref().clone()).collect();
        if args.len()
            != callable
                .function
                .body
                .set_bound_parameters
                .groups
                .iter()
                .map(|g| g.params.len())
                .sum::<usize>()
        {
            return None;
        }
        let map = set_bound_params_to_arg_map(&callable.function.body.set_bound_parameters, &args);
        self.inst_obj(&callable.function.equal_to, &map).ok()
    }

    pub(crate) fn matrix_scalar_definition(&mut self, operator: &MatrixOperator) -> Option<Obj> {
        match operator {
            MatrixOperator::Trace(x) => {
                let k = self.fresh_internal_param();
                let index = matrix_identifier(&k);
                let callback = Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
                    body: FnSet {
                        set_bound_parameters: SetBoundParameterList {
                            groups: vec![SetBoundParameterGroup {
                                params: vec![k],
                                param_type: Box::new(index_range(&x.order)),
                            }],
                        },
                        dom_facts: vec![],
                        ret_set: Box::new(Obj::StandardSet(StandardSet::C)),
                    },
                    equal_to: Box::new(matrix_call(&x.matrix, vec![index.clone(), index])),
                }));
                Some(Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(
                    SumOfFiniteSet {
                        set: Box::new(index_range(&x.order)),
                        func: Box::new(callback),
                    },
                )))
            }
            MatrixOperator::Determinant(x) => {
                let n = super::matrix_operations::natural_literal(&x.order)?;
                let mut budget = crate::execute::execute_eval_stmt::helper::MAX_AGGREGATE_TERMS;
                if n > budget as i64 {
                    return None;
                }
                let indices: Vec<_> = (1..=n).collect();
                super::matrix_operations::determinant_formula(
                    &x.matrix,
                    &indices,
                    &indices,
                    &mut budget,
                )
            }
            _ => self.extended_matrix_scalar_definition(operator),
        }
    }
}

pub enum MatrixMembershipProof {
    ExtendedScalar(super::matrix_operations::ExtendedMatrixScalarMembershipProof),
    Space(MatrixSpaceMembershipProof),
    Function(MatrixFunctionMembershipProof),
    Application(MatrixApplicationMembershipProof),
    ScalarComplex(MatrixScalarComplexProof),
    ScalarReal(MatrixScalarRealProof),
}
pub struct MatrixSpaceMembershipProof {
    pub signature: FnSet,
    pub membership: MatrixSpaceMembershipEvidence,
}
pub enum MatrixSpaceMembershipEvidence {
    Exact(Box<VerifyFactResult>),
    RealToComplex(Box<VerifyFactResult>),
}
pub struct MatrixFunctionMembershipProof {
    pub callable: Box<MatrixCallableProof>,
    pub target: FnSet,
}
pub struct MatrixApplicationMembershipProof {
    pub callable: Box<MatrixCallableProof>,
    pub return_set: Obj,
}
pub struct MatrixScalarComplexProof {}
pub struct MatrixScalarRealProof {
    pub input_is_real: Box<VerifyFactResult>,
}

pub enum MatrixEqualityProof {
    SpaceDefinition(MatrixSpaceDefinitionProof),
    FunctionDefinition(MatrixFunctionDefinitionProof),
    ComponentDefinition(MatrixComponentDefinitionProof),
    ScalarDefinition(MatrixScalarDefinitionProof),
}
pub struct MatrixSpaceDefinitionProof {
    pub signature: FnSet,
    pub equality: Box<MatrixDefinitionResidualProof>,
}
pub struct MatrixFunctionDefinitionProof {
    pub callable: Box<MatrixCallableProof>,
    pub equality: Box<MatrixDefinitionResidualProof>,
}
pub struct MatrixComponentDefinitionProof {
    pub callable: Box<MatrixCallableProof>,
    pub body: Obj,
    pub reduction: MatrixComponentReduction,
    pub equality: Box<MatrixDefinitionResidualProof>,
}
pub struct MatrixComponentReduction {
    pub value: Obj,
    pub evidence: MatrixComponentReductionEvidence,
}
pub enum MatrixComponentReductionEvidence {
    Unchanged,
    NativeApplication(MatrixNestedApplicationReduction),
    ConjugateArgument(Box<MatrixComponentReduction>),
}
pub struct MatrixNestedApplicationReduction {
    pub application_well_defined: Box<ObjWellDefinedProof>,
    pub callable: Box<MatrixCallableProof>,
    pub body: Obj,
    pub continuation: Box<MatrixComponentReduction>,
}
pub struct MatrixScalarDefinitionProof {
    pub expression: Obj,
    pub equality: Box<MatrixDefinitionResidualProof>,
}

impl Runtime {
    pub(crate) fn search_native_matrix_membership(
        &mut self,
        fact: &InFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixMembershipProof>> {
        if let Some(target) = self.function_space_signature(&fact.set) {
            for callable in self.parent_checked_matrix_callables(&fact.element, state)? {
                let source = &callable.function.body;
                let returns = source.ret_set.ir()==target.ret_set.ir()
                    || match (source.ret_set.as_ref(),target.ret_set.as_ref()) {
                        (Obj::StandardSet(s),Obj::StandardSet(t)) =>
                            super::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq(s,t),
                        _=>false,
                    };
                if returns && super::function_domain::function_domains_alpha_equal(source, &target)
                {
                    return Ok(Some(MatrixMembershipProof::Function(
                        MatrixFunctionMembershipProof {
                            callable: Box::new(callable),
                            target: target.clone(),
                        },
                    )));
                }
            }
        }
        if let Obj::SetFormer(SetFormer::MatrixSet(_)) = &fact.set {
            let signature = self.function_space_signature(&fact.set).unwrap();
            let equivalent: Fact = AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: fact.element.clone(),
                set: Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
                line_file: None,
            })
            .into();
            let proof = self.verify_fact(&equivalent, state)?;
            if !proof.is_failed() {
                return Ok(Some(MatrixMembershipProof::Space(
                    MatrixSpaceMembershipProof {
                        signature,
                        membership: MatrixSpaceMembershipEvidence::Exact(Box::new(proof)),
                    },
                )));
            }
            // Standard scalar widening needs no further function-domain search:
            // the checked real FnSet has precisely the same full input domain.
            if matches!(signature.ret_set.as_ref(), Obj::StandardSet(StandardSet::C)) {
                let mut real_signature = signature.clone();
                real_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
                let real: Fact = AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: fact.element.clone(),
                    set: Obj::FunctionSpace(FunctionSpace::FnSet(real_signature)),
                    line_file: None,
                })
                .into();
                let proof = self.verify_fact(&real, state)?;
                if !proof.is_failed() {
                    return Ok(Some(MatrixMembershipProof::Space(
                        MatrixSpaceMembershipProof {
                            signature,
                            membership: MatrixSpaceMembershipEvidence::RealToComplex(Box::new(
                                proof,
                            )),
                        },
                    )));
                }
            }
            return Ok(None);
        }
        if let Obj::StandardSet(target) = &fact.set {
            if let Obj::MatrixOperator(operator) = &fact.element {
                if let Some(proof) =
                    self.extended_matrix_scalar_membership(operator, target.clone(), state)?
                {
                    return Ok(Some(MatrixMembershipProof::ExtendedScalar(proof)));
                }
                let scalar_input = match operator {
                    MatrixOperator::Determinant(x) => Some((&x.matrix, &x.order)),
                    MatrixOperator::Trace(x) => Some((&x.matrix, &x.order)),
                    _ => None,
                };
                if let Some((input, order)) = scalar_input {
                    if *target == StandardSet::C {
                        return Ok(Some(MatrixMembershipProof::ScalarComplex(
                            MatrixScalarComplexProof {},
                        )));
                    }
                    if *target == StandardSet::R {
                        let signature = self.matrix_fn_signature(
                            &Obj::StandardSet(StandardSet::R),
                            order,
                            order,
                        );
                        let real: Fact = AtomicFact::InFact(InFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            element: input.as_ref().clone(),
                            set: Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
                            line_file: None,
                        })
                        .into();
                        let proof = self.verify_fact(&real, state)?;
                        if !proof.is_failed() {
                            return Ok(Some(MatrixMembershipProof::ScalarReal(
                                MatrixScalarRealProof {
                                    input_is_real: Box::new(proof),
                                },
                            )));
                        }
                    }
                }
            }
            if let Obj::FnObj(call) = &fact.element {
                let head = matrix_head_object(&call.head);
                for callable in self.parent_checked_matrix_callables(&head, state)? {
                    let Some(return_set) =
                        self.applied_fn_set_return_set(call, &callable.function.body)
                    else {
                        continue;
                    };
                    let matches=return_set.ir()==fact.set.ir() || match &return_set {
                        Obj::StandardSet(s)=>super::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq(s,target),
                        _=>false,
                    };
                    if matches {
                        return Ok(Some(MatrixMembershipProof::Application(
                            MatrixApplicationMembershipProof {
                                callable: Box::new(callable),
                                return_set,
                            },
                        )));
                    }
                }
            }
        }
        Ok(None)
    }

    pub(crate) fn search_native_matrix_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixEqualityProof>> {
        for (native, other) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Obj::SetFormer(SetFormer::MatrixSet(space)) = native {
                let signature = self.matrix_fn_signature(&space.set, &space.rows, &space.cols);
                let expanded = Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()));
                if let Some(equality) =
                    self.verify_matrix_expanded_equality(expanded, other, state)?
                {
                    return Ok(Some(MatrixEqualityProof::SpaceDefinition(
                        MatrixSpaceDefinitionProof {
                            signature,
                            equality: Box::new(equality),
                        },
                    )));
                }
            }
            if let Obj::MatrixOperator(operator) = native {
                if let Some(expression) = self.matrix_scalar_definition(operator) {
                    if let Some(equality) =
                        self.verify_matrix_expanded_equality(expression.clone(), other, state)?
                    {
                        return Ok(Some(MatrixEqualityProof::ScalarDefinition(
                            MatrixScalarDefinitionProof {
                                expression,
                                equality: Box::new(equality),
                            },
                        )));
                    }
                } else {
                    for callable in self.parent_checked_matrix_callables(native, state)? {
                        let function = Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                            callable.function.clone(),
                        ));
                        if let Some(equality) =
                            self.verify_matrix_expanded_equality(function, other, state)?
                        {
                            return Ok(Some(MatrixEqualityProof::FunctionDefinition(
                                MatrixFunctionDefinitionProof {
                                    callable: Box::new(callable),
                                    equality: Box::new(equality),
                                },
                            )));
                        }
                    }
                }
            }
            if let Obj::FnObj(call) = native {
                let head = matrix_head_object(&call.head);
                for callable in self.parent_checked_matrix_callables(&head, state)? {
                    let Some(body) = self.matrix_component_body(call, &callable) else {
                        continue;
                    };
                    let reduction = self.reduce_native_matrix_component(&body, state, 0)?;
                    if let Some(equality) =
                        self.verify_matrix_expanded_equality(reduction.value.clone(), other, state)?
                    {
                        return Ok(Some(MatrixEqualityProof::ComponentDefinition(
                            MatrixComponentDefinitionProof {
                                callable: Box::new(callable),
                                body,
                                reduction,
                                equality: Box::new(equality),
                            },
                        )));
                    }
                }
            }
        }
        Ok(None)
    }

    // Definition-owned beta steps, with the inherited proof ceiling and each
    // actual application's domain evidence. This never reopens truth search.
    fn reduce_native_matrix_component(
        &mut self,
        body: &Obj,
        state: VerifyState,
        depth: usize,
    ) -> RuntimeResult<MatrixComponentReduction> {
        let unchanged = || MatrixComponentReduction {
            value: body.clone(),
            evidence: MatrixComponentReductionEvidence::Unchanged,
        };
        if depth >= crate::execute::execute_eval_stmt::helper::MAX_EVAL_DEPTH {
            return Ok(unchanged());
        }
        if let Obj::ComplexOperator(ComplexOperator::Conjugate(x)) = body {
            let argument = self.reduce_native_matrix_component(&x.arg, state, depth + 1)?;
            let value = Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate {
                arg: Box::new(argument.value.clone()),
            }));
            return Ok(MatrixComponentReduction {
                value,
                evidence: MatrixComponentReductionEvidence::ConjugateArgument(Box::new(argument)),
            });
        }
        let Obj::FnObj(call) = body else {
            return Ok(unchanged());
        };
        let head = matrix_head_object(&call.head);
        let has_native = self
            .exact_property_object_values_of_shapes(&head, &[EqualToObjShape::Other])
            .iter()
            .any(|(peer, _)| matches!(peer, Obj::MatrixOperator(_)));
        if !has_native {
            return Ok(unchanged());
        }
        let VerifyObjWellDefinedResult::Success(wd) =
            self.verify_obj_well_definedness(body, state)?
        else {
            return Ok(unchanged());
        };
        for callable in self.parent_checked_matrix_callables(&head, state)? {
            let Some(expanded) = self.matrix_component_body(call, &callable) else {
                continue;
            };
            let continuation = self.reduce_native_matrix_component(&expanded, state, depth + 1)?;
            return Ok(MatrixComponentReduction {
                value: continuation.value.clone(),
                evidence: MatrixComponentReductionEvidence::NativeApplication(
                    MatrixNestedApplicationReduction {
                        application_well_defined: Box::new(wd),
                        callable: Box::new(callable),
                        body: expanded,
                        continuation: Box::new(continuation),
                    },
                ),
            });
        }
        Ok(unchanged())
    }

    fn verify_matrix_expanded_equality(
        &mut self,
        left: Obj,
        right: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<MatrixDefinitionResidualProof>> {
        let residual: Fact = AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right: right.clone(),
            line_file: None,
        })
        .into();
        let proof = self.verify_fact(&residual, state)?;
        if !proof.is_failed() {
            return Ok(Some(MatrixDefinitionResidualProof::Verified(Box::new(
                proof,
            ))));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) = residual else {
            unreachable!()
        };
        let left_beta = self.matrix_residual_beta(&residual.left, state)?;
        let right_beta = self.matrix_residual_beta(&residual.right, state)?;
        if !matches!(left_beta, MatrixResidualBeta::Unchanged(_))
            || !matches!(right_beta, MatrixResidualBeta::Unchanged(_))
        {
            let goal: Fact = AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: left_beta.value().clone(),
                right: right_beta.value().clone(),
                line_file: None,
            })
            .into();
            let proof = self.verify_fact(&goal, state)?;
            if !proof.is_failed() {
                return Ok(Some(MatrixDefinitionResidualProof::CheckedBeta(
                    MatrixResidualBetaProof {
                        left: left_beta,
                        right: right_beta,
                        proof: Box::new(proof),
                    },
                )));
            }
        }
        if !exact_matrix_evaluation_source(&residual.left)
            || !exact_matrix_evaluation_source(&residual.right)
        {
            return Ok(None);
        }
        let mut context = crate::execute::execute_eval_stmt::helper::ActiveAlgoCalls::new();
        context.proof_mode = true;
        context.function_proof_state = state;
        let Ok(left_value) = crate::execute::execute_eval_stmt::evaluate_obj::evaluate_obj(
            self,
            &residual.left,
            0,
            &mut context,
        )?
        else {
            return Ok(None);
        };
        let Ok(right_value) = crate::execute::execute_eval_stmt::evaluate_obj::evaluate_obj(
            self,
            &residual.right,
            0,
            &mut context,
        )?
        else {
            return Ok(None);
        };
        if !context.algo_evaluations.is_empty()
            || !context
                .function_evaluations
                .iter()
                .all(|p| exact_matrix_evaluation_source(p.expansion.expanded_body()))
            || !crate::rational_expression::objs_equal_by_rational_expression_evaluation(
                &left_value,
                &right_value,
            )
        {
            return Ok(None);
        }
        Ok(Some(MatrixDefinitionResidualProof::ExactEvaluation(
            MatrixExactEvaluationProof {
                left_value,
                right_value,
                cited_equal_fact_ids: context.cited_equal_fact_ids,
                matrix_scalar_evaluations: context.matrix_scalar_evaluations,
                aggregate_evaluations: context.aggregate_evaluations,
                function_evaluations: context.function_evaluations,
            },
        )))
    }

    fn matrix_residual_beta(
        &mut self,
        value: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<MatrixResidualBeta> {
        if matches!(value, Obj::FnObj(_)) {
            if let VerifyObjWellDefinedResult::Success(wd) =
                self.verify_obj_well_definedness(value, state)?
            {
                if let Some((source, body)) = self.parent_checked_beta_body(value, &wd, state)? {
                    return Ok(MatrixResidualBeta::Expanded(MatrixResidualBetaExpansion {
                        application_well_defined: Box::new(wd),
                        source,
                        body,
                    }));
                }
            }
        }
        Ok(MatrixResidualBeta::Unchanged(value.clone()))
    }
}

pub(crate) fn matrix_head_object(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(x) => Obj::Identifier(x.clone()),
        FnObjHead::Object(x) => x.as_ref().clone(),
        FnObjHead::AnonymousFnLiteral(x) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(x.as_ref().clone()))
        }
        FnObjHead::InstantiatedTemplateObj(x) => Obj::InstantiatedTemplateObj(x.clone()),
        FnObjHead::FieldAccess(x) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x.clone()))
        }
    }
}

impl MatrixMembershipProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::ExtendedScalar(p) => match p {
                super::matrix_operations::ExtendedMatrixScalarMembershipProof::Rank(_) => {
                    "MatrixRankNatural"
                }
                super::matrix_operations::ExtendedMatrixScalarMembershipProof::Cofactor(_) => {
                    "MatrixCofactorCarrier"
                }
                super::matrix_operations::ExtendedMatrixScalarMembershipProof::InnerProduct(_) => {
                    "FiniteInnerProductCarrier"
                }
                super::matrix_operations::ExtendedMatrixScalarMembershipProof::EuclideanNorm(_) => {
                    "EuclideanNormReal"
                }
                super::matrix_operations::ExtendedMatrixScalarMembershipProof::FrobeniusNorm(_) => {
                    "MatrixFrobeniusNormReal"
                }
            },
            Self::Space(_) => "MatrixSpaceMember",
            Self::Function(_) => "MatrixFunctionMember",
            Self::Application(_) => "MatrixApplicationInCodomain",
            Self::ScalarComplex(_) => "MatrixScalarComplex",
            Self::ScalarReal(_) => "MatrixScalarReal",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::ExtendedScalar(_) => {
                "the checked finite matrix construction has its standard scalar carrier"
            }
            Self::Space(_) => "matrix(S,m,n) is its exact two-argument function space",
            Self::Function(_) => {
                "the checked constructor has the target complete domain and return upper bound"
            }
            Self::Application(_) => {
                "the checked matrix function call returns in its scalar carrier"
            }
            Self::ScalarComplex(_) => "det and trace of complex square matrices are complex",
            Self::ScalarReal(_) => "det and trace of a proved real square matrix are real",
        }
    }
}
impl MatrixEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SpaceDefinition(_) => "MatrixSpaceDefinition",
            Self::FunctionDefinition(_) => "MatrixFunctionDefinition",
            Self::ComponentDefinition(_) => "MatrixComponentDefinition",
            Self::ScalarDefinition(_) => "MatrixScalarDefinition",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SpaceDefinition(_) => "matrix(S,m,n) = fn(r 1..m,c 1..n) S",
            Self::FunctionDefinition(_) => {
                "a matrix constructor equals its defining finite-domain function"
            }
            Self::ComponentDefinition(_) => {
                "a matrix component is the checked defining function body"
            }
            Self::ScalarDefinition(_) => {
                "determinant (orders 0/1/2) or trace expands by its exact definition"
            }
        }
    }
}

pub enum MatrixDefinitionResidualProof {
    Verified(Box<VerifyFactResult>),
    CheckedBeta(MatrixResidualBetaProof),
    ExactEvaluation(MatrixExactEvaluationProof),
}
pub struct MatrixResidualBetaProof {
    pub left: MatrixResidualBeta,
    pub right: MatrixResidualBeta,
    pub proof: Box<VerifyFactResult>,
}
pub enum MatrixResidualBeta {
    Unchanged(Obj),
    Expanded(MatrixResidualBetaExpansion),
}
pub struct MatrixResidualBetaExpansion {
    pub application_well_defined: Box<ObjWellDefinedProof>,
    pub source: crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::ParentCheckedBetaFunctionBody,
    pub body: Obj,
}
impl MatrixResidualBeta {
    fn value(&self) -> &Obj {
        match self {
            Self::Unchanged(value) => value,
            Self::Expanded(p) => &p.body,
        }
    }
}
pub struct MatrixExactEvaluationProof {
    pub left_value: Obj,
    pub right_value: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub matrix_scalar_evaluations: Vec<crate::execute::execute_eval_stmt::aggregate_evaluation_result::MatrixScalarEvaluationResult>,
    pub aggregate_evaluations: Vec<crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult>,
    pub function_evaluations: Vec<crate::execute::execute_eval_stmt::aggregate_evaluation_result::FunctionApplicationEvaluationResult>,
}
fn exact_matrix_evaluation_source(value: &Obj) -> bool {
    match value {
        Obj::MatrixOperator(operator) => operator
            .operand_refs()
            .iter()
            .all(|x| exact_matrix_evaluation_source(x)),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(x)) => exact_matrix_evaluation_source(&x.arg),
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(x)) => {
            exact_matrix_evaluation_source(&x.arg)
        }
        Obj::ComplexOperator(ComplexOperator::RealPart(x)) => {
            exact_matrix_evaluation_source(&x.arg)
        }
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(x)) => {
            exact_matrix_evaluation_source(&x.arg)
        }
        Obj::Literal(Literal::Number(_) | Literal::ImaginaryUnit(_)) => true,
        Obj::Identifier(_) => true, // binder/callee names; unresolved values cannot evaluate
        Obj::ArithmeticOperator(operator) => match operator {
            ArithmeticOperator::Add(x) => {
                exact_matrix_evaluation_source(&x.left) && exact_matrix_evaluation_source(&x.right)
            }
            ArithmeticOperator::Sub(x) => {
                exact_matrix_evaluation_source(&x.left) && exact_matrix_evaluation_source(&x.right)
            }
            ArithmeticOperator::Mul(x) => {
                exact_matrix_evaluation_source(&x.left) && exact_matrix_evaluation_source(&x.right)
            }
            ArithmeticOperator::Div(x) => {
                exact_matrix_evaluation_source(&x.left) && exact_matrix_evaluation_source(&x.right)
            }
            ArithmeticOperator::Pow(x) => {
                crate::rational_expression::exact_rational::EvalRational::from_obj(&x.exponent)
                    .is_some_and(|n| n.to_i128_if_integer().is_some())
                    && exact_matrix_evaluation_source(&x.base)
            }
            ArithmeticOperator::Neg(x) => exact_matrix_evaluation_source(&x.arg),
            ArithmeticOperator::Abs(x) => exact_matrix_evaluation_source(&x.arg),
            ArithmeticOperator::Floor(x) => exact_matrix_evaluation_source(&x.arg),
            ArithmeticOperator::Ceil(x) => exact_matrix_evaluation_source(&x.arg),
            ArithmeticOperator::Sign(x) => exact_matrix_evaluation_source(&x.arg),
            ArithmeticOperator::Min(x) => {
                exact_matrix_evaluation_source(&x.left) && exact_matrix_evaluation_source(&x.right)
            }
            ArithmeticOperator::Max(x) => {
                exact_matrix_evaluation_source(&x.left) && exact_matrix_evaluation_source(&x.right)
            }
        },
        Obj::ComplexOperator(ComplexOperator::Conjugate(x)) => {
            exact_matrix_evaluation_source(&x.arg)
        }
        Obj::FnObj(x) => x
            .body
            .iter()
            .flatten()
            .all(|x| exact_matrix_evaluation_source(x)),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(x)) => {
            exact_matrix_evaluation_source(&x.equal_to)
        }
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(x)) => {
            exact_matrix_evaluation_source(&x.func)
        }
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_)) => true, // finite enumeration is exact
        _ => false,
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/native_matrix/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "../../../tests/unit/execute/native_matrix/completion.rs"]
mod completion_tests;
