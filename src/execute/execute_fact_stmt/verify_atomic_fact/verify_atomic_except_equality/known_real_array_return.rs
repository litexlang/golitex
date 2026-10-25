//! Read real return types from checked native array constructors and declared
//! operand carriers. Parent application WD owns shape, arguments and guards.
use super::result::AtomicExceptEqualityFactKnownProof;
use super::search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty;
use crate::execute::execute_fact_stmt::matrix_operations::real_signature::real_layout;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::StructuralMembershipProof;
use crate::prelude::*;

pub struct RealMatrixApplicationCodomainProof {
    pub array: RealNativeArrayCarrierProof,
    pub applied_return: Obj,
}
pub struct RealNativeArrayCarrierProof {
    pub operator: MatrixOperator,
    pub signature: FnSet,
    pub real_operands: Vec<DeclaredRealOperandProof>,
}
pub struct DeclaredRealOperandProof {
    pub requirement: InFact,
    pub source: DeclaredRealOperandSource,
}
pub enum DeclaredRealOperandSource {
    Known(AtomicExceptEqualityFactKnownProof),
    Structural(StructuralMembershipProof),
    Special(Box<InFactSearchProofByKnownSpecialProperty>),
    NativeArray(RealNativeArrayCarrierProof),
    NativeApplication(RealMatrixApplicationCodomainProof),
    RealArithmetic(DeclaredRealArithmeticProof),
}
pub struct DeclaredRealArithmeticProof {
    pub expression: Obj,
    pub operands: Vec<DeclaredRealOperandProof>,
}
impl Runtime {
    pub(super) fn known_real_matrix_application_codomain(
        &mut self,
        fact: &InFact,
    ) -> Option<RealMatrixApplicationCodomainProof> {
        let mut budget = 256;
        self.real_matrix_application_codomain_inner(fact, 0, &mut budget)
    }
    fn real_matrix_application_codomain_inner(
        &mut self,
        fact: &InFact,
        depth: usize,
        budget: &mut usize,
    ) -> Option<RealMatrixApplicationCodomainProof> {
        if depth >= 32 || *budget == 0 || fact.set != Obj::StandardSet(StandardSet::R) {
            return None;
        }
        let Obj::FnObj(call) = &fact.element else {
            return None;
        };
        let head =
            crate::execute::execute_fact_stmt::multivariable::expression::call_head(&call.head);
        let Obj::MatrixOperator(operator) = head else {
            return None;
        };
        let array = self.real_native_array_carrier(&operator, depth + 1, budget)?;
        let applied_return = self.applied_fn_set_return_set(call, &array.signature)?;
        if applied_return != fact.set {
            return None;
        }
        Some(RealMatrixApplicationCodomainProof {
            array,
            applied_return,
        })
    }
    fn real_native_array_carrier(
        &mut self,
        operator: &MatrixOperator,
        depth: usize,
        budget: &mut usize,
    ) -> Option<RealNativeArrayCarrierProof> {
        if depth >= 32 || *budget == 0 {
            return None;
        }
        *budget -= 1;
        let layout = real_layout(operator)?;
        let space = if layout.vector {
            Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                set: Box::new(Obj::StandardSet(StandardSet::R)),
                n: Box::new(layout.rows),
            }))
        } else {
            crate::execute::execute_fact_stmt::native_matrix::matrix_space(
                Obj::StandardSet(StandardSet::R),
                layout.rows,
                layout.cols,
            )
        };
        let signature = self.function_space_signature(&space)?;
        let mut real_operands = Vec::new();
        for (element, set) in layout.real_domains {
            real_operands.push(self.declared_real_operand(&element, &set, depth + 1, budget)?);
        }
        Some(RealNativeArrayCarrierProof {
            operator: operator.clone(),
            signature,
            real_operands,
        })
    }
    fn declared_real_operand(
        &mut self,
        element: &Obj,
        set: &Obj,
        depth: usize,
        budget: &mut usize,
    ) -> Option<DeclaredRealOperandProof> {
        if depth >= 32 || *budget == 0 {
            return None;
        }
        *budget -= 1;
        let requirement = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: set.clone(),
            line_file: None,
        };
        let source = if let Some(proof) =
            self.lookup_known_atomic_premise(requirement.clone().into())
        {
            DeclaredRealOperandSource::Known(proof)
        } else if let Some(proof) = match set {
            Obj::StandardSet(carrier) => self.search_structural_membership(element, carrier),
            _ => None,
        } {
            DeclaredRealOperandSource::Structural(proof)
        } else if let Some(proof) = self.finite_tuple_in_standard_function_space(&requirement) {
            DeclaredRealOperandSource::Special(Box::new(
                InFactSearchProofByKnownSpecialProperty::FiniteTupleInStandardFunctionSpace(proof),
            ))
        } else if let Some(proof) =
            self.search_in_fact_proof_by_known_special_property(&requirement)
        {
            DeclaredRealOperandSource::Special(Box::new(proof))
        } else if let Obj::MatrixOperator(operator) = element {
            let expected = self.function_space_signature(set)?;
            let proof = self.real_native_array_carrier(operator, depth + 1, budget)?;
            if !crate::execute::execute_fact_stmt::fn_sets_alpha_equal(&proof.signature, &expected)
            {
                return None;
            }
            DeclaredRealOperandSource::NativeArray(proof)
        } else if let Some(proof) =
            self.real_matrix_application_codomain_inner(&requirement, depth + 1, budget)
        {
            DeclaredRealOperandSource::NativeApplication(proof)
        } else if *set == Obj::StandardSet(StandardSet::R) {
            let Obj::ArithmeticOperator(operator) = element else {
                return None;
            };
            let inputs: Vec<&Obj> = match operator {
                ArithmeticOperator::Add(x) => vec![&x.left, &x.right],
                ArithmeticOperator::Sub(x) => vec![&x.left, &x.right],
                ArithmeticOperator::Mul(x) => vec![&x.left, &x.right],
                ArithmeticOperator::Div(x) => vec![&x.left, &x.right],
                ArithmeticOperator::Neg(x) => vec![&x.arg],
                _ => return None,
            };
            let mut operands = Vec::new();
            for input in inputs {
                operands.push(self.declared_real_operand(input, set, depth + 1, budget)?);
            }
            DeclaredRealOperandSource::RealArithmetic(DeclaredRealArithmeticProof {
                expression: element.clone(),
                operands,
            })
        } else {
            return None;
        };
        Some(DeclaredRealOperandProof {
            requirement,
            source,
        })
    }
}

/// Covariance of the declared numeric return set, with exactly the same finite
/// sequence arguments and guards. This is membership, not equality of fn sets.
pub struct DeclaredNumericSequenceCarrierProof {
    pub declared_signature: FnSet,
    pub target_signature: FnSet,
    pub widened_signature: FnSet,
    pub source_return: StandardSet,
    pub target_return: StandardSet,
    pub signature_match:
        Box<crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof>,
}
impl Runtime {
    pub(super) fn declared_numeric_sequence_carrier(
        &mut self,
        fact: &InFact,
    ) -> Option<DeclaredNumericSequenceCarrierProof> {
        use super::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq;
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
        let (
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)),
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)),
        ) = (&fact.element, &fact.set)
        else {
            return None;
        };
        let target_signature = self.function_space_signature(&fact.set)?;
        let (Obj::StandardSet(source_return), Obj::StandardSet(target_return)) =
            (&*function.body.ret_set, &*target_signature.ret_set)
        else {
            return None;
        };
        if !standard_set_is_subset_eq(source_return, target_return) {
            return None;
        }
        let mut widened_signature = function.body.clone();
        widened_signature.ret_set = target_signature.ret_set.clone();
        let comparison = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::FunctionSpace(FunctionSpace::FnSet(widened_signature.clone())),
            right: Obj::FunctionSpace(FunctionSpace::FnSet(target_signature.clone())),
            line_file: None,
        };
        let signature_match = search_equal_fact_proof_by_they_are_the_same(&comparison)?;
        Some(DeclaredNumericSequenceCarrierProof {
            declared_signature: function.body.clone(),
            source_return: source_return.clone(),
            target_return: target_return.clone(),
            target_signature,
            widened_signature,
            signature_match: Box::new(signature_match.into()),
        })
    }
}
