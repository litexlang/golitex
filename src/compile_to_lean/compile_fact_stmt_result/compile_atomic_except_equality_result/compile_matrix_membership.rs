use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal;
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixMembershipProof, MatrixSpaceMembershipEvidence,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_membership(
        &self,
        fact: &InFact,
        proof: &MatrixMembershipProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let value = self.compile_object_reference(&fact.element, position)?;
        let target = self.compile_object_reference(&fact.set, position)?;
        let member = match proof {
            MatrixMembershipProof::ExtendedScalar(crate::execute::execute_fact_stmt::matrix_operations::ExtendedMatrixScalarMembershipProof::Rank(p)) => self.compile_matrix_rank_member(fact,&p.target,position)?,
            MatrixMembershipProof::ExtendedScalar(crate::execute::execute_fact_stmt::matrix_operations::ExtendedMatrixScalarMembershipProof::Cofactor(p)) => self.compile_matrix_cofactor_member(fact,p,position)?,
            MatrixMembershipProof::ExtendedScalar(crate::execute::execute_fact_stmt::matrix_operations::ExtendedMatrixScalarMembershipProof::EuclideanNorm(p)) => self.compile_matrix_norm_member(fact,&p.target,true,position)?,
            MatrixMembershipProof::ExtendedScalar(crate::execute::execute_fact_stmt::matrix_operations::ExtendedMatrixScalarMembershipProof::FrobeniusNorm(p)) => self.compile_matrix_norm_member(fact,&p.target,false,position)?,
            MatrixMembershipProof::ExtendedScalar(crate::execute::execute_fact_stmt::matrix_operations::ExtendedMatrixScalarMembershipProof::InnerProduct(p)) => self.compile_finite_inner_product_member(fact,p,position)?,
            MatrixMembershipProof::ScalarComplex(_) if matches!(&fact.element,Obj::MatrixOperator(MatrixOperator::Determinant(_))) && fact.set==Obj::StandardSet(StandardSet::C) => format!("(Litex.matrixDeterminantInC {value})"),
            MatrixMembershipProof::ScalarComplex(_) if matches!(&fact.element,Obj::MatrixOperator(MatrixOperator::Trace(_))) && fact.set==Obj::StandardSet(StandardSet::C) => format!("(Litex.matrixTraceInC {value})"),
            MatrixMembershipProof::ScalarReal(p) if fact.set==Obj::StandardSet(StandardSet::R) => self.compile_matrix_square_scalar_real(&fact.element,&p.input_is_real,position)?,
            MatrixMembershipProof::Space(proof) => {
                let Obj::SetFormer(SetFormer::MatrixSet(space)) = &fact.set else {
                    return Err(LeanCompileError::unsupported("Matrix/MembershipSubject"));
                };
                Self::validate_matrix_signature(space, &proof.signature)?;
                let (checked, widen) = match &proof.membership {
                    MatrixSpaceMembershipEvidence::Exact(checked) => (checked, false),
                    MatrixSpaceMembershipEvidence::RealToComplex(checked) => (checked, true),
                };
                let mut source_signature = proof.signature.clone();
                if widen {
                    if source_signature.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C) {
                        return Err(LeanCompileError::unsupported("Matrix/ScalarWidening"));
                    }
                    source_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R));
                }
                let signature = Obj::FunctionSpace(FunctionSpace::FnSet(source_signature));
                if !matches!(source_subject(checked)?, Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir() == fact.element.ir() && f.set.ir() == signature.ir())
                {
                    return Err(LeanCompileError::unsupported("Matrix/MembershipPremise"));
                }
                let member = self.compile_verify(checked, position)?.1;
                if widen {
                    format!("(Litex.functionRealToComplex {member})")
                } else {
                    member
                }
            }
            MatrixMembershipProof::Function(proof) => {
                self.validate_function_carrier_signature(&fact.set, &proof.target)?;
                if !function_domains_alpha_equal(&proof.callable.function.body, &proof.target) {
                    return Err(LeanCompileError::unsupported("Matrix/CompleteDomain"));
                }
                let member =
                    self.compile_matrix_callable_member(&fact.element, &proof.callable, position)?;
                match (
                    proof.callable.function.body.ret_set.as_ref(),
                    proof.target.ret_set.as_ref(),
                ) {
                    (Obj::StandardSet(StandardSet::R), Obj::StandardSet(StandardSet::C)) => {
                        format!("(Litex.functionRealToComplex {member})")
                    }
                    (source, target) if source.ir() == target.ir() => member,
                    _ => return Err(LeanCompileError::unsupported("Matrix/ReturnCarrier")),
                }
            }
            MatrixMembershipProof::Application(proof) => {
                let Obj::FnObj(call) = &fact.element else {
                    return Err(LeanCompileError::unsupported("Matrix/CallSubject"));
                };
                if call.body.len() != 1
                    || proof.return_set.ir() != proof.callable.function.body.ret_set.ir()
                {
                    return Err(LeanCompileError::unsupported("Matrix/CallReturn"));
                }
                let head = match call.head.as_ref() {
                    FnObjHead::Identifier(i) => Obj::Identifier(i.clone()),
                    FnObjHead::Object(o) => o.as_ref().clone(),
                    _ => return Err(LeanCompileError::unsupported("Matrix/CallHead")),
                };
                let interface =
                    self.compile_matrix_callable_member(&head, &proof.callable, position)?;
                let member = position.with_visible_wd(&fact.element, &mut |wd, producer| {
                    let DetailedObjWellDefinedProof::ByDef { proof:ObjWellDefinedProofByDef::FnObj(p), .. } = (wd).detailed_ref() else {
                        return Err(LeanCompileError::unsupported("Matrix/CallWD"));
                    };
                    let scope = SourcePosition::new(Some(producer),SourceOwner::WD(wd),0);
                    let (input, domain) = self.compile_fn_return_domain(call,p,&proof.callable.function.body,&scope)?;
                    let f = self.compile_object_reference(&head,position)?;
                    let signature = self.compile_matrix_callable_signature(&proof.callable, &SourcePosition {before:usize::MAX, ..scope})?;
                    Ok(format!("(let _litex_matrix_signature := {signature}; Litex.FunctionSemantics.call_mem _litex_matrix_signature.domain _litex_matrix_signature.output (Litex.denote {f}) {input} {interface} {domain})"))
                })?.ok_or_else(||LeanCompileError::unsupported("Matrix/CallProducer"))?;
                if fact.set.ir() == proof.return_set.ir() {
                    member
                } else {
                    let (Obj::StandardSet(source), Obj::StandardSet(target)) =
                        (&proof.return_set, &fact.set)
                    else {
                        return Err(LeanCompileError::unsupported("Matrix/CallInclusion"));
                    };
                    standard_inclusion_term(source, target, &value, &member)?
                }
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/MembershipRule")),
        };
        Ok(format!("(show Litex.In {value} {target} from {member})"))
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_matrix_return(
        &self,
        fact: &InFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::RealMatrixApplicationCodomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if fact.set != Obj::StandardSet(StandardSet::R) || proof.applied_return != fact.set {
            return Err(LeanCompileError::unsupported("Matrix/RealReturnSubject"));
        }
        let (signature, member) =
            self.compile_real_matrix_array_member(&proof.array, "_litex_real_matrix", position)?;
        let Obj::FnObj(call) = &fact.element else {
            return Err(LeanCompileError::unsupported("Matrix/RealReturnCall"));
        };
        let FnObjHead::Object(head) = call.head.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/RealReturnHead"));
        };
        let Obj::MatrixOperator(head) = head.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/RealReturnHead"));
        };
        if *head != proof.array.operator {
            return Err(LeanCompileError::unsupported(
                "Matrix/RealReturnOperatorSubject",
            ));
        }
        let root = self.compile_object_reference(
            &Obj::MatrixOperator(proof.array.operator.clone()),
            position,
        )?;
        let value = self.compile_object_reference(&fact.element, position)?;
        position.with_visible_wd(&fact.element,&mut |wd,producer| {
            let DetailedObjWellDefinedProof::ByDef {proof:ObjWellDefinedProofByDef::FnObj(p),..}=(wd).detailed_ref() else {return Err(LeanCompileError::unsupported("Matrix/RealReturnWD"))};
            let scope=SourcePosition::new(Some(producer),SourceOwner::WD(wd),0);
            let (input,domain)=self.compile_fn_return_domain(call,p,&proof.array.signature,&scope)?;
            Ok(format!("(let _litex_real_matrix := {root}; let _litex_real_signature := {signature}; (show Litex.In {value} Litex.R from Litex.FunctionSemantics.call_mem _litex_real_signature.domain _litex_real_signature.output (Litex.denote _litex_real_matrix) {input} {member} {domain}))"))
        })?.ok_or_else(||LeanCompileError::unsupported("Matrix/RealReturnProducer"))
    }

    fn compile_real_matrix_array_member(
        &self,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::RealNativeArrayCarrierProof,
        root: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if matches!(
            proof.operator,
            MatrixOperator::Add(_) | MatrixOperator::Subtract(_)
        ) {
            let (left, right, rows, cols) = match &proof.operator {
                MatrixOperator::Add(m) => (&m.left, &m.right, &m.rows, &m.cols),
                MatrixOperator::Subtract(m) => (&m.left, &m.right, &m.rows, &m.cols),
                _ => unreachable!(),
            };
            if proof.real_operands.len() != 2 {
                return Err(LeanCompileError::unsupported("Matrix/RealOperandArity"));
            }
            Self::validate_matrix_signature(
                &MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::R)),
                    rows: rows.clone(),
                    cols: cols.clone(),
                },
                &proof.signature,
            )?;
            let a = self.compile_declared_real_matrix_operand(
                &proof.real_operands[0],
                left,
                rows,
                cols,
                position,
            )?;
            let b = self.compile_declared_real_matrix_operand(
                &proof.real_operands[1],
                right,
                rows,
                cols,
                position,
            )?;
            let rows = self.compile_object_reference(rows, position)?;
            let cols = self.compile_object_reference(cols, position)?;
            return Ok((
                format!("(Litex.matrixEntrywiseSignature {rows} {cols} .real)"),
                format!("(Litex.matrixEntrywiseInRealFnSet {root} {a} {b})"),
            ));
        }
        let (rows, cols, input) = match &proof.operator {
            MatrixOperator::ZeroMatrix(m) if proof.real_operands.is_empty() => {
                (&m.rows, &m.cols, None)
            }
            MatrixOperator::IdentityMatrix(m) if proof.real_operands.is_empty() => {
                (&m.order, &m.order, None)
            }
            MatrixOperator::Transpose(m) if proof.real_operands.len() == 1 => (
                &m.cols,
                &m.rows,
                Some((&m.matrix, &m.rows, &m.cols, "transpose")),
            ),
            MatrixOperator::ConjugateTranspose(m) if proof.real_operands.len() == 1 => (
                &m.cols,
                &m.rows,
                Some((&m.matrix, &m.rows, &m.cols, "conjugateTranspose")),
            ),
            _ => return Err(LeanCompileError::unsupported("Matrix/RealArrayOperator")),
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(StandardSet::R)),
                rows: rows.clone(),
                cols: cols.clone(),
            },
            &proof.signature,
        )?;
        let signature = format!(
            "(Litex.matrixEntrywiseSignature {} {} .real)",
            self.compile_object_reference(rows, position)?,
            self.compile_object_reference(cols, position)?
        );
        match input {
            None => match &proof.operator {
                MatrixOperator::IdentityMatrix(_) => {
                    Ok((signature, format!("(Litex.identityMatrixInFnSet {root})")))
                }
                _ => Ok((signature, format!("(Litex.zeroMatrixInFnSet {root})"))),
            },
            Some((matrix, input_rows, input_cols, name)) => {
                let member = self.compile_declared_real_matrix_operand(
                    &proof.real_operands[0],
                    matrix,
                    input_rows,
                    input_cols,
                    position,
                )?;
                Ok((
                    signature,
                    format!("(Litex.{name}InRealFnSet {root} {member})"),
                ))
            }
        }
    }
    fn compile_declared_real_matrix_operand(
        &self,
        operand: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::DeclaredRealOperandProof,
        matrix: &Obj,
        input_rows: &Obj,
        input_cols: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::DeclaredRealOperandSource;
        let expected = Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
            set: Box::new(Obj::StandardSet(StandardSet::R)),
            rows: Box::new(input_rows.clone()),
            cols: Box::new(input_cols.clone()),
        }));
        if operand.requirement.element.ir() != matrix.ir()
            || operand.requirement.set.ir() != expected.ir()
        {
            return Err(LeanCompileError::unsupported("Matrix/RealOperandSubject"));
        }
        let member = match &operand.source {
            DeclaredRealOperandSource::Known(p) => {
                if !matches!(&p.fact,AtomicFact::InFact(f) if f.element.ir()==matrix.ir() && f.set.ir()==expected.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/RealOperandKnownSubject",
                    ));
                }
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                    p.searched_proof.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("Matrix/RealOperandKnownRule"));
                };
                self.compile_known_atomic(known, &p.fact, position)?
            }
            DeclaredRealOperandSource::NativeArray(p)
                if matrix.ir() == Obj::MatrixOperator(p.operator.clone()).ir() =>
            {
                self.validate_function_carrier_signature(&expected, &p.signature)?;
                {
                    let root = self.compile_object_reference(matrix, position)?;
                    self.compile_real_matrix_array_member(p, &root, position)?.1
                }
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/RealOperandRule")),
        };
        Ok(member)
    }
}
