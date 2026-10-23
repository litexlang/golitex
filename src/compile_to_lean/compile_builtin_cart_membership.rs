use crate::compile_to_lean::compile_fact_stmt_result::validate_finite_signature;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate;
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainSourceProof, FunctionDomainComparisonProof,
    FunctionDomainMatchProof,
};
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_builtin_cart_membership(
        &self,
        member: &InFact,
        domain: &FunctionDomainMatchProof,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Some(Fact::AtomicFact(AtomicFact::EqualFact(definition))) = requirements.first() else {
            return Err(LeanCompileError::unsupported("CartTheorem/CarrierEquality"));
        };
        let Obj::ProductShape(ProductShape::Cart(cart)) = &definition.right else {
            return Err(LeanCompileError::unsupported("CartTheorem/CarrierEquality"));
        };
        let CompleteFunctionDomainSourceProof::FiniteFunction(finite) = &domain.source.source
        else {
            return Err(LeanCompileError::unsupported(
                "CartTheorem/CompleteDomainSource",
            ));
        };
        validate_finite_signature(finite)?;
        let n = cart.args.len();
        if definition.left.ir() != member.set.ir()
            || requirements.len() != n + 1
            || references.len() != requirements.len()
            || finite.source.dimension() != n
            || finite.signature.ir() != domain.source.signature.ir()
            || !matches!(
                domain.comparison,
                FunctionDomainComparisonProof::AlphaEquivalent
            )
            || !function_domains_alpha_equal(&finite.signature, &domain.target)
        {
            return Err(LeanCompileError::unsupported("CartTheorem/CompleteDomain"));
        }
        let mut factors = cart.args.iter();
        let mut output = factors
            .next()
            .map(|x| x.as_ref().clone())
            .unwrap_or_else(|| Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })));
        for factor in factors {
            output = Obj::SetOperator(SetOperator::Union(Union {
                left: Box::new(output),
                right: factor.clone(),
            }));
        }
        if output.ir() != domain.target.ret_set.ir() {
            return Err(LeanCompileError::unsupported("CartTheorem/TargetFactors"));
        }
        let (source_cart, source_member) =
            self.compile_cart_shape_member(&member.element, &finite.source, position)?;
        let target_cart = self.compile_object_reference(&definition.right, position)?;
        let target = self.compile_object_reference(&member.set, position)?;
        let mut coordinates = Vec::new();
        for index in 0..n {
            let (coordinate, equality) = if let KnownTupleShapeProof::TupleEquality(tuple_source) =
                &finite.source
            {
                let tuple_obj = Obj::ProductShape(ProductShape::Tuple(tuple_source.value.clone()));
                let tuple = self.compile_object_reference(&tuple_obj, position)?;
                let same = self.compile_equality_path(
                    &member.element,
                    &tuple_obj,
                    &tuple_source.tuple_equal,
                    position,
                )?;
                (tuple_source.value.args[index].as_ref().clone(), format!(
                    "((congrArg (fun _p => Litex.FunctionSemantics.callValue (M := M) _p (Litex.FiniteFunction.index ({index} : Fin {n}))) {same}).trans (Litex.tuple_coordinate {tuple} ({index} : Fin {n})))"))
            } else {
                let coordinate = finite_function_coordinate(&member.element, index)
                    .map_err(|e| LeanCompileError::new("CartTheorem/Coordinate", &e))?;
                (coordinate, format!("(by\n  have _index : Litex.FiniteFunction.index (M := M) ({index} : Fin {n}) = M.number ({} : ℂ) := by norm_num [Litex.FiniteFunction.index]\n  exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function)) _index)", index+1))
            };
            let Fact::AtomicFact(AtomicFact::InFact(premise)) = &requirements[index + 1] else {
                return Err(LeanCompileError::unsupported(
                    "CartTheorem/CoordinateSubject",
                ));
            };
            if premise.element.ir() != coordinate.ir() || premise.set.ir() != cart.args[index].ir()
            {
                return Err(LeanCompileError::unsupported(
                    "CartTheorem/CoordinateSubject",
                ));
            }
            let value = self.compile_normalization_value(&coordinate, position)?;
            let factor = self.compile_object_reference(&cart.args[index], position)?;
            let reference = &references[index + 1];
            coordinates.push(format!("(show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index ({index} : Fin {n}))) (Litex.denote {factor}) from by\n  have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index ({index} : Fin {n})) = {value} := {equality}\n  rw [_coordinate]\n  exact {reference})"));
        }
        let coordinates = finite_vector_proof(&coordinates);
        let carrier_same = &references[0];
        Ok(format!("(by\n  let _source_cart := {source_cart}\n  have _source_member : Litex.In _membership_function _source_cart := {source_member}\n  let _cart := {target_cart}\n  let _target := {target}\n  have _coordinates : ∀ i : Fin {n}, M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index i)) (_cart.val.factors i) := {coordinates}\n  have _member : Litex.In _membership_function _cart := Litex.FiniteFunction.cart_of_coordinates _source_member _coordinates\n  have _carrier_same : Litex.Same _target _cart := {carrier_same}\n  exact Litex.inOfSame _membership_function _membership_function _cart _target (Litex.sameRefl _) _carrier_same.symm _member)"))
    }
}
