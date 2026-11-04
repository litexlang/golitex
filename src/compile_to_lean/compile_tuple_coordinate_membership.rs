use crate::compile_to_lean::compile_fact_stmt_result::finite_call_parts;
use crate::compile_to_lean::helper::finite_vector_proof;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::known_tuple::literal_positive_usize;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_tuple_coordinate_membership(
        &self,
        goal: &InFact,
        rule: &InFactSearchProofByKnownSpecialProperty,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(application) = &goal.element else {
            return Err(LeanCompileError::unsupported("TupleMember/Application"));
        };
        let (receiver, argument) = finite_call_parts(application)?;
        let tuple = match rule {
            InFactSearchProofByKnownSpecialProperty::LiteralTupleNumericCoordinate(p) => &p.tuple,
            InFactSearchProofByKnownSpecialProperty::UniformTupleCoordinateCarrier(p) => &p.tuple,
            _ => return Err(LeanCompileError::unsupported("TupleMember/Rule")),
        };
        let n = tuple.value.args.len();
        if let InFactSearchProofByKnownSpecialProperty::UniformTupleCoordinateCarrier(p) = rule {
            if n == 0
                || p.index.ir() != argument.ir()
                || goal.set != Obj::StandardSet(p.carrier.clone())
                || p.coordinates.len() != n
            {
                return Err(LeanCompileError::unsupported("TupleMember/UniformSubject"));
            }
            let mut members = Vec::new();
            for (value, checked) in tuple.value.args.iter().zip(&p.coordinates) {
                if checked.element.ir() != value.ir() || checked.set != p.carrier {
                    return Err(LeanCompileError::unsupported(
                        "TupleMember/ComponentSubject",
                    ));
                }
                members.push(self.compile_structural(checked, position)?);
            }
            // Uniform membership uses every recorded component proof and the
            // original call's domain proof; the index need not be a numeral.
            let call = position
                .with_visible_wd(&goal.element, &mut |wd, producer| {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof: ObjWellDefinedProofByDef::FnObj(evidence),
                        ..
                    } = wd.detailed_ref()
                    else {
                        return Err(LeanCompileError::unsupported("TupleMember/CallWD"));
                    };
                    let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) =
                        &evidence.domain_fn_set
                    else {
                        return Err(LeanCompileError::unsupported("TupleMember/FiniteDomain"));
                    };
                    if finite.source.dimension() != n {
                        return Err(LeanCompileError::unsupported("TupleMember/Dimension"));
                    }
                    let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                    self.compile_finite_fn_call(application, evidence, finite, &scope)
                })?
                .ok_or_else(|| LeanCompileError::unsupported("TupleMember/Producer"))?;
            let value = Obj::ProductShape(ProductShape::Tuple(tuple.value.clone()));
            let same =
                self.compile_equality_path(&receiver, &value, &tuple.tuple_equal, position)?;
            let tuple_term = self.compile_object_reference(&value, position)?;
            let receiver = self.compile_object_reference(&receiver, position)?;
            let argument = self.compile_object_reference(argument, position)?;
            let target = self.compile_object_reference(&goal.set, position)?;
            let members = finite_vector_proof(&members);
            return Ok(format!("(by\n  let _tuple := {tuple_term}\n  let _call := {call}\n  have _same : Litex.Same {receiver} _tuple := {same}\n  have _values : ∀ i : Fin {n}, M.mem (_tuple.val.values i) (Litex.denote {target}) := {members}\n  have _input : M.mem (Litex.denote {argument}) (Litex.FiniteFunction.indexSet (M := M) {n}) := _call.wd.2\n  obtain ⟨i, hi⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := {n}) (Litex.denote {argument})).mp _input\n  change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote {receiver}) (Litex.denote {argument})) (Litex.denote {target})\n  rw [hi, _same, Litex.tuple_coordinate]\n  exact _values i\n)"));
        }
        let index = literal_positive_usize(argument)
            .ok_or_else(|| LeanCompileError::unsupported("TupleMember/LiteralIndex"))?;
        let component = tuple
            .value
            .args
            .get(index - 1)
            .ok_or_else(|| LeanCompileError::unsupported("TupleMember/Bounds"))?;
        let member = match rule {
            InFactSearchProofByKnownSpecialProperty::LiteralTupleNumericCoordinate(p) => {
                if p.index != index {
                    return Err(LeanCompileError::unsupported("TupleMember/Index"));
                }
                self.compile_closed_membership(
                    component,
                    &goal.set,
                    &p.component_membership,
                    position,
                )?
            }
            _ => unreachable!("selected coordinate rule was validated"),
        };
        let value = Obj::ProductShape(ProductShape::Tuple(tuple.value.clone()));
        let same = self.compile_equality_path(&receiver, &value, &tuple.tuple_equal, position)?;
        let tuple_term = self.compile_object_reference(&value, position)?;
        let receiver = self.compile_object_reference(&receiver, position)?;
        let call = self.compile_object_reference(&goal.element, position)?;
        let component = self.compile_object_reference(component, position)?;
        let target = self.compile_object_reference(&goal.set, position)?;
        let i = index - 1;
        Ok(format!("(by\n  let _tuple := {tuple_term}\n  have _same : Litex.Same {receiver} _tuple := {same}\n  have _coordinate : Litex.Same {call} {component} := by\n    change Litex.FunctionSemantics.callValue (M := M) (Litex.denote {receiver}) (M.number ({index} : ℂ)) = Litex.denote {component}\n    have _beta : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number ({index} : ℂ)) = _tuple.val.values ({i} : Fin {n}) := by\n      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple ({i} : Fin {n}))\n    have _entry : _tuple.val.values ({i} : Fin {n}) = Litex.denote {component} := rfl\n    exact (congrArg (fun v => Litex.FunctionSemantics.callValue (M := M) v (M.number ({index} : ℂ))) _same).trans (_beta.trans _entry)\n  exact Litex.inOfSame {component} {call} {target} {target} _coordinate.symm (Litex.sameRefl {target}) {member}\n)"))
    }
}
