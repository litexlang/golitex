use super::compile_struct_projection::field_receiver;
use super::helper::ensure_object;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_struct_field_value(
        &self,
        object: &Obj,
        wd: &ObjWellDefinedProof,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::struct_field_value::StructFieldValueProof,
        expanded: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::struct_field_value::StructTupleValueSource;
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) = object
        else {
            return Err(LeanCompileError::unsupported("StructField/BetaSubject"));
        };
        let Some(field) = access.fields.last() else {
            return Err(LeanCompileError::unsupported("StructField/EmptyPath"));
        };
        let receiver = field_receiver(access, access.fields.len() - 1);
        ensure_object(object, wd)?;
        ensure_object(&receiver, &proof.receiver_well_defined)?;
        let checked = self.compile_wd(wd, position)?;
        let checked_scope = SourcePosition::new(Some(position), SourceOwner::ObjectLocal(wd), 0);
        let checked_name = checked_scope.object_local_name();
        let receiver_checked = self.compile_wd(&proof.receiver_well_defined, &checked_scope)?;
        let receiver_scope = SourcePosition::new(
            Some(&checked_scope),
            SourceOwner::ObjectLocal(&proof.receiver_well_defined),
            0,
        );
        let receiver_name = receiver_scope.object_local_name();
        let position = &receiver_scope;
        let carrier = if access.fields.len() > 1 {
            let mut select = |projection: &crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FieldAccessObjWellDefinedProof, scope: &SourcePosition<'_>| {
                self.validate_struct_projection(access, projection, scope)?;
                Ok(projection.projection_steps.last().unwrap().carrier.clone())
            };
            if let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                        projection,
                    )),
                ..
            } = wd.detailed_ref()
            {
                let formed = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
                select(projection, &formed)?
            } else {
                self.with_struct_field_evidence(access, position, &mut select)?
            }
        } else if let Obj::InstantiatedTemplateObj(instance) = &receiver {
            self.compile_template_record_member(instance, &proof.carrier, position)?;
            proof.carrier.clone()
        } else {
            self.compile_struct_receiver(&receiver, position)?.0
        };
        let (declaration, _, _) = position.visible_struct(&carrier.name, &self.runtime)?;
        let index = declaration
            .statement
            .fields
            .iter()
            .position(|f| &f.binding.name == field)
            .ok_or_else(|| LeanCompileError::unsupported("StructField/Name"))?;
        let n = declaration.statement.fields.len();
        if carrier != proof.carrier || proof.index != index + 1 {
            return Err(LeanCompileError::unsupported("StructField/BetaDeclaration"));
        }
        let value = match &proof.source {
            StructTupleValueSource::Known(source) => &source.value,
            StructTupleValueSource::Function(source) => &source.value,
            StructTupleValueSource::Template { value, .. } => value,
            StructTupleValueSource::Returned { value, .. } => value,
            StructTupleValueSource::ReturnedFunction { function, .. } => &function.value,
        };
        if value.args.len() != n || value.args[index].ir() != expanded.ir() {
            return Err(LeanCompileError::unsupported("StructField/BetaCoordinate"));
        }
        let tuple = Obj::ProductShape(ProductShape::Tuple(value.clone()));
        let equality = match &proof.source {
            StructTupleValueSource::Known(source) => {
                self.compile_equality_path(&receiver, &tuple, &source.tuple_equal, position)?
            }
            StructTupleValueSource::Function(source) => {
                self.compile_known_tuple_beta(&receiver, &receiver, source, &tuple, position)?
            }
            StructTupleValueSource::Template { instance, .. } => {
                if receiver != Obj::InstantiatedTemplateObj(instance.clone()) {
                    return Err(LeanCompileError::unsupported("StructField/TemplateSubject"));
                }
                self.compile_template_record_value(instance, &tuple, position)?
            }
            StructTupleValueSource::Returned { body, .. } => self
                .compile_parent_checked_function_body(
                    &receiver,
                    &proof.receiver_well_defined,
                    body,
                    &tuple,
                    position,
                )?,
            StructTupleValueSource::ReturnedFunction {
                body,
                application_well_defined,
                function,
            } => {
                let application = application_well_defined.obj();
                let intermediate = SourcePosition::new(
                    Some(position),
                    SourceOwner::WD(application_well_defined),
                    usize::MAX,
                );
                let returned = self.compile_parent_checked_function_body(
                    &receiver,
                    &proof.receiver_well_defined,
                    body,
                    application,
                    &intermediate,
                )?;
                let called = self.compile_checked_tuple_beta(
                    application,
                    application,
                    function,
                    &tuple,
                    application_well_defined,
                    position,
                    &intermediate,
                )?;
                format!("({returned}.trans {called})")
            }
        };
        let coordinates = value
            .args
            .iter()
            .map(|x| self.compile_normalization_value(x, position))
            .collect::<Result<Vec<_>, _>>()?
            .join(", ");
        let input = self.compile_normalization_value(object, position)?;
        let endpoint = self.compile_normalization_value(expanded, position)?;
        let coordinate = index + 1;
        Ok(format!("(let {checked_name} := {checked};\nlet {receiver_name} := {receiver_checked};\nshow {input} = {endpoint} from by\n  let _field_values : Fin {n} → M.Value := ![{coordinates}]\n  have _field_receiver := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number ({coordinate} : ℂ))) {equality}\n  have _field_value : Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue _field_values) (M.number ({coordinate} : ℂ)) = _field_values ({index} : Fin {n}) := by\n    simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.call_tuple _field_values ({index} : Fin {n}))\n  exact _field_receiver.trans _field_value\n)"))
    }
}
