use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::ParentCheckedBetaFunctionBody;
use crate::prelude::*;
use std::collections::HashMap;
use super::compile_function_definition::function_head_object;

impl LitexToLeanCompiler {
    /// Replay receiver beta, application congruence, then the recorded call beta.
    pub(super) fn compile_returned_known_beta(
        &self,
        application: &Obj,
        parent_wd: &ObjWellDefinedProof,
        receiver_wd: &ObjWellDefinedProof,
        receiver_body: &ParentCheckedBetaFunctionBody,
        application_wd: &ObjWellDefinedProof,
        application_body: &ParentCheckedBetaFunctionBody,
        expanded: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(call) = application else {
            return Err(LeanCompileError::unsupported(
                "ReturnedKnownBeta/Application",
            ));
        };
        let receiver = if let FnObjHead::FieldAccess(field) = call.head.as_ref() {
            if call.body.len() != 1 {
                return Err(LeanCompileError::unsupported(
                    "ReturnedKnownBeta/FieldArguments",
                ));
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field.clone()))
        } else {
            if call.body.len() < 2 {
                return Err(LeanCompileError::unsupported("ReturnedKnownBeta/Receiver"));
            }
            Obj::FnObj(FnObj {
                head: call.head.clone(),
                body: call.body[..call.body.len() - 1].to_vec(),
            })
        };
        let arguments = call.body.last().unwrap();
        let Obj::FnObj(substituted) = application_wd.obj() else {
            return Err(LeanCompileError::unsupported(
                "ReturnedKnownBeta/SubstitutedCall",
            ));
        };
        if arguments.is_empty() || substituted.body.as_slice() != std::slice::from_ref(arguments) {
            return Err(LeanCompileError::unsupported("ReturnedKnownBeta/Arguments"));
        }
        ensure_object(&receiver, receiver_wd)?;
        let returned = function_head_object(&substituted.head)?;
        let actual = self.compile_wd(parent_wd, position)?;
        // This is the producer's checked intermediate call. Its WD supplies
        // its own constructor subjects; it publishes no fact to later source.
        let intermediate =
            SourcePosition::new(Some(position), SourceOwner::WD(application_wd), usize::MAX);
        let receiver_equal = self.compile_parent_checked_function_body(
            &receiver,
            receiver_wd,
            receiver_body,
            &returned,
            &intermediate,
        )?;
        let application_equal = self.compile_parent_checked_function_body(
            application_wd.obj(),
            application_wd,
            application_body,
            expanded,
            &intermediate,
        )?;
        let values = arguments
            .iter()
            .map(|a| self.compile_normalization_value(a, position))
            .collect::<Result<Vec<_>, _>>()?;
        let packed = if values.len() == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        let input = self.compile_normalization_value(application, position)?;
        let endpoint = self.compile_normalization_value(expanded, &intermediate)?;
        Ok(format!("(show {input} = {endpoint} from by\n\
  let _litex_original := {actual}\n\
  exact (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f {packed}) {receiver_equal}).trans {application_equal}\n)"))
    }

    /// Eliminate the returned graph using the complete call's original WD.
    /// The receiver certificate determines the formula; no new literal WD or
    /// function-body search is needed at the substituted endpoint.
    pub(super) fn compile_returned_anonymous_beta(
        &self,
        application: &Obj,
        parent_wd: &ObjWellDefinedProof,
        receiver_wd: &ObjWellDefinedProof,
        receiver_body: &ParentCheckedBetaFunctionBody,
        function: &AnonymousFn,
        expanded: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(call) = application else {
            return Err(LeanCompileError::unsupported("ReturnedBeta/Application"));
        };
        if call.body.len() < 2 {
            return Err(LeanCompileError::unsupported("ReturnedBeta/Receiver"));
        }
        let arguments = call.body.last().unwrap();
        let parameters = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if parameters.len() != arguments.len() || arguments.is_empty() {
            return Err(LeanCompileError::unsupported("ReturnedBeta/Arguments"));
        }
        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            if substitution
                .insert(parameter.id, argument.as_ref().clone())
                .is_some()
            {
                return Err(LeanCompileError::unsupported(
                    "ReturnedBeta/ParameterIdentity",
                ));
            }
        }
        if !instantiated_object_matches(&function.equal_to, expanded, &substitution) {
            return Err(LeanCompileError::unsupported("ReturnedBeta/Substitution"));
        }
        // This is the recorded source prefix, not a fabricated WD result.
        let receiver = Obj::FnObj(FnObj {
            head: call.head.clone(),
            body: call.body[..call.body.len() - 1].to_vec(),
        });
        ensure_object(&receiver, receiver_wd)?;
        let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
        let receiver_equal = self.compile_parent_checked_function_body(
            &receiver,
            receiver_wd,
            receiver_body,
            &literal,
            position,
        )?;
        let receiver_denotation = self.compile_normalization_denotation(&receiver, position)?;
        let source_denotation = self.compile_normalization_denotation(application, position)?;
        let actual = self.compile_wd(parent_wd, position)?;
        let (domain, output, body) =
            self.compile_function_literal_parts(function, position, &HashMap::new())?;
        let graph =
            format!("(Litex.FunctionSemantics.graphValue (M := M) {domain} {output} {body})");
        let input = self.compile_normalization_value(application, position)?;
        let endpoint = self.compile_normalization_value(expanded, position)?;
        let values = arguments
            .iter()
            .map(|a| self.compile_normalization_value(a, position))
            .collect::<Result<Vec<_>, _>>()?;
        let argument_equal =
            self.compile_normalization_packed_argument_denotation(arguments, position)?;
        let packed = if values.len() == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        let template = self.compile_function_body_template(function, position)?;
        let body_equal = self.compile_function_packed_application_equality(&template, &values)?;
        Ok(format!("(show {input} = {endpoint} from by\n\
  let _litex_original := {actual}\n\
  have _litex_receiver_eq : Litex.denote _litex_original.val.function = {graph} := ({receiver_denotation}).trans {receiver_equal}\n\
  have _litex_argument_eq : Litex.denote _litex_original.val.argument = {packed} := {argument_equal}\n\
  have _litex_point := Litex.FunctionSemantics.call_graph _ _ _ _ ((Litex.FunctionSemantics.fnSet_members _ _ _).mp _litex_original.wd.1) _litex_original.wd.2\n\
  have _litex_beta : Litex.denote _litex_original = {body} (Litex.denote _litex_original.val.argument) := ((Litex.FunctionSemantics.pair_mem_graph {domain} {output} {body} _ _).mp (_litex_receiver_eq ▸ _litex_point)).2.2\n\
  exact (Eq.symm {source_denotation}).trans (_litex_beta.trans ((congrArg {body} _litex_argument_eq).trans (show {body} {packed} = {endpoint} from {body_equal})))\n)"))
    }
}
