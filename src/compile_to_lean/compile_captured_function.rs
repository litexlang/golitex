use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    /// Interpret a nested literal under the source's lexical parameter IDs.
    /// This is only its graph value: construction and beta consumers retain
    /// the original literal/call WD and checked return-membership proof.
    pub(super) fn compile_function_literal_value(
        &self,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
        outer: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let (domain, output, body) =
            self.compile_function_literal_parts(function, position, outer)?;
        Ok(format!(
            "(Litex.FunctionSemantics.graphValue (M := M) {domain} {output} {body})"
        ))
    }

    pub(super) fn compile_function_literal_parts(
        &self,
        function: &AnonymousFn,
        position: &SourcePosition<'_>,
        outer: &HashMap<IdentifierId, String>,
    ) -> Result<(String, String, String), LeanCompileError> {
        let signature = &function.body;
        let (domain, output, bindings) =
            self.compile_function_signature_value_parts(signature, position, outer)?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .map(|parameter| format!("(_raw_i{} : M.Value)", parameter.id.value()))
            .collect::<Vec<_>>();
        let body =
            self.compile_function_raw_expression_bound(&function.equal_to, position, &bindings)?;
        let values = self
            .compile_function_packed_values(signature, "_captured_input")?
            .join(" ");
        let body = format!("(fun {} => {body})", parameters.join(" "));
        Ok((
            domain,
            output,
            format!("(fun (_captured_input : M.Value) => {body} {values})"),
        ))
    }

    /// The raw function-space denotation is shared with literal construction.
    /// It carries no new WD evidence; callers must replay the source WD separately.
    pub(super) fn compile_function_signature_value_parts(
        &self,
        signature: &FnSet,
        position: &SourcePosition<'_>,
        outer: &HashMap<IdentifierId, String>,
    ) -> Result<(String, String, HashMap<IdentifierId, String>), LeanCompileError> {
        let mut bindings = outer.clone();
        for parameter in signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
        {
            let name = format!("_raw_i{}", parameter.id.value());
            if bindings.insert(parameter.id, name.clone()).is_some() {
                return Err(LeanCompileError::unsupported(
                    "Function/CaptureBinderIdentity",
                ));
            }
        }

        // Input carriers are raw denotations under the outer lexical bindings.
        // Dependence on this literal's own parameters still needs a dependent
        // product adapter. A captured output carrier is fixed for this literal;
        // only dependence on the literal's own inputs needs a dependent codomain.
        let local_ids = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect::<HashSet<_>>();
        for carrier in signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.param_type.as_ref())
        {
            let mut free = HashSet::new();
            crate::instantiate::collect_free_plain_ids(carrier, &HashSet::new(), &mut free);
            if free.iter().any(|id| local_ids.contains(id)) {
                return Err(LeanCompileError::unsupported(
                    "Function/CapturedSignatureCarrier",
                ));
            }
        }
        let mut output_free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(
            &signature.ret_set,
            &HashSet::new(),
            &mut output_free,
        );
        if output_free.iter().any(|id| local_ids.contains(id)) {
            return Err(LeanCompileError::unsupported(
                "Function/CapturedSignatureCarrier",
            ));
        }
        let domain = if Self::function_uses_numeric_interface(signature) {
            self.compile_function_semantic_base_domain(signature, position)?
                .0
        } else {
            let values = signature
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
                .map(|carrier| self.compile_function_raw_expression_bound(carrier, position, outer))
                .collect::<Result<Vec<_>, _>>()?;
            match values.as_slice() {
                [value] => value.clone(),
                [] => return Err(LeanCompileError::unsupported("Function/Arity")),
                _ => format!(
                    "(Litex.FiniteFunction.cartValue (M := M) ![{}])",
                    values.join(", ")
                ),
            }
        };
        let output =
            self.compile_function_raw_expression_bound(&signature.ret_set, position, outer)?;
        let guard = self.compile_function_guard_template_bound(signature, position, &bindings)?;
        let values = self
            .compile_function_packed_values(signature, "_captured_input")?
            .join(" ");
        Ok((
            format!("(Litex.SetSemantics.sepValue (M := M) {domain} (fun (_captured_input : M.Value) => {guard} {values}))"),
            output,
            bindings,
        ))
    }
}
