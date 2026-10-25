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
        let signature = &function.body;
        let mut bindings = outer.clone();
        let mut parameters = Vec::new();
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
            parameters.push(format!("({name} : M.Value)"));
        }

        // A fixed carrier can use the original checked object. A carrier that
        // itself depends on a raw binder needs its own dependent WD adapter.
        for carrier in signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.param_type.as_ref())
            .chain([signature.ret_set.as_ref()])
        {
            let mut free = HashSet::new();
            crate::instantiate::collect_free_plain_ids(carrier, &HashSet::new(), &mut free);
            if free.iter().any(|id| bindings.contains_key(id)) {
                return Err(LeanCompileError::unsupported(
                    "Function/CapturedSignatureCarrier",
                ));
            }
        }
        let (domain, _) = self.compile_function_semantic_base_domain(signature, position)?;
        let output =
            self.compile_function_raw_expression_bound(&signature.ret_set, position, outer)?;
        let guard = self.compile_function_guard_template_bound(signature, position, &bindings)?;
        let body =
            self.compile_function_raw_expression_bound(&function.equal_to, position, &bindings)?;
        let values = self
            .compile_function_packed_values(signature, "_captured_input")?
            .join(" ");
        let body = format!("(fun {} => {body})", parameters.join(" "));
        Ok(format!(
            "(Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) {domain} (fun (_captured_input : M.Value) => {guard} {values})) {output} (fun (_captured_input : M.Value) => {body} {values}))"
        ))
    }
}
