use crate::prelude::*;

impl Runtime {
    pub fn store_def_prop(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), RuntimeError> {
        let name = def_prop_stmt.name.clone();
        self.top_level_env()
            .defined_def_props
            .insert(name, def_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_abstract_prop(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_abstract_prop_stmt.name.clone();
        self.top_level_env()
            .defined_abstract_props
            .insert(name, def_abstract_prop_stmt.clone());
        Ok(())
    }

    pub fn store_def_algo(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<(), RuntimeError> {
        let name = def_algo_stmt.name.clone();
        self.top_level_env()
            .defined_algorithms
            .insert(name, def_algo_stmt.clone());
        Ok(())
    }

    pub fn store_free_param_or_identifier_name(
        &mut self,
        name: &str,
        kind: ParamObjType,
    ) -> Result<(), RuntimeError> {
        let env = self.top_level_env();
        if let Some(existing_kind) = env.defined_identifiers.get(name) {
            return Err(NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "identifier `{}` is already bound in this scope as {:?} (cannot re-bind as {:?})",
                    name, existing_kind, kind
                )))
            .into());
        }
        env.defined_identifiers.insert(name.to_string(), kind);
        Ok(())
    }

    pub fn store_def_family(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_family_stmt.name.clone();
        self.top_level_env()
            .defined_families
            .insert(name, def_family_stmt.clone());
        Ok(())
    }
}
