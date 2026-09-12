use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{AtomObj, Obj};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::execution_environment::helper::{ast_obj_eq, ast_obj_key};
use crate::new_pipeline::execute::execute_fact_stmt::result::{
    ExecFactStmtResult, StoreFactAndInferResult2,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;
use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

pub struct NativeVerifyEqualResult {
    pub fact: EqualFact,
    pub left_wd: NativeObjWdProof,
    pub right_wd: NativeObjWdProof,
    pub searched_proof: NativeEqualProof,
}

pub enum NativeEqualProof {
    Reflexive,
    ByLetBinding {
        name: String,
        equality_fact_id: crate::new_pipeline::runtime::FactId,
    },
    ByKnownEqual {
        cite_fact_id: crate::new_pipeline::runtime::FactId,
    },
}

pub enum NativeObjWdProof {
    ByReuse(WellDefinednessId),
    ByTrivial,
    ByAdd {
        left: Box<NativeObjWdProof>,
        right: Box<NativeObjWdProof>,
        wd_id: WellDefinednessId,
    },
}

impl Runtime {
    pub(crate) fn exec_native_equal_fact(
        &mut self,
        fact: &EqualFact,
    ) -> RuntimeResult<ExecFactStmtResult> {
        let verify_state = VerifyState2 {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };
        let verify_result = self.verify_native_equal_fact(fact, verify_state)?;
        let store_and_infer_result = self.store_native_equal_fact(&verify_result.fact)?;
        Ok(ExecFactStmtResult {
            verify_result: VerifyFactResult2::NativeEqual(verify_result),
            store_and_infer_result,
        })
    }

    fn verify_native_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<NativeVerifyEqualResult> {
        let left_wd = self.verify_native_obj_wd(&fact.left, verify_state.clone())?;
        let right_wd = self.verify_native_obj_wd(&fact.right, verify_state)?;
        let searched_proof = self.search_native_equal_proof(fact)?;
        Ok(NativeVerifyEqualResult {
            fact: fact.clone(),
            left_wd,
            right_wd,
            searched_proof,
        })
    }

    fn search_native_equal_proof(&self, fact: &EqualFact) -> RuntimeResult<NativeEqualProof> {
        if ast_obj_eq(&fact.left, &fact.right) {
            return Ok(NativeEqualProof::Reflexive);
        }

        if let Some(proof) = self.search_equal_by_let(&fact.left, &fact.right) {
            return Ok(proof);
        }

        if let Some(cite) = self.top_exec_env().find_native_equal(&fact.left, &fact.right) {
            return Ok(NativeEqualProof::ByKnownEqual {
                cite_fact_id: cite,
            });
        }

        Err(RuntimeError::Unknown(
            "search_proof: no equality proof found".to_string(),
        ))
    }

    fn search_equal_by_let(&self, left: &Obj, right: &Obj) -> Option<NativeEqualProof> {
        if let Obj::Atom(AtomObj::Identifier(id)) = left {
            if let Some(binding) = self.top_exec_env().lookup_let_binding(&id.name) {
                if ast_obj_eq(&binding.value, right) {
                    return Some(NativeEqualProof::ByLetBinding {
                        name: id.name.clone(),
                        equality_fact_id: binding.equality_fact_id,
                    });
                }
            }
        }
        if let Obj::Atom(AtomObj::Identifier(id)) = right {
            if let Some(binding) = self.top_exec_env().lookup_let_binding(&id.name) {
                if ast_obj_eq(&binding.value, left) {
                    return Some(NativeEqualProof::ByLetBinding {
                        name: id.name.clone(),
                        equality_fact_id: binding.equality_fact_id,
                    });
                }
            }
        }
        None
    }

    fn store_native_equal_fact(&mut self, fact: &EqualFact) -> RuntimeResult<StoreFactAndInferResult2> {
        self.top_exec_env_mut()
            .store_native_equal_fact(fact.clone());
        Ok(StoreFactAndInferResult2 {
            stored_fact_ids: vec![fact.fact_id],
        })
    }

    // Number and identifier are trivial; Add is WD when both children are WD.
    pub(crate) fn verify_native_obj_wd(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState2,
    ) -> RuntimeResult<NativeObjWdProof> {
        let key = ast_obj_key(obj);
        if let Some(wd_id) = self.top_exec_env().lookup_native_wd(&key) {
            return Ok(NativeObjWdProof::ByReuse(wd_id));
        }

        let proof = match obj {
            Obj::Number(_) | Obj::Atom(AtomObj::Identifier(_)) => NativeObjWdProof::ByTrivial,
            Obj::Add(add) => {
                let left = self.verify_native_obj_wd(add.left.as_ref(), verify_state.clone())?;
                let right = self.verify_native_obj_wd(add.right.as_ref(), verify_state.clone())?;
                let wd_id = self.ids.allocate_well_definedness_id();
                NativeObjWdProof::ByAdd {
                    left: Box::new(left),
                    right: Box::new(right),
                    wd_id,
                }
            }
            _ => {
                return Err(RuntimeError::Unknown(
                    "object well-definedness for this Obj variant is not wired yet".to_string(),
                ));
            }
        };

        if verify_state.store_well_defined_fact {
            let wd_id = match &proof {
                NativeObjWdProof::ByReuse(id) => *id,
                NativeObjWdProof::ByTrivial => self.ids.allocate_well_definedness_id(),
                NativeObjWdProof::ByAdd { wd_id, .. } => *wd_id,
            };
            // For trivial, allocate once and record.
            if matches!(proof, NativeObjWdProof::ByTrivial) {
                self.top_exec_env_mut().record_native_wd(key, wd_id);
                return Ok(NativeObjWdProof::ByReuse(wd_id));
            }
            self.top_exec_env_mut().record_native_wd(key, wd_id);
        }

        Ok(proof)
    }
}

pub fn equal_fact_from_let(
    fact_id: crate::new_pipeline::runtime::FactId,
    name: String,
    value: Obj,
    line_file: LineFile,
) -> EqualFact {
    EqualFact {
        fact_id,
        left: Obj::Atom(AtomObj::Identifier(
            crate::new_pipeline::ast::obj::Identifier { name },
        )),
        right: value,
        line_file,
    }
}
