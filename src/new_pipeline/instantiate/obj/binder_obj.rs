use std::collections::HashMap;

use crate::new_pipeline::ast::obj::{AnonymousFn, FnObj, FnObjHead, FnSet, Obj, SetBuilder};
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_fn_obj_head(
        &mut self,
        head: &FnObjHead,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<FnObjHead, InstError> {
        match head {
            FnObjHead::Identifier(id) => Ok(FnObjHead::Identifier(id.clone())),
            FnObjHead::AnonymousFnLiteral(af) => Ok(FnObjHead::AnonymousFnLiteral(Box::new(
                self.inst_anonymous_fn(af, param_to_arg_map, fresh, binder_renames)?,
            ))),
            FnObjHead::FiniteSeqListObj(a) => Ok(FnObjHead::FiniteSeqListObj(
                self.inst_finite_seq_list_obj(a, param_to_arg_map, fresh, binder_renames)?
                    .expect_finite_seq_list(),
            )),
            FnObjHead::ObjAtIndex(a) => Ok(FnObjHead::ObjAtIndex(
                self.inst_obj_at_index_obj(a, param_to_arg_map, fresh, binder_renames)?
                    .expect_obj_at_index(),
            )),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(a) => Ok(
                FnObjHead::ObjAsStructInstanceWithFieldAccess(
                    self.inst_obj_as_struct(a, param_to_arg_map, fresh, binder_renames)?,
                ),
            ),
            FnObjHead::InstantiatedTemplateObj(a) => Ok(FnObjHead::InstantiatedTemplateObj(
                self.inst_instantiated_template(a, param_to_arg_map, fresh, binder_renames)?,
            )),
        }
    }

    pub(crate) fn inst_fn_obj(
        &mut self,
        f: &FnObj,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        let head = self.inst_fn_obj_head(f.head.as_ref(), param_to_arg_map, fresh, binder_renames)?;
        let mut body = Vec::with_capacity(f.body.len());
        for group in &f.body {
            let mut new_group = Vec::with_capacity(group.len());
            for o in group {
                new_group.push(Box::new(
                    self.inst_obj_rec(o, param_to_arg_map, fresh, binder_renames)?,
                ));
            }
            body.push(new_group);
        }
        Ok(Obj::FnObj(FnObj {
            head: Box::new(head),
            body,
        }))
    }

    pub(crate) fn inst_set_builder_obj(
        &mut self,
        sb: &SetBuilder,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::SetBuilder(
            self.inst_set_builder(sb, param_to_arg_map, fresh, binder_renames)?,
        ))
    }

    pub(crate) fn inst_fn_set_obj(
        &mut self,
        fs: &FnSet,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::FnSet(
            self.inst_fn_set(fs, param_to_arg_map, fresh, binder_renames)?,
        ))
    }

    pub(crate) fn inst_anonymous_fn_obj(
        &mut self,
        af: &AnonymousFn,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        Ok(Obj::AnonymousFn(
            self.inst_anonymous_fn(af, param_to_arg_map, fresh, binder_renames)?,
        ))
    }
}

trait ObjExpect {
    fn expect_finite_seq_list(self) -> crate::new_pipeline::ast::obj::FiniteSeqListObj;
    fn expect_obj_at_index(self) -> crate::new_pipeline::ast::obj::ObjAtIndex;
}

impl ObjExpect for Obj {
    fn expect_finite_seq_list(self) -> crate::new_pipeline::ast::obj::FiniteSeqListObj {
        match self {
            Obj::FiniteSeqListObj(a) => a,
            _ => panic!("expected FiniteSeqListObj"),
        }
    }

    fn expect_obj_at_index(self) -> crate::new_pipeline::ast::obj::ObjAtIndex {
        match self {
            Obj::ObjAtIndex(a) => a,
            _ => panic!("expected ObjAtIndex"),
        }
    }
}
