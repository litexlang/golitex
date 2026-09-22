use std::collections::HashMap;

use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

use crate::new_pipeline::ast::obj::{InstantiatedTemplateObj, IntervalObj, IntervalObjStruct, Obj, FieldAccess, OneSideInfinityIntervalObj, OneSideInfinityIntervalObjStruct, StructObj, SetFormer};
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_struct_obj(
        &mut self,
        s: &StructObj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<StructObj, InstError> {
        let mut params = Vec::with_capacity(s.params.len());
        for o in &s.params {
            params.push(self.inst_obj_rec(o, param_to_arg_map)?);
        }
        Ok(StructObj {
            name: s.name.clone(),
            params,
        })
    }

    pub(crate) fn inst_field_access(
        &mut self,
        a: &FieldAccess,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<FieldAccess, InstError> {
        Ok(FieldAccess {
            obj: Box::new(self.inst_obj_rec(&a.obj, param_to_arg_map)?),
            fields: a.fields.clone(),
        })
    }

    pub(crate) fn inst_instantiated_template(
        &mut self,
        a: &InstantiatedTemplateObj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<InstantiatedTemplateObj, InstError> {
        let mut args = Vec::with_capacity(a.args.len());
        for o in &a.args {
            args.push(self.inst_obj_rec(o, param_to_arg_map)?);
        }
        Ok(InstantiatedTemplateObj {
            template_name: a.template_name.clone(),
            args,
        })
    }

    pub(crate) fn inst_one_side_infinity_interval(
        &mut self,
        i: &OneSideInfinityIntervalObj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        let mut inst_struct = |s: &OneSideInfinityIntervalObjStruct| {
            Ok(OneSideInfinityIntervalObjStruct {
                start: Box::new(self.inst_obj_rec(&s.start, param_to_arg_map)?),
            })
        };
        Ok(match i {
            OneSideInfinityIntervalObj::LeftOpen(s) => {
                Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(OneSideInfinityIntervalObj::LeftOpen(inst_struct(s)?)))
            }
            OneSideInfinityIntervalObj::LeftClosed(s) => Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(
                OneSideInfinityIntervalObj::LeftClosed(inst_struct(s)?),
            )),
            OneSideInfinityIntervalObj::RightOpen(s) => {
                Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(OneSideInfinityIntervalObj::RightOpen(inst_struct(s)?)))
            }
            OneSideInfinityIntervalObj::RightClosed(s) => Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(
                OneSideInfinityIntervalObj::RightClosed(inst_struct(s)?),
            )),
        })
    }

    pub(crate) fn inst_interval(
        &mut self,
        i: &IntervalObj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
        let mut inst_struct = |s: &IntervalObjStruct| {
            Ok(IntervalObjStruct {
                start: Box::new(self.inst_obj_rec(&s.start, param_to_arg_map)?),
                end: Box::new(self.inst_obj_rec(&s.end, param_to_arg_map)?),
            })
        };
        Ok(match i {
            IntervalObj::LeftOpenRightOpen(s) => {
                Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(inst_struct(s)?)))
            }
            IntervalObj::LeftOpenRightClosed(s) => {
                Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightClosed(inst_struct(s)?)))
            }
            IntervalObj::LeftClosedRightOpen(s) => {
                Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftClosedRightOpen(inst_struct(s)?)))
            }
            IntervalObj::LeftClosedRightClosed(s) => {
                Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftClosedRightClosed(inst_struct(s)?)))
            }
        })
    }
}
