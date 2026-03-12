use crate::obj::{
    Add, Cap, Cart, CartDim, Choose, ClosedRange, Count, Cup, Dim, Div, FieldAccess, FieldAccessWithMod, 
    FnObj, FnSetWithDom, FnSetWithoutDom, Identifier, IdentifierWithMod, InstStructObj, ListSet, Mod,
    Mul, Number, Obj, ObjAtIndex, PowerSet, Pow, Proj, RObj, Range, SetBuilder, SetDiff, SetMinus, Sub, Tuple, Union, Val, ZObj,
    Intersect,
};
use crate::error::{WellDefinedError, StmtError};
use crate::verify::VerifyState;
use crate::fact::{AtomicFact, NotEqualFact, IsCartFact, IsNonemptySetFact};
use crate::fact::InFact;
use crate::execute::Executor;
use crate::stmt::parameter_type_and_property::{ParamDefWithParamSet, facts_for_args_satisfy_param_def_with_type};

// well-defined check for obj
impl<'a> Executor<'a> {
    pub fn verify_obj_well_defined(&mut self, obj: &Obj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        match obj {
            Obj::Identifier(identifier) => self.verify_identifier_well_defined(identifier),
            Obj::IdentifierWithMod(x) => self.verify_identifier_with_mod_well_defined(x),
            Obj::FieldAccess(x) => self.verify_field_access_well_defined(x),
            Obj::FieldAccessWithMod(x) => self.verify_field_access_with_mod_well_defined(x),
            Obj::FnObj(fn_obj) => self.verify_fn_obj_well_defined(fn_obj, verify_state),
            Obj::Number(_) => Ok(()),
            Obj::Add(add) => self.verify_add_well_defined(add, verify_state),
            Obj::Sub(sub) => self.verify_sub_well_defined(sub, verify_state),
            Obj::Mul(mul) => self.verify_mul_well_defined(mul, verify_state),
            Obj::Div(div) => self.verify_div_well_defined(div, verify_state),
            Obj::Mod(m) => self.verify_mod_well_defined(m, verify_state),
            Obj::Pow(pow) => self.verify_pow_well_defined(pow, verify_state),
            Obj::Union(x) => self.verify_union_well_defined(x, verify_state),
            Obj::Intersect(x) => self.verify_intersect_well_defined(x, verify_state),
            Obj::SetMinus(x) => self.verify_set_minus_well_defined(x, verify_state),
            Obj::SetDiff(x) => self.verify_set_diff_well_defined(x, verify_state),
            Obj::Cup(x) => self.verify_cup_well_defined(x, verify_state),
            Obj::Cap(x) => self.verify_cap_well_defined(x, verify_state),
            Obj::ListSet(x) => self.verify_list_set_well_defined(x, verify_state),
            Obj::SetBuilder(x) => self.verify_set_builder_well_defined(x, verify_state),
            Obj::FnSetWithoutDom(x) => self.verify_fn_set_without_dom_well_defined(x, verify_state),
            Obj::FnSetWithDom(x) => self.verify_fn_set_with_dom_well_defined(x, verify_state),
            Obj::NPosObj(_) => self.verify_n_pos_obj_well_defined(),
            Obj::NObj(_) => self.verify_n_obj_well_defined(),
            Obj::QObj(_) => self.verify_q_obj_well_defined(),
            Obj::ZObj(_) => self.verify_z_obj_well_defined(),
            Obj::RObj(_) => self.verify_r_obj_well_defined(),
            Obj::InstSetStructObj(x) => self.verify_inst_set_struct_obj_well_defined(x, verify_state),
            Obj::Cart(x) => self.verify_cart_well_defined(x, verify_state),
            Obj::CartDim(x) => self.verify_cart_dim_well_defined(x, verify_state),
            Obj::Proj(x) => self.verify_proj_well_defined(x, verify_state),
            Obj::Dim(x) => self.verify_dim_well_defined(x, verify_state),
            Obj::Tuple(x) => self.verify_tuple_well_defined(x, verify_state),
            Obj::Count(x) => self.verify_count_well_defined(x, verify_state),
            Obj::Range(x) => self.verify_range_well_defined(x, verify_state),
            Obj::ClosedRange(x) => self.verify_closed_range_well_defined(x, verify_state),
            Obj::Val(x) => self.verify_val_well_defined(x, verify_state),
            Obj::PowerSet(x) => self.verify_power_set_well_defined(x, verify_state),
            Obj::Choose(x) => self.verify_choose_well_defined(x, verify_state),
            Obj::ObjAtIndex(x) => self.verify_obj_at_index_well_defined(x, verify_state),
            Obj::QPos(_) => self.verify_q_pos_well_defined(),
            Obj::ZPos(_) => self.verify_z_pos_well_defined(),
            Obj::RPos(_) => self.verify_r_pos_well_defined(),
            Obj::QNeg(_) => self.verify_q_neg_well_defined(),
            Obj::ZNeg(_) => self.verify_z_neg_well_defined(),
            Obj::RNeg(_) => self.verify_r_neg_well_defined(),
            Obj::QNz(_) => self.verify_q_nz_well_defined(),
            Obj::ZNz(_) => self.verify_z_nz_well_defined(),
            Obj::RNz(_) => self.verify_r_nz_well_defined(),
        }
    }

    fn verify_identifier_well_defined(&self, identifier: &Identifier) -> Result<(), WellDefinedError> {
        if self.runtime_context.is_defined_identifier_obj(identifier) {
            Ok(())
        } else {
            Err(WellDefinedError::new("identifier not defined", vec![], None))
        }
    }

    fn verify_identifier_with_mod_well_defined(&self, x: &IdentifierWithMod) -> Result<(), WellDefinedError> {
        let _ = x;
        Err(WellDefinedError::new("verify_identifier_with_mod_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_field_access_well_defined(&self, x: &FieldAccess) -> Result<(), WellDefinedError> {
        let _ = x;
        Err(WellDefinedError::new("verify_field_access_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_field_access_with_mod_well_defined(&self, x: &FieldAccessWithMod) -> Result<(), WellDefinedError> {
        let _ = x;
        Err(WellDefinedError::new("verify_field_access_with_mod_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_fn_obj_well_defined(&self, _fn_obj: &FnObj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = verify_state;
        Err(WellDefinedError::new("verify_fn_obj_well_defined 此函数还没有 implement", vec![], None))
    }

    fn require_obj_in_r(&self, obj: &Obj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let r_obj = Obj::RObj(RObj::new());
        let in_fact = InFact::new(obj.clone(), r_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_atomic_fact(&atomic_fact, verify_state)?;
        Ok(())
    }

    fn require_obj_in_z(&self, obj: &Obj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let z_obj = Obj::ZObj(ZObj::new());
        let in_fact = InFact::new(obj.clone(), z_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_atomic_fact(&atomic_fact, verify_state)?;
        Ok(())
    }

    fn verify_add_well_defined(&mut self, add: &Add, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&add.left, verify_state)?;
        self.verify_obj_well_defined(&add.right, verify_state)?;
        self.require_obj_in_r(&add.left, verify_state)?;
        self.require_obj_in_r(&add.right, verify_state)?;
        Ok(())
    }

    fn verify_sub_well_defined(&mut self, sub: &Sub, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&sub.left, verify_state)?;
        self.verify_obj_well_defined(&sub.right, verify_state)?;
        self.require_obj_in_r(&sub.left, verify_state)?;
        self.require_obj_in_r(&sub.right, verify_state)?;
        Ok(())
    }

    fn verify_mul_well_defined(&mut self, mul: &Mul, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&mul.left, verify_state)?;
        self.verify_obj_well_defined(&mul.right, verify_state)?;
        self.require_obj_in_r(&mul.left, verify_state)?;
        self.require_obj_in_r(&mul.right, verify_state)?;
        Ok(())
    }

    fn verify_div_well_defined(&mut self, div: &Div, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&div.left, verify_state)?;
        self.verify_obj_well_defined(&div.right, verify_state)?;

        let zero = Obj::Number(Number::new("0"));
        let not_equal_fact = NotEqualFact::new((*div.right).clone(), zero, None);
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        self.verify_atomic_fact(&atomic_fact, verify_state)?;
        
        self.require_obj_in_r(&div.left, verify_state)?;
        self.require_obj_in_r(&div.right, verify_state)?;
        Ok(())
    }

    fn verify_mod_well_defined(&mut self, m: &Mod, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&m.left, verify_state)?;
        self.verify_obj_well_defined(&m.right, verify_state)?;
        self.require_obj_in_z(&m.left, verify_state)?;
        self.require_obj_in_z(&m.right, verify_state)?;
        let zero = Obj::Number(Number::new("0"));
        let not_equal_fact = NotEqualFact::new((*m.right).clone(), zero, None);
        self.verify_atomic_fact(&AtomicFact::NotEqualFact(not_equal_fact), verify_state)?;
        Ok(())
    }

    fn verify_pow_well_defined(&self, _pow: &Pow, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = verify_state;
        Err(WellDefinedError::new("verify_pow_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_union_well_defined(&mut self, x: &Union, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_intersect_well_defined(&mut self, x: &Intersect, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())

    }

    fn verify_set_minus_well_defined(&mut self, x: &SetMinus, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_diff_well_defined(&mut self, x: &SetDiff, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_cup_well_defined(&mut self, x: &Cup, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_cap_well_defined(&mut self, x: &Cap, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_list_set_well_defined(&mut self, x: &ListSet, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.list {
            self.verify_obj_well_defined(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_set_builder_well_defined(&mut self, x: &SetBuilder, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.runtime_context.new_env();
        let result = self.verify_set_builder_well_defined_body(x, verify_state);
        self.runtime_context.delete_env();
        result
    }

    fn verify_set_builder_well_defined_body(&mut self, x: &SetBuilder, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        if let Err(e) = self.define_params_with_set(&ParamDefWithParamSet::new(vec![x.param.clone()], *x.param_set.clone())) {
            return Err(WellDefinedError::new(format!("failed to verify well-defined of set builder {}", x.to_string()).as_str(), vec![StmtError::ExecError(e)], None));
        }

        for fact in x.facts.iter() {
            if let Err(e) = self.verify_fact_well_defined_and_store(&(fact.from_ref_to_cloned_fact()), verify_state) {
                return Err(WellDefinedError::new(format!("failed to verify well-defined of set builder {}", x.to_string()).as_str(), vec![StmtError::ExecError(e)], None));
            }
        }

        Ok(())
    }


    fn verify_fn_set_without_dom_well_defined(&mut self, x: &FnSetWithoutDom, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.param_sets {
            self.verify_obj_well_defined(obj, verify_state)?;
        }
        self.verify_obj_well_defined(&x.ret_set, verify_state)?;
        Ok(())
    }

    fn verify_fn_set_with_dom_well_defined(&mut self, x: &FnSetWithDom, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.runtime_context.new_env();
        let result = self.verify_fn_set_with_dom_well_defined_body(x, verify_state);
        self.runtime_context.delete_env();
        result
    }

    fn verify_fn_set_with_dom_well_defined_body(&mut self, x: &FnSetWithDom, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        if let Err(e) = self.verify_obj_well_defined(&x.ret_set, verify_state) {
            return Err(WellDefinedError::new(format!("failed to verify well-defined of fn set with dom {}", x.to_string()).as_str(), vec![StmtError::WellDefinedError(e)], None));
        }
        
        
        for param_def_with_set in x.params_def_with_set.iter() {
            if let Err(e) = self.define_params_with_set(param_def_with_set) {
                return Err(WellDefinedError::new(format!("failed to verify well-defined of fn set with dom {}", x.to_string()).as_str(), vec![StmtError::ExecError(e)], None));
            }
        }

        for fact in x.dom_facts.iter() {
            if let Err(e) = self.verify_fact_well_defined_and_store(&(fact.from_ref_to_cloned_fact()), verify_state) {
                return Err(WellDefinedError::new(format!("failed to verify well-defined of fn set with dom {}", x.to_string()).as_str(), vec![StmtError::ExecError(e)], None));
            }
        }

        Ok(())
    }

    fn verify_n_pos_obj_well_defined(&mut self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_n_obj_well_defined(&mut self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_obj_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_obj_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_obj_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_inst_set_struct_obj_well_defined(&mut self, x: &InstStructObj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.runtime_context.new_env();
        let result = self.verify_inst_set_struct_obj_well_defined_body(x, verify_state);
        self.runtime_context.delete_env();
        result
    }

    fn verify_inst_set_struct_obj_well_defined_body(&mut self, x: &InstStructObj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let def = self.runtime_context.get_set_struct_definition_by_name(x.struct_name.to_string().as_str()).ok_or(WellDefinedError::new(format!("set struct definition not found {}", x.struct_name.to_string()).as_str(), vec![], None))?;

        let param_defs = def.get_params_def_with_type();
        let facts = facts_for_args_satisfy_param_def_with_type(param_defs, &x.args)
            .map_err(|e| WellDefinedError::new(format!("failed to build facts for inst struct {}: {}", x.struct_name, e).as_str(), vec![e], None))?;
        for fact in facts.iter() {
            self.exec_fact(fact, verify_state).map_err(|e| WellDefinedError::new(
                &format!("exec_fact failed for inst struct obj arg (struct {})", x.struct_name),
                vec![e],
                None,
            ))?;
        }

        Ok(())
    }

    fn verify_cart_well_defined(&mut self, x: &Cart, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.args {
            self.verify_obj_well_defined(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_cart_dim_well_defined(&mut self, x: &CartDim, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.set, verify_state)?;

        let is_cart_fact = AtomicFact::IsCartFact(IsCartFact::new((*x.set).clone(), None));
        self.verify_atomic_fact(&is_cart_fact, verify_state)?;
        
        Ok(())
    }

    fn verify_proj_well_defined(&mut self, x: &Proj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_proj_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_dim_well_defined(&mut self, x: &Dim, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_dim_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_tuple_well_defined(&mut self, x: &Tuple, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_tuple_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_count_well_defined(&mut self, x: &Count, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_count_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_range_well_defined(&mut self, x: &Range, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_range_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_closed_range_well_defined(&mut self, x: &ClosedRange, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_closed_range_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_val_well_defined(&mut self, x: &Val, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_val_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_power_set_well_defined(&mut self, x: &PowerSet, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.set, verify_state)?;
        Ok(())
    }

    fn verify_choose_well_defined(&mut self, x: &Choose, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.set, verify_state)?;
        let is_nonempty_set_fact = AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new((*x.set).clone(), None));
        self.verify_atomic_fact(&is_nonempty_set_fact, verify_state)?;
        Ok(())
    }

    fn verify_obj_at_index_well_defined(&self, x: &ObjAtIndex, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_obj_at_index_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_q_pos_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_pos_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_pos_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_neg_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_neg_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_neg_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_nz_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_nz_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_nz_well_defined(&self) -> Result<(), WellDefinedError> {
        Ok(())
    }
}
