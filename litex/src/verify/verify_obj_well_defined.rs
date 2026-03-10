use crate::obj::{
    Add, Cap, Cart, CartDim, Choose, ClosedRange, Count, Cup, Dim, Div, FieldAccess, FieldAccessWithMod,
    FnObj, FnSetWithDom, FnSetWithoutDom, Identifier, IdentifierWithMod, InstStructObj, ListSet, Mod,
    Mul, NObj, NPosObj, Number, Obj, ObjAtIndex, PowerSet, Pow, Proj, QNeg, QNz, QObj, QPos, RObj, RNeg, RNz,
    RPos, Range, SetBuilder, SetDiff, SetMinus, Sub, Tuple, Union, Val, ZNeg, ZNz, ZObj, ZPos,
    Intersect,
};
use crate::error::WellDefinedError;
use crate::verify::VerifyState;
use crate::fact::{AtomicFact, NotEqualFact};
use crate::fact::InFact;
use crate::execute::Executor;

// well-defined check for obj
impl<'a> Executor<'a> {
    pub fn verify_obj_well_defined(&self, obj: &Obj, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        match obj {
            Obj::Identifier(identifier) => self.verify_identifier_well_defined(identifier, verify_state),
            Obj::IdentifierWithMod(x) => self.verify_identifier_with_mod_well_defined(x, verify_state),
            Obj::FieldAccess(x) => self.verify_field_access_well_defined(x, verify_state),
            Obj::FieldAccessWithMod(x) => self.verify_field_access_with_mod_well_defined(x, verify_state),
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
            Obj::NPosObj(x) => self.verify_n_pos_obj_well_defined(x, verify_state),
            Obj::NObj(x) => self.verify_n_obj_well_defined(x, verify_state),
            Obj::QObj(x) => self.verify_q_obj_well_defined(x, verify_state),
            Obj::ZObj(x) => self.verify_z_obj_well_defined(x, verify_state),
            Obj::RObj(x) => self.verify_r_obj_well_defined(x, verify_state),
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
            Obj::QPos(x) => self.verify_q_pos_well_defined(x, verify_state),
            Obj::ZPos(x) => self.verify_z_pos_well_defined(x, verify_state),
            Obj::RPos(x) => self.verify_r_pos_well_defined(x, verify_state),
            Obj::QNeg(x) => self.verify_q_neg_well_defined(x, verify_state),
            Obj::ZNeg(x) => self.verify_z_neg_well_defined(x, verify_state),
            Obj::RNeg(x) => self.verify_r_neg_well_defined(x, verify_state),
            Obj::QNz(x) => self.verify_q_nz_well_defined(x, verify_state),
            Obj::ZNz(x) => self.verify_z_nz_well_defined(x, verify_state),
            Obj::RNz(x) => self.verify_r_nz_well_defined(x, verify_state),
        }
    }

    fn verify_identifier_well_defined(&self, identifier: &Identifier, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        if self.runtime_context.is_defined_identifier_obj(identifier) {
            Ok(())
        } else {
            Err(WellDefinedError::new("identifier not defined", vec![], None))
        }
    }

    fn verify_identifier_with_mod_well_defined(&self, _x: &IdentifierWithMod, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_identifier_with_mod_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_field_access_well_defined(&self, _x: &FieldAccess, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_field_access_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_field_access_with_mod_well_defined(&self, _x: &FieldAccessWithMod, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_field_access_with_mod_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_fn_obj_well_defined(&self, _fn_obj: &FnObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_fn_obj_well_defined 此函数还没有 implement", vec![], None))
    }

    fn require_obj_in_r(&self, obj: &Obj, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        let r_obj = Obj::RObj(RObj::new());
        let in_fact = InFact::new(obj.clone(), r_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_atomic_fact(&atomic_fact, verify_state)?;
        Ok(())
    }

    fn require_obj_in_z(&self, obj: &Obj, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        let z_obj = Obj::ZObj(ZObj::new());
        let in_fact = InFact::new(obj.clone(), z_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_atomic_fact(&atomic_fact, verify_state)?;
        Ok(())
    }

    fn verify_add_well_defined(&self, add: &Add, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&add.left, verify_state)?;
        self.verify_obj_well_defined(&add.right, verify_state)?;
        self.require_obj_in_r(&add.left, verify_state)?;
        self.require_obj_in_r(&add.right, verify_state)?;
        Ok(())
    }

    fn verify_sub_well_defined(&self, sub: &Sub, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&sub.left, verify_state)?;
        self.verify_obj_well_defined(&sub.right, verify_state)?;
        self.require_obj_in_r(&sub.left, verify_state)?;
        self.require_obj_in_r(&sub.right, verify_state)?;
        Ok(())
    }

    fn verify_mul_well_defined(&self, mul: &Mul, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&mul.left, verify_state)?;
        self.verify_obj_well_defined(&mul.right, verify_state)?;
        self.require_obj_in_r(&mul.left, verify_state)?;
        self.require_obj_in_r(&mul.right, verify_state)?;
        Ok(())
    }

    fn verify_div_well_defined(&self, div: &Div, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
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

    fn verify_mod_well_defined(&self, m: &Mod, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&m.left, verify_state)?;
        self.verify_obj_well_defined(&m.right, verify_state)?;
        self.require_obj_in_z(&m.left, verify_state)?;
        self.require_obj_in_z(&m.right, verify_state)?;
        let zero = Obj::Number(Number::new("0"));
        let not_equal_fact = NotEqualFact::new((*m.right).clone(), zero, None);
        self.verify_atomic_fact(&AtomicFact::NotEqualFact(not_equal_fact), verify_state)?;
        Ok(())
    }

    fn verify_pow_well_defined(&self, _pow: &Pow, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_pow_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_union_well_defined(&self, x: &Union, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_intersect_well_defined(&self, x: &Intersect, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())

    }

    fn verify_set_minus_well_defined(&self, x: &SetMinus, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_diff_well_defined(&self, x: &SetDiff, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        self.verify_obj_well_defined(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_cup_well_defined(&self, x: &Cup, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_cap_well_defined(&self, x: &Cap, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_list_set_well_defined(&self, x: &ListSet, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.list {
            self.verify_obj_well_defined(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_set_builder_well_defined(&self, _x: &SetBuilder, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_set_builder_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_fn_set_without_dom_well_defined(&self, x: &FnSetWithoutDom, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.param_sets {
            self.verify_obj_well_defined(obj, verify_state)?;
        }
        self.verify_obj_well_defined(&x.ret_set, verify_state)?;
        Ok(())
    }

    fn verify_fn_set_with_dom_well_defined(&self, _x: &FnSetWithDom, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_fn_set_with_dom_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_n_pos_obj_well_defined(&self, _x: &NPosObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_n_obj_well_defined(&self, _x: &NObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_q_obj_well_defined(&self, _x: &QObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_z_obj_well_defined(&self, _x: &ZObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_r_obj_well_defined(&self, _x: &RObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Ok(())
    }

    fn verify_inst_set_struct_obj_well_defined(&self, _x: &InstStructObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_inst_set_struct_obj_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_cart_well_defined(&self, _x: &Cart, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_cart_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_cart_dim_well_defined(&self, _x: &CartDim, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_cart_dim_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_proj_well_defined(&self, _x: &Proj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_proj_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_dim_well_defined(&self, _x: &Dim, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_dim_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_tuple_well_defined(&self, _x: &Tuple, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_tuple_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_count_well_defined(&self, _x: &Count, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_count_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_range_well_defined(&self, _x: &Range, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_range_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_closed_range_well_defined(&self, _x: &ClosedRange, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_closed_range_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_val_well_defined(&self, _x: &Val, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_val_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_power_set_well_defined(&self, _x: &PowerSet, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_power_set_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_choose_well_defined(&self, _x: &Choose, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_choose_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_obj_at_index_well_defined(&self, _x: &ObjAtIndex, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_obj_at_index_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_q_pos_well_defined(&self, _x: &QPos, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_q_pos_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_z_pos_well_defined(&self, _x: &ZPos, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_z_pos_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_r_pos_well_defined(&self, _x: &RPos, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_r_pos_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_q_neg_well_defined(&self, _x: &QNeg, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_q_neg_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_z_neg_well_defined(&self, _x: &ZNeg, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_z_neg_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_r_neg_well_defined(&self, _x: &RNeg, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_r_neg_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_q_nz_well_defined(&self, _x: &QNz, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_q_nz_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_z_nz_well_defined(&self, _x: &ZNz, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_z_nz_well_defined 此函数还没有 implement", vec![], None))
    }

    fn verify_r_nz_well_defined(&self, _x: &RNz, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        Err(WellDefinedError::new("verify_r_nz_well_defined 此函数还没有 implement", vec![], None))
    }
}
