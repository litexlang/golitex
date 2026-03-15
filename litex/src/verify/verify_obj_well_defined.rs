use crate::obj::{
    Add, Cap, Cart, CartDim, Choose, ClosedRange, Count, Cup, Dim, Div, FieldAccess, FieldAccessWithMod,
    FnObj, FnSetWithDom, FnSetWithoutDom, Identifier, IdentifierWithMod, InstStructObj, ListSet, Mod,
    Mul, Number, Obj, ObjAtIndex, PowerSet, Pow, Proj, RObj, Range, SetBuilder, SetDiff, SetMinus, Sub, Tuple, Union, Val, ZObj,
    Intersect, FnSetObj, 
};
use crate::error::{WellDefinedError, StmtError};
use crate::verify::VerifyState;
use crate::fact::{AtomicFact, NotEqualFact, IsCartFact, IsNonemptySetFact, Fact};
use crate::fact::InFact;
use crate::execute::Executor;
use crate::stmt::parameter_type_and_property::{ParamDefWithParamSet, ParamDefWithParamType, ParamType};
use crate::common::helper::todo_error_message;

// well-defined check for obj
impl<'a> Executor<'a> {
    /// If obj is cacheable (not FnSetWithDom or SetBuilder) and found in well-defined cache, returns Some(()).
    fn verify_obj_well_defined_from_cache_if_known(&self, obj: &Obj) -> Option<()> {
        let use_cache = !matches!(obj, Obj::FnSetWithDom(_) | Obj::SetBuilder(_));
        if !use_cache {
            return None;
        }
        let key = obj.to_string();
        if self.runtime_context.cache_well_defined_obj_contains(&key) {
            Some(())
        } else {
            None
        }
    }

    pub fn verify_obj_well_defined_and_store_cache(&mut self, obj: &Obj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        if self.verify_obj_well_defined_from_cache_if_known(obj).is_some() {
            return Ok(());
        }

        let use_cache = !matches!(obj, Obj::FnSetWithDom(_) | Obj::SetBuilder(_));

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
        }?;

        if use_cache {
            self.runtime_context.top_level_env().cache_well_defined_obj_except_fn_set_with_dom_and_set_builder.insert(obj.to_string(), ());
        }
        Ok(())
    }

    fn verify_identifier_well_defined(&self, identifier: &Identifier) -> Result<(), WellDefinedError> {
        if self.runtime_context.is_defined_identifier_obj(identifier) {
            Ok(())
        } else {
            Err(WellDefinedError::new("identifier not defined".to_string(), vec![], None))
        }
    }

    fn verify_identifier_with_mod_well_defined(&self, x: &IdentifierWithMod) -> Result<(), WellDefinedError> {
        let _ = x;
        Err(WellDefinedError::new("verify_identifier_with_mod_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_field_access_well_defined(&self, x: &FieldAccess) -> Result<(), WellDefinedError> {
        let _ = x;
        Err(WellDefinedError::new("verify_field_access_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_field_access_with_mod_well_defined(&self, x: &FieldAccessWithMod) -> Result<(), WellDefinedError> {
        let _ = x;
        Err(WellDefinedError::new("verify_field_access_with_mod_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_fn_obj_well_defined(&mut self, fn_obj: &FnObj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let mut the_set_where_current_fn_obj_is_in = self.runtime_context.find_fn_definition_for_atom(&fn_obj.head).ok_or_else(|| WellDefinedError::new(
            todo_error_message("verify_fn_obj_well_defined: function head identifier has no known definition yet".to_string()).to_string(),
            vec![],
            None,
        ))?.clone();

        for args in fn_obj.body.iter() {
            match &the_set_where_current_fn_obj_is_in {
                FnSetObj::FnSetWithDom(fn_set_with_dom) => {
                    self.verify_fn_obj_well_defined_against_fn_set_with_dom(args, &fn_set_with_dom, verify_state)?;
                }
                FnSetObj::FnSetWithoutDom(fn_set_without_dom) => {
                    self.verify_fn_obj_args_well_defined_against_fn_set_without_dom(args, &fn_set_without_dom, verify_state)?;
                }
            }

            let set_where_the_next_fn_obj_is_in = the_set_where_current_fn_obj_is_in.ret_set();
            the_set_where_current_fn_obj_is_in = match *set_where_the_next_fn_obj_is_in {
                Obj::FnSetWithDom(e) => FnSetObj::FnSetWithDom(e),
                Obj::FnSetWithoutDom(e) => FnSetObj::FnSetWithoutDom(e),
                _ => {
                    return Err(WellDefinedError::new(
                        format!("expect return set of {} to be a fn_set object.", the_set_where_current_fn_obj_is_in.to_string()),
                        vec![],
                        None,
                    ));
                }
            };
        }

        Ok(())
    }

    /// Verify that the given FnObj is well-defined with respect to a FnSetWithDom definition.
    fn verify_fn_obj_well_defined_against_fn_set_with_dom(
        &mut self,
        args: &Vec<Box<Obj>>,
        fn_set_with_dom: &FnSetWithDom,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let param_count = fn_set_with_dom.params_def_with_set.len();
        if args.len() != param_count {
            return Err(WellDefinedError::new(
                format!("number of args ({}) does not match fn set with dom param count ({})", args.len(), param_count),
                vec![],
                None,
            ));
        }

        for (index, arg) in args.iter().enumerate() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
            let param_set = &fn_set_with_dom.params_def_with_set[index].1;
            let in_fact = InFact::new((**arg).clone(), param_set.clone(), None);
            self.verify_fact(&Fact::AtomicFact(AtomicFact::InFact(in_fact)), verify_state)?;
        }

        Ok(())
    }

    /// Verify that the given FnObj is well-defined with respect to a FnSetWithoutDom definition.
    fn verify_fn_obj_args_well_defined_against_fn_set_without_dom(
        &mut self,
        args: &Vec<Box<Obj>>,
        fn_set_without_dom: &FnSetWithoutDom,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let param_count = fn_set_without_dom.param_sets.len();
        if args.len() != param_count {
            return Err(WellDefinedError::new(
                format!("number of args ({}) does not match fn set without dom param count ({})", args.len(), param_count),
                vec![],
                None,
            ));
        }

        for (index, arg) in args.iter().enumerate() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
            let param_set = &fn_set_without_dom.param_sets[index];
            let in_fact = InFact::new((**arg).clone(), (**param_set).clone(), None);
            self.verify_fact(&Fact::AtomicFact(AtomicFact::InFact(in_fact)), verify_state)?;
        }

        Ok(())
    }

    fn require_obj_in_r(&mut self, obj: &Obj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let r_obj = Obj::RObj(RObj::new());
        let in_fact = InFact::new(obj.clone(), r_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_fact(&Fact::AtomicFact(atomic_fact), verify_state)?;
        Ok(())
    }

    fn require_obj_in_z(&mut self, obj: &Obj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let z_obj = Obj::ZObj(ZObj::new());
        let in_fact = InFact::new(obj.clone(), z_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_fact(&Fact::AtomicFact(atomic_fact), verify_state)?;
        Ok(())
    }

    fn verify_add_well_defined(&mut self, add: &Add, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&add.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&add.right, verify_state)?;
        self.require_obj_in_r(&add.left, verify_state)?;
        self.require_obj_in_r(&add.right, verify_state)?;
        Ok(())
    }

    fn verify_sub_well_defined(&mut self, sub: &Sub, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&sub.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&sub.right, verify_state)?;
        self.require_obj_in_r(&sub.left, verify_state)?;
        self.require_obj_in_r(&sub.right, verify_state)?;
        Ok(())
    }

    fn verify_mul_well_defined(&mut self, mul: &Mul, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&mul.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&mul.right, verify_state)?;
        self.require_obj_in_r(&mul.left, verify_state)?;
        self.require_obj_in_r(&mul.right, verify_state)?;
        Ok(())
    }

    fn verify_div_well_defined(&mut self, div: &Div, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&div.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&div.right, verify_state)?;

        let zero = Obj::Number(Number::new("0".to_string()));
        let not_equal_fact = NotEqualFact::new((*div.right).clone(), zero, None);
        let atomic_fact = AtomicFact::NotEqualFact(not_equal_fact);
        self.verify_fact(&Fact::AtomicFact(atomic_fact), verify_state)?;
        
        self.require_obj_in_r(&div.left, verify_state)?;
        self.require_obj_in_r(&div.right, verify_state)?;
        Ok(())
    }

    fn verify_mod_well_defined(&mut self, m: &Mod, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&m.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&m.right, verify_state)?;
        self.require_obj_in_z(&m.left, verify_state)?;
        self.require_obj_in_z(&m.right, verify_state)?;
        let zero = Obj::Number(Number::new("0".to_string()));
        let not_equal_fact = NotEqualFact::new((*m.right).clone(), zero, None);
        self.verify_fact(&Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal_fact)), verify_state)?;
        Ok(())
    }

    fn verify_pow_well_defined(&self, _pow: &Pow, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = verify_state;
        Err(WellDefinedError::new("verify_pow_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_union_well_defined(&mut self, x: &Union, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_intersect_well_defined(&mut self, x: &Intersect, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())

    }

    fn verify_set_minus_well_defined(&mut self, x: &SetMinus, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_set_diff_well_defined(&mut self, x: &SetDiff, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&x.right, verify_state)?;
        Ok(())
    }

    fn verify_cup_well_defined(&mut self, x: &Cup, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_cap_well_defined(&mut self, x: &Cap, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.left, verify_state)?;
        Ok(())
    }

    fn verify_list_set_well_defined(&mut self, x: &ListSet, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.list {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
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
            return Err(WellDefinedError::new(format!("failed to verify well-defined of set builder {}", x.to_string()), vec![StmtError::ExecError(e)], None));
        }

        for fact in x.facts.iter() {
            if let Err(e) = self.verify_fact_well_defined_and_store_and_infer(&(fact.from_ref_to_cloned_fact()), verify_state) {
                return Err(WellDefinedError::new(format!("failed to verify well-defined of set builder {}", x.to_string()), vec![StmtError::ExecError(e)], None));
            }
        }

        Ok(())
    }


    fn verify_fn_set_without_dom_well_defined(&mut self, x: &FnSetWithoutDom, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.param_sets {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        self.verify_obj_well_defined_and_store_cache(&x.ret_set, verify_state)?;
        Ok(())
    }

    fn verify_fn_set_with_dom_well_defined(&mut self, x: &FnSetWithDom, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.runtime_context.new_env();
        let result = self.verify_fn_set_with_dom_well_defined_body(x, verify_state);
        self.runtime_context.delete_env();
        result
    }

    fn verify_fn_set_with_dom_well_defined_body(&mut self, x: &FnSetWithDom, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        if let Err(e) = self.verify_obj_well_defined_and_store_cache(&x.ret_set, verify_state) {
            return Err(WellDefinedError::new(format!("failed to verify well-defined of fn set with dom {}", x.to_string()), vec![StmtError::WellDefinedError(e)], None));
        }
        
        
        for param_def_with_set in x.params_def_with_set.iter() {
            if let Err(e) = self.define_params_with_set(param_def_with_set) {
                return Err(WellDefinedError::new(format!("failed to verify well-defined of fn set with dom {}", x.to_string()), vec![StmtError::ExecError(e)], None));
            }
        }

        for fact in x.dom_facts.iter() {
            if let Err(e) = self.verify_fact_well_defined_and_store_and_infer(&(fact.from_ref_to_cloned_fact()), verify_state) {
                return Err(WellDefinedError::new(format!("failed to verify well-defined of fn set with dom {}", x.to_string()), vec![StmtError::ExecError(e)], None));
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
        let param_defs = if let Some(def) = self.runtime_context.get_set_struct_with_fields_definition_by_name(x.struct_name.to_string().as_str()) {
            &def.params_def_with_type
        } else if let Some(def) = self.runtime_context.get_set_struct_with_no_field_definition_by_name(x.struct_name.to_string().as_str()) {
            &def.params_def_with_type
        } else {
            return Err(WellDefinedError::new(format!("set struct definition not found {}", x.struct_name.to_string()), vec![], None));
        };
        let facts = ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(param_defs, &x.args)
            .map_err(|e| WellDefinedError::new(format!("failed to build facts for inst struct {}: {}", x.struct_name, e.error_body()), vec![e], None))?;
        for fact in facts.iter() {
            self.verify_fact(fact, verify_state).map_err(|e| WellDefinedError::new(
                format!("exec_fact failed for inst struct obj arg (struct {})", x.struct_name),
                vec![StmtError::VerifyError(e)],
                None,
            ))?;
        }

        Ok(())
    }

    fn verify_cart_well_defined(&mut self, x: &Cart, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        for obj in &x.args {
            self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
        }
        Ok(())
    }

    fn verify_cart_dim_well_defined(&mut self, x: &CartDim, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;

        let is_cart_fact = AtomicFact::IsCartFact(IsCartFact::new((*x.set).clone(), None));
        self.verify_fact(&Fact::AtomicFact(is_cart_fact), verify_state)?;
        
        Ok(())
    }

    fn verify_proj_well_defined(&mut self, x: &Proj, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_proj_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_dim_well_defined(&mut self, x: &Dim, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_dim_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_tuple_well_defined(&mut self, x: &Tuple, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_tuple_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_count_well_defined(&mut self, x: &Count, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_count_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_range_well_defined(&mut self, x: &Range, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_range_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_closed_range_well_defined(&mut self, x: &ClosedRange, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_closed_range_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_val_well_defined(&mut self, x: &Val, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_val_well_defined 此函数还没有 implement".to_string(), vec![], None))
    }

    fn verify_power_set_well_defined(&mut self, x: &PowerSet, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        Ok(())
    }

    fn verify_choose_well_defined(&mut self, x: &Choose, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&x.set, verify_state)?;
        let is_nonempty_set_fact = AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new((*x.set).clone(), None));
        self.verify_fact(&Fact::AtomicFact(is_nonempty_set_fact), verify_state)?;
        Ok(())
    }

    fn verify_obj_at_index_well_defined(&self, x: &ObjAtIndex, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        let _ = x;
        let _ = verify_state;
        Err(WellDefinedError::new("verify_obj_at_index_well_defined 此函数还没有 implement".to_string(), vec![], None))
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

impl<'a> Executor<'a> {
    pub fn verify_param_type_well_defined(&mut self, param_type: &ParamType, verify_state: &VerifyState) -> Result<(), WellDefinedError> {
        match param_type {
            ParamType::Set(_) => Ok(()),
            ParamType::NonemptySet(_) => Ok(()),
            ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(obj) => self.verify_obj_well_defined_and_store_cache(obj, verify_state),
        }
    }
}