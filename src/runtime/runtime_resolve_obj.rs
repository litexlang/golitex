use crate::prelude::*;

impl Runtime {
    pub fn resolve_obj_to_number(&self, obj: &Obj) -> Option<Number> {
        if let Some(number) = obj.evaluate_to_normalized_decimal_number() {
            return Some(number);
        }
        self.get_normalized_decimal_number_value_of_obj(&obj.to_string())
    }

    pub fn resolve_obj(&self, obj: &Obj) -> Obj {
        match obj {
            Obj::Number(number) => Obj::Number(number.clone()),
            Obj::Add(add) => {
                let result = Obj::Add(Add::new(
                    self.resolve_obj(&add.left),
                    self.resolve_obj(&add.right),
                ));
                let calculated_result = result.evaluate_to_normalized_decimal_number();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Sub(sub) => {
                let result = Obj::Sub(Sub::new(
                    self.resolve_obj(&sub.left),
                    self.resolve_obj(&sub.right),
                ));
                let calculated_result = result.evaluate_to_normalized_decimal_number();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Mul(mul) => {
                let result = Obj::Mul(Mul::new(
                    self.resolve_obj(&mul.left),
                    self.resolve_obj(&mul.right),
                ));
                let calculated_result = result.evaluate_to_normalized_decimal_number();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Mod(mod_obj) => {
                let result = Obj::Mod(Mod::new(
                    self.resolve_obj(&mod_obj.left),
                    self.resolve_obj(&mod_obj.right),
                ));
                let calculated_result = result.evaluate_to_normalized_decimal_number();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Pow(pow) => {
                let result = Obj::Pow(Pow::new(
                    self.resolve_obj(&pow.base),
                    self.resolve_obj(&pow.exponent),
                ));
                let calculated_result = result.evaluate_to_normalized_decimal_number();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Div(div) => {
                let result = Obj::Div(Div::new(
                    self.resolve_obj(&div.left),
                    self.resolve_obj(&div.right),
                ));
                let calculated_result = result.evaluate_to_normalized_decimal_number();
                if let Some(calculated_result) = calculated_result {
                    Obj::Number(calculated_result)
                } else {
                    result
                }
            }
            Obj::Identifier(_)
            | Obj::IdentifierWithMod(_)
            | Obj::FieldAccess(_)
            | Obj::FieldAccessWithMod(_)
            | Obj::FnObj(_) => {
                if let Some(number) = self.resolve_obj_to_number(obj) {
                    Obj::Number(number)
                } else {
                    obj.clone()
                }
            }
            Obj::Count(count) => match &*count.set {
                Obj::ListSet(list_set) => Obj::Number(Number::new(list_set.list.len().to_string())),
                _ => obj.clone(),
            },
            Obj::TupleDim(dim) => match &*dim.arg {
                Obj::Tuple(tuple) => Obj::Number(Number::new(tuple.args.len().to_string())),
                _ => obj.clone(),
            },
            Obj::CartDim(cart_dim) => match &*cart_dim.set {
                Obj::Cart(cart) => Obj::Number(Number::new(cart.args.len().to_string())),
                _ => obj.clone(),
            },
            Obj::Proj(proj) => match &*proj.set {
                Obj::Cart(cart) => {
                    let projection_index_number = self.resolve_obj_to_number(&proj.dim);
                    if let Some(projection_index_number) = projection_index_number {
                        let projection_index_parsed_result =
                            projection_index_number.normalized_value.parse::<usize>();
                        if let Ok(projection_index_one_based) = projection_index_parsed_result {
                            if projection_index_one_based >= 1
                                && projection_index_one_based <= cart.args.len()
                            {
                                return (*cart.args[projection_index_one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                _ => {
                    let known_cart_obj = self.get_known_cart_obj_of_obj(&proj.set.to_string());
                    if let Some(known_cart_obj) = known_cart_obj {
                        let projection_index_number = self.resolve_obj_to_number(&proj.dim);
                        if let Some(projection_index_number) = projection_index_number {
                            let projection_index_parsed_result =
                                projection_index_number.normalized_value.parse::<usize>();
                            if let Ok(projection_index_one_based) = projection_index_parsed_result {
                                if projection_index_one_based >= 1
                                    && projection_index_one_based <= known_cart_obj.args.len()
                                {
                                    return (*known_cart_obj.args[projection_index_one_based - 1])
                                        .clone();
                                }
                            }
                        }
                    }
                    obj.clone()
                }
            },
            Obj::ObjAtIndex(obj_at_index) => match &*obj_at_index.obj {
                Obj::Tuple(tuple) => {
                    let tuple_index_number = self.resolve_obj_to_number(&obj_at_index.index);
                    if let Some(tuple_index_number) = tuple_index_number {
                        let tuple_index_parsed_result =
                            tuple_index_number.normalized_value.parse::<usize>();
                        if let Ok(tuple_index_one_based) = tuple_index_parsed_result {
                            if tuple_index_one_based >= 1
                                && tuple_index_one_based <= tuple.args.len()
                            {
                                return (*tuple.args[tuple_index_one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                _ => {
                    let known_tuple_obj =
                        self.get_obj_equal_to_tuple(&obj_at_index.obj.to_string());
                    if let Some(known_tuple_obj) = known_tuple_obj {
                        let tuple_index_number = self.resolve_obj_to_number(&obj_at_index.index);
                        if let Some(tuple_index_number) = tuple_index_number {
                            let tuple_index_parsed_result =
                                tuple_index_number.normalized_value.parse::<usize>();
                            if let Ok(tuple_index_one_based) = tuple_index_parsed_result {
                                if tuple_index_one_based >= 1
                                    && tuple_index_one_based <= known_tuple_obj.args.len()
                                {
                                    return (*known_tuple_obj.args[tuple_index_one_based - 1])
                                        .clone();
                                }
                            }
                        }
                    }
                    obj.clone()
                }
            },
            _ => obj.clone(),
        }
    }
}
