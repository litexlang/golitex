use crate::prelude::*;
use std::collections::HashMap;

use super::parse_obj::{validate_litex_name_for_parse, validate_module_path_segment_for_parse};

impl Runtime {
    pub fn parse_braced_objs(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(vec![]);
        }
        let mut objs = self.parse_call_argument_or_unfold(tb)?;
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.extend(self.parse_call_argument_or_unfold(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        Ok(objs)
    }

    /// `unfold value` is an argument-list spread. A tuple literal contributes
    /// its elements; a struct-declared value contributes its declared fields in source
    /// order. Struct header parameters and `<=>:` facts are never arguments.
    /// Example: `f(unfold pair, unfold group)`.
    fn parse_call_argument_or_unfold(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<Obj>, RuntimeError> {
        if !tb.current_token_is_equal_to(UNFOLD) {
            return Ok(vec![self.parse_obj(tb)?]);
        }

        self.parse_unfold_call_argument(tb)
    }

    // Keep the comparatively large unfold/error path out of the ordinary
    // braced-object parser frame. Parser recursion is already deep for nested
    // set builders and function signatures, and Rust's test threads use a
    // deliberately small default stack.
    #[inline(never)]
    fn parse_unfold_call_argument(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let line_file = tb.line_file.clone();
        tb.skip_token(UNFOLD)?;
        if tb.exceed_end_of_head()
            || tb.current_token_is_equal_to(COMMA)
            || tb.current_token_is_equal_to(RIGHT_BRACE)
        {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unfold expects a tuple value or an object declared with a struct carrier"
                        .to_string(),
                    line_file,
                ),
            )));
        }

        let obj = self.parse_obj(tb)?;

        if let Obj::Tuple(tuple) = &obj {
            return Ok(tuple.args.iter().map(|arg| arg.as_ref().clone()).collect());
        }

        // A declaration-owned struct carrier wins over tuple facts learned
        // later. In particular, materializing a template instance may expose
        // its tuple constructor, but `unfold` must still preserve the fields
        // selected by the template body's direct declaration.
        if let Ok(struct_obj) = self.struct_view_for_field_access_receiver(&obj, line_file.clone())
        {
            return self.struct_field_arguments_for_unfold(&obj, struct_obj, line_file);
        }

        let known_tuple_arity = self
            .get_obj_equal_to_tuple(&obj)
            .map(|tuple| tuple.args.len())
            .or_else(|| {
                let symbol = match &obj {
                    Obj::Atom(atom) => atom.symbol_ref(),
                    _ => None,
                }?;
                self.default_tuple_view_for_symbol(symbol)
                    .map(|cart| cart.args.len())
            })
            .or_else(|| self.get_obj_tuple_cart(&obj).map(|cart| cart.args.len()));
        if let Some(arity) = known_tuple_arity {
            return Ok((1..=arity)
                .map(|index| {
                    ObjAtIndex::new(obj.clone(), Number::new(index.to_string()).into()).into()
                })
                .collect());
        }

        let struct_obj = self
            .struct_view_for_field_access_receiver(&obj, line_file.clone())
            .map_err(|cause| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "unfold expects a tuple with compile-time arity or an object whose declaration has a direct `&Struct` carrier"
                        .to_string(),
                    line_file.clone(),
                    Some(cause),
                    vec![],
                )))
            })?;
        self.struct_field_arguments_for_unfold(&obj, struct_obj, line_file)
    }

    fn struct_field_arguments_for_unfold(
        &self,
        obj: &Obj,
        struct_obj: StructObj,
        line_file: LineFile,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let struct_name = struct_obj.name.to_string();
        let definition = self
            .get_struct_definition_by_name(&struct_name)
            .or_else(|| self.parsed_struct_definition_by_name(&struct_name))
            .ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("cannot unfold undefined struct `{}`", struct_name),
                        line_file.clone(),
                    ),
                ))
            })?;

        Ok(definition
            .fields
            .iter()
            .map(|field| {
                ObjAsStructInstanceWithFieldAccess::new(
                    struct_obj.clone(),
                    obj.clone(),
                    field.name().to_string(),
                )
                .into()
            })
            .collect())
    }

    pub(super) fn parse_two_sided_interval_literal(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        tb.skip_token(INTERVAL_LITERAL_PREFIX)?;
        let left_closed = match tb.current()? {
            LEFT_BRACE => false,
            LEFT_BRACKET => true,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal after `'` expects `(` or `[`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        tb.skip()?;
        if tb.current_token_is_equal_to(COMMA) {
            if left_closed {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "left-unbounded interval must start with `(`; use `'(,a)` or `'(,a]`"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.skip_token(COMMA)?;
            if tb.current_token_is_equal_to(RIGHT_BRACE) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal cannot omit both endpoints; use `R`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let right = self.parse_obj(tb)?;
            if tb.current_token_is_equal_to(COMMA) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal expects exactly two endpoints".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let right_closed = match tb.current()? {
                RIGHT_BRACE => false,
                RIGHT_BRACKET => true,
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "interval literal expects `)` or `]` after its right endpoint"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            };
            tb.skip()?;
            return Ok(if right_closed {
                OneSideInfinityIntervalObj::new_right_closed(right).into()
            } else {
                OneSideInfinityIntervalObj::new_right_open(right).into()
            });
        }

        let left = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(if left_closed {
                OneSideInfinityIntervalObj::new_left_closed(left).into()
            } else {
                OneSideInfinityIntervalObj::new_left_open(left).into()
            });
        }
        if tb.current_token_is_equal_to(RIGHT_BRACKET) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "right-unbounded interval must end with `)`; use `'(a,)` or `'[a,)`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let right = self.parse_obj(tb)?;
        if tb.current_token_is_equal_to(COMMA) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "interval literal expects exactly two endpoints".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let right_closed = match tb.current()? {
            RIGHT_BRACE => false,
            RIGHT_BRACKET => true,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "interval literal expects `)` or `]` after its right endpoint".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };
        tb.skip()?;

        Ok(match (left_closed, right_closed) {
            (false, false) => IntervalObj::new_left_open_right_open(left, right).into(),
            (false, true) => IntervalObj::new_left_open_right_closed(left, right).into(),
            (true, false) => IntervalObj::new_left_closed_right_open(left, right).into(),
            (true, true) => IntervalObj::new_left_closed_right_closed(left, right).into(),
        })
    }

    pub(super) fn parse_angle_bracketed_objs(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<Obj>, RuntimeError> {
        tb.skip_token(LESS)?;
        if tb.current_token_is_equal_to(GREATER) {
            tb.skip_token(GREATER)?;
            return Ok(vec![]);
        }
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(GREATER)?;
        Ok(objs)
    }

    pub(super) fn parse_fn_obj_arg_group(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let args = self.parse_braced_objs(tb)?;
        if args.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "function application expects at least one argument".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(args)
    }

    pub fn parse_braced_obj(&mut self, tb: &mut TokenBlock) -> Result<Obj, RuntimeError> {
        let mut parsed_args = self.parse_braced_objs(tb)?;
        if parsed_args.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "expected exactly 1 argument".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let parsed_obj = parsed_args.remove(0);
        Ok(parsed_obj)
    }

    pub(super) fn parse_replacement_obj(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "replacement expects 2 arguments (prop name, source set)".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let prop_name = self.parse_valid_replacement_prop_name(tb)?;
        tb.skip_token(COMMA)?;
        let source_set = self.parse_obj(tb)?;
        tb.skip_token(RIGHT_BRACE)?;
        Ok(Replacement::new(prop_name, source_set).into())
    }

    fn parse_valid_replacement_prop_name(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AtomicName, RuntimeError> {
        let left = tb.advance()?;
        if !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
            let mut parts = vec![left];
            while !tb.exceed_end_of_head() && tb.current()? == MOD_SIGN {
                tb.skip()?;
                let part = tb.advance()?;
                parts.push(part);
            }
            let right = parts
                .pop()
                .expect("qualified name should have a local name");
            for (index, part) in parts.iter().enumerate() {
                validate_module_path_segment_for_parse(part, index == 0, tb.line_file.clone())
                    .map_err(|e| {
                        RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                            None,
                            "replacement expects its first argument to be a prop name".to_string(),
                            tb.line_file.clone(),
                            Some(e),
                            vec![],
                        )))
                    })?;
            }
            validate_litex_name_for_parse(&right, tb.line_file.clone()).map_err(|e| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "replacement expects its first argument to be a prop name".to_string(),
                    tb.line_file.clone(),
                    Some(e),
                    vec![],
                )))
            })?;
            let module_name = self.canonical_module_name_for_parse(&parts.join(MOD_SIGN));
            Ok(AtomicName::WithMod(module_name, right))
        } else {
            validate_litex_name_for_parse(&left, tb.line_file.clone()).map_err(|e| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "replacement expects its first argument to be a prop name".to_string(),
                    tb.line_file.clone(),
                    Some(e),
                    vec![],
                )))
            })?;
            Ok(self.qualify_bare_atomic_name_if_needed(left))
        }
    }

    /// Parses a comma-separated object list until the next token is not a comma.
    pub fn parse_obj_list(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        Ok(objs)
    }

    pub(super) fn parse_set_builder_or_set_list(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        tb.skip_token(LEFT_CURLY_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_CURLY_BRACE) {
            tb.skip_token(RIGHT_CURLY_BRACE)?;
            return Ok(self.new_parsed_list_set(vec![])?.into());
        }

        let left = self.parse_obj(tb)?;
        // Plain identifiers and parsing-time free-param atoms (e.g. forall-bound `x`) must both
        // allow `{ x S : ... }` set-builder syntax; only `Identifier` was handled originally.
        let name_for_set_builder = match &left {
            Obj::Atom(AtomObj::Identifier(a)) => Some(a.name.as_str()),
            Obj::Atom(AtomObj::IdentifierWithMod(m)) => Some(m.name.as_str()),
            Obj::Atom(AtomObj::Forall(p)) => Some(p.name()),
            Obj::Atom(AtomObj::Def(p)) => Some(p.name()),
            Obj::Atom(AtomObj::Exist(p)) => Some(p.name()),
            Obj::Atom(AtomObj::SetBuilder(p)) => Some(p.name()),
            Obj::Atom(AtomObj::FnSet(p)) => Some(p.name()),
            Obj::Atom(AtomObj::Induc(p)) => Some(p.name()),
            Obj::Atom(AtomObj::DefAlgo(p)) => Some(p.name()),
            _ => None,
        };
        if let Some(name) = name_for_set_builder {
            if tb.current_token_is_equal_to(COMMA) || tb.current()? == RIGHT_CURLY_BRACE {
                self.parse_list_set_obj_with_leftmost_obj(tb, left)
            } else {
                self.parse_set_builder(tb, Identifier::new(name.to_string()))
            }
        } else {
            self.parse_list_set_obj_with_leftmost_obj(tb, left)
        }
    }

    pub(super) fn parse_instantiated_template_obj(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Obj, RuntimeError> {
        tb.skip_token(TEMPLATE_INSTANCE_PREFIX)?;
        let template_name = self.parse_module_qualified_reference_name(tb)?;
        let (left_token, right_token) = if tb.current_token_is_equal_to(LESS) {
            (LESS, GREATER)
        } else {
            (LEFT_CURLY_BRACE, RIGHT_CURLY_BRACE)
        };
        tb.skip_token(left_token)?;
        let mut args = Vec::new();
        if !tb.current_token_is_equal_to(right_token) {
            args.push(self.parse_obj(tb)?);
            while tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
                args.push(self.parse_obj(tb)?);
            }
        }
        tb.skip_token(right_token)?;
        let surface_name = format!(
            "{}{}{}{}{}",
            TEMPLATE_INSTANCE_PREFIX,
            template_name,
            LESS,
            vec_to_string_join_by_comma(&args),
            GREATER
        );
        let binding = self.template_instance_symbol_binding(&surface_name)?;
        Ok(InstantiatedTemplateObj::new(template_name, args, binding.as_ref()).into())
    }

    /// Parse set builder or list set after the first identifier; wraps body in a name block for the bound variable.
    fn parse_set_builder(
        &mut self,
        tb: &mut TokenBlock,
        a: Identifier,
    ) -> Result<Obj, RuntimeError> {
        self.run_in_local_parsing_time_name_scope(|this| {
            let set_builder_param = [a.name.clone()];
            let bindings = this.begin_parsing_scope(
                ParamObjType::SetBuilder,
                &set_builder_param,
                tb.line_file.clone(),
            )?;
            let parsed = (|| -> Result<Obj, RuntimeError> {
                let (second, default_struct_view) = this.parse_obj_with_default_struct_view(tb)?;
                if tb.current()? == COLON {
                    if let Some(struct_obj) = default_struct_view.as_ref() {
                        this.register_default_struct_view(&bindings, struct_obj);
                    }
                    tb.skip_token(COLON)?;

                    let user_names = vec![a.name.clone()];
                    this.validate_user_fn_param_names_for_parse(&user_names, tb.line_file.clone())?;
                    let empty: HashMap<String, Obj> = HashMap::new();
                    let second_inst = this.inst_obj(&second, &empty, ParamObjType::SetBuilder)?;

                    let mut facts_inst = Vec::new();
                    loop {
                        let f = this.parse_inline_quantifier_free_fact(tb)?;
                        facts_inst.push(this.inst_quantifier_free_fact(
                            &f,
                            &empty,
                            ParamObjType::SetBuilder,
                            None,
                        )?);
                        if tb.current()? == RIGHT_CURLY_BRACE {
                            break;
                        }
                        tb.skip_token(COMMA)?;
                    }
                    tb.skip_token(RIGHT_CURLY_BRACE)?;

                    Ok(SetBuilder::new(bindings[0].clone(), second_inst, facts_inst)?.into())
                } else {
                    Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "expected colon after first argument".to_string(),
                            tb.line_file.clone(),
                        ),
                    )))
                }
            })();
            this.end_parsing_scope(ParamObjType::SetBuilder, &set_builder_param);
            parsed
        })
    }

    /// Parses a list set after the first object, accepting optional commas between items.
    fn parse_list_set_obj_with_leftmost_obj(
        &mut self,
        tb: &mut TokenBlock,
        left_most_obj: Obj,
    ) -> Result<Obj, RuntimeError> {
        let mut objs = vec![left_most_obj];
        while tb.current()? != RIGHT_CURLY_BRACE {
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(self.new_parsed_list_set(objs)?.into())
    }

    pub fn parse_list_set_obj(&mut self, tb: &mut TokenBlock) -> Result<ListSet, RuntimeError> {
        let mut objs = vec![];
        tb.skip_token(LEFT_CURLY_BRACE)?;
        while tb.current()? != RIGHT_CURLY_BRACE {
            objs.push(self.parse_obj(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        self.new_parsed_list_set(objs)
    }
}
