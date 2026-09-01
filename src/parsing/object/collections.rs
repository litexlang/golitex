//! Collection-shaped objects, argument groups, intervals, and set builders.

use crate::prelude::*;
use std::collections::HashMap;

use super::expression::{validate_litex_name_for_parse, validate_module_path_segment_for_parse};

impl Runtime {
    pub fn parse_braced_objs(&mut self, tb: &mut TokenBlock) -> Result<Vec<Obj>, RuntimeError> {
        tb.skip_token(LEFT_BRACE)?;
        if tb.current_token_is_equal_to(RIGHT_BRACE) {
            tb.skip_token(RIGHT_BRACE)?;
            return Ok(vec![]);
        }
        let mut objs = vec![self.parse_obj(tb)?];
        while tb.current_token_is_equal_to(COMMA) {
            tb.skip_token(COMMA)?;
            objs.push(self.parse_obj(tb)?);
        }
        tb.skip_token(RIGHT_BRACE)?;
        Ok(objs)
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
            Obj::Atom(AtomObj::Bound(p)) => Some(p.name()),
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
                BindingScope::LocalBinder,
                &set_builder_param,
                tb.line_file.clone(),
            )?;
            let parsed = (|| -> Result<Obj, RuntimeError> {
                let second = this.parse_obj(tb)?;
                if tb.current()? == COLON {
                    tb.skip_token(COLON)?;

                    let user_names = vec![a.name.clone()];
                    this.validate_user_fn_param_names_for_parse(&user_names, tb.line_file.clone())?;
                    let empty: HashMap<String, Obj> = HashMap::new();
                    let second_inst = this.inst_obj(&second, &empty, SubstitutionMode::Exact)?;

                    let mut facts_inst = Vec::new();
                    loop {
                        let f = this.parse_inline_quantifier_free_fact(tb)?;
                        facts_inst.push(this.inst_quantifier_free_fact(
                            &f,
                            &empty,
                            SubstitutionMode::Exact,
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
            this.end_parsing_scope(&set_builder_param);
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
