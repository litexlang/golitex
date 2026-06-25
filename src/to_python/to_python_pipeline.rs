use crate::prelude::*;
use std::collections::HashSet;

pub fn to_python(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let mut tokenizer = Tokenizer::new();
    let current_file_path = runtime.module_manager.borrow().current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;

    let mut stmts: Vec<Stmt> = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        run_stmt_at_global_env(&stmt, runtime)?;
        stmts.push(stmt);
    }

    extract_python_from_stmts(&stmts)
}

pub fn to_python_from_source_after_builtins(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_python(normalized.as_str(), &mut runtime)
}

struct PythonExtractor {
    lines: Vec<String>,
    constants: HashSet<String>,
    functions: HashSet<String>,
}

impl PythonExtractor {
    fn new() -> Self {
        PythonExtractor {
            lines: Vec::new(),
            constants: HashSet::new(),
            functions: HashSet::new(),
        }
    }

    fn extract_stmt(&mut self, stmt: &Stmt) -> Result<(), RuntimeError> {
        match stmt {
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(s)) => {
                self.extract_have_obj_equal_stmt(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(s)) if s.as_algo => {
                self.extract_have_fn_equal_stmt(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(s)) if s.as_algo => {
                self.extract_have_fn_equal_case_by_case_stmt(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(s)) if s.as_algo => {
                Err(python_extract_error(
                    &s.line_file,
                    "python extractor v1 does not support `have fn as algo ... by induc`",
                ))
            }
            Stmt::DefAlgoStmt(s) => Err(python_extract_error(
                &s.line_file,
                "python extractor v1 does not support standalone `algo`; use `have fn as algo ...`",
            )),
            _ => Ok(()),
        }
    }

    fn finish(self) -> String {
        if self.lines.is_empty() {
            return "# No Python-extractable Litex definitions.".to_string();
        }
        self.lines.join("\n")
    }

    fn extract_have_obj_equal_stmt(&mut self, stmt: &HaveObjEqualStmt) -> Result<(), RuntimeError> {
        let names_with_types = stmt.param_def.collect_param_names_with_types();
        if names_with_types.len() != stmt.objs_equal_to.len() {
            return Err(python_extract_error(
                &stmt.line_file,
                "python extractor internal error: object definition arity mismatch",
            ));
        }

        let params = HashSet::new();
        for ((name, param_type), obj) in names_with_types.iter().zip(stmt.objs_equal_to.iter()) {
            if !is_numeric_param_type(param_type) {
                continue;
            }
            validate_python_name(name, &stmt.line_file)?;
            let expr = self.python_expr(obj, &params, &stmt.line_file)?;
            self.lines.push(format!("{} = {}", name, expr));
            self.constants.insert(name.clone());
        }

        Ok(())
    }

    fn extract_have_fn_equal_stmt(&mut self, stmt: &HaveFnEqualStmt) -> Result<(), RuntimeError> {
        let params_def = &stmt.equal_to_anonymous_fn.body.params_def_with_set;
        let dom_facts = &stmt.equal_to_anonymous_fn.body.dom_facts;
        let ret_set = stmt.equal_to_anonymous_fn.body.ret_set.as_ref();
        self.validate_real_function_signature(
            &stmt.name,
            params_def,
            dom_facts,
            ret_set,
            &stmt.line_file,
        )?;

        let params = ParamGroupWithSet::collect_param_names(params_def);
        let params_in_scope: HashSet<String> = params.iter().cloned().collect();
        let expr = self.python_expr(
            stmt.equal_to_anonymous_fn.equal_to.as_ref(),
            &params_in_scope,
            &stmt.line_file,
        )?;

        self.push_blank_line_before_function();
        self.lines
            .push(format!("def {}({}):", stmt.name, params.join(", ")));
        self.lines.push(format!("    return {}", expr));
        self.functions.insert(stmt.name.clone());
        Ok(())
    }

    fn extract_have_fn_equal_case_by_case_stmt(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<(), RuntimeError> {
        self.validate_real_function_signature(
            &stmt.name,
            &stmt.fn_set_clause.params_def_with_set,
            &stmt.fn_set_clause.dom_facts,
            &stmt.fn_set_clause.ret_set,
            &stmt.line_file,
        )?;
        if stmt.cases.len() != stmt.equal_tos.len() {
            return Err(python_extract_error(
                &stmt.line_file,
                "python extractor internal error: case count does not match return count",
            ));
        }
        if stmt.cases.is_empty() {
            return Err(python_extract_error(
                &stmt.line_file,
                "python extractor v1 needs at least one case for `have fn as algo ... by cases`",
            ));
        }

        let params =
            ParamGroupWithSet::collect_param_names(&stmt.fn_set_clause.params_def_with_set);
        let params_in_scope: HashSet<String> = params.iter().cloned().collect();
        self.push_blank_line_before_function();
        self.lines
            .push(format!("def {}({}):", stmt.name, params.join(", ")));

        for (index, (case, equal_to)) in stmt.cases.iter().zip(stmt.equal_tos.iter()).enumerate() {
            let atomic_case = match case {
                AndChainAtomicFact::AtomicFact(a) => a,
                AndChainAtomicFact::AndFact(_) | AndChainAtomicFact::ChainFact(_) => {
                    return Err(python_extract_error(
                        &stmt.line_file,
                        "python extractor v1 supports only atomic `case` conditions",
                    ));
                }
            };
            let condition = self.python_atomic_condition(atomic_case, &params_in_scope)?;
            let expr = self.python_expr(equal_to, &params_in_scope, &stmt.line_file)?;
            let keyword = if index == 0 { "if" } else { "elif" };
            self.lines.push(format!("    {} {}:", keyword, condition));
            self.lines.push(format!("        return {}", expr));
        }

        self.lines
            .push("    raise AssertionError(\"unreachable verified Litex cases\")".to_string());
        self.functions.insert(stmt.name.clone());
        Ok(())
    }

    fn validate_real_function_signature(
        &self,
        name: &str,
        params_def: &ParamDefWithSet,
        dom_facts: &[OrAndChainAtomicFact],
        ret_set: &Obj,
        line_file: &LineFile,
    ) -> Result<(), RuntimeError> {
        validate_python_name(name, line_file)?;
        if !dom_facts.is_empty() {
            return Err(python_extract_error(
                line_file,
                format!(
                    "python extractor v1 does not support domain restrictions in `{}`",
                    name
                ),
            ));
        }
        for group in params_def.iter() {
            if !is_real_set_obj(group.set_obj()) {
                return Err(python_extract_error(
                    line_file,
                    format!(
                        "python extractor v1 supports only `R` function parameters; `{}` has parameter set `{}`",
                        name,
                        group.set_obj()
                    ),
                ));
            }
            for param_name in group.params.iter() {
                validate_python_name(param_name, line_file)?;
            }
        }
        if !is_real_set_obj(ret_set) {
            return Err(python_extract_error(
                line_file,
                format!(
                    "python extractor v1 supports only `R` function return values; `{}` returns `{}`",
                    name, ret_set
                ),
            ));
        }
        Ok(())
    }

    fn push_blank_line_before_function(&mut self) {
        if !self.lines.is_empty() {
            self.lines.push(String::new());
        }
    }

    fn python_atomic_condition(
        &self,
        fact: &AtomicFact,
        params: &HashSet<String>,
    ) -> Result<String, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(f) => self.python_binary_condition(&f.left, "==", &f.right, params, &f.line_file),
            AtomicFact::NotEqualFact(f) => self.python_binary_condition(&f.left, "!=", &f.right, params, &f.line_file),
            AtomicFact::LessFact(f) => self.python_binary_condition(&f.left, "<", &f.right, params, &f.line_file),
            AtomicFact::LessEqualFact(f) => self.python_binary_condition(&f.left, "<=", &f.right, params, &f.line_file),
            AtomicFact::GreaterFact(f) => self.python_binary_condition(&f.left, ">", &f.right, params, &f.line_file),
            AtomicFact::GreaterEqualFact(f) => self.python_binary_condition(&f.left, ">=", &f.right, params, &f.line_file),
            _ => Err(python_extract_error(
                &fact.line_file(),
                format!(
                    "python extractor v1 supports only equality and order comparison cases; got `{}`",
                    fact
                ),
            )),
        }
    }

    fn python_binary_condition(
        &self,
        left: &Obj,
        op: &str,
        right: &Obj,
        params: &HashSet<String>,
        line_file: &LineFile,
    ) -> Result<String, RuntimeError> {
        let left_expr = self.python_expr(left, params, line_file)?;
        let right_expr = self.python_expr(right, params, line_file)?;
        Ok(format!("{} {} {}", left_expr, op, right_expr))
    }

    fn python_expr(
        &self,
        obj: &Obj,
        params: &HashSet<String>,
        line_file: &LineFile,
    ) -> Result<String, RuntimeError> {
        match obj {
            Obj::Number(n) => Ok(python_float_literal(&n.normalized_value)),
            Obj::Atom(a) => self.python_atom(a, params, line_file),
            Obj::Add(a) => {
                self.python_binary_expr(a.left.as_ref(), "+", a.right.as_ref(), params, line_file)
            }
            Obj::Sub(s) => {
                self.python_binary_expr(s.left.as_ref(), "-", s.right.as_ref(), params, line_file)
            }
            Obj::Mul(m) => {
                self.python_binary_expr(m.left.as_ref(), "*", m.right.as_ref(), params, line_file)
            }
            Obj::Div(d) => {
                self.python_binary_expr(d.left.as_ref(), "/", d.right.as_ref(), params, line_file)
            }
            Obj::Pow(p) => self.python_binary_expr(
                p.base.as_ref(),
                "**",
                p.exponent.as_ref(),
                params,
                line_file,
            ),
            Obj::FnObj(f) => self.python_fn_call(f, params, line_file),
            _ => Err(python_extract_error(
                line_file,
                format!("python extractor v1 cannot translate object `{}`", obj),
            )),
        }
    }

    fn python_binary_expr(
        &self,
        left: &Obj,
        op: &str,
        right: &Obj,
        params: &HashSet<String>,
        line_file: &LineFile,
    ) -> Result<String, RuntimeError> {
        let left_expr = self.python_expr(left, params, line_file)?;
        let right_expr = self.python_expr(right, params, line_file)?;
        Ok(format!("({} {} {})", left_expr, op, right_expr))
    }

    fn python_atom(
        &self,
        atom: &AtomObj,
        params: &HashSet<String>,
        line_file: &LineFile,
    ) -> Result<String, RuntimeError> {
        let name = match atom {
            AtomObj::Identifier(i) => i.name.as_str(),
            AtomObj::FnSet(p) => p.name.as_str(),
            _ => {
                return Err(python_extract_error(
                    line_file,
                    format!("python extractor v1 cannot translate atom `{}`", atom),
                ));
            }
        };

        if params.contains(name) || self.constants.contains(name) {
            validate_python_name(name, line_file)?;
            return Ok(name.to_string());
        }

        Err(python_extract_error(
            line_file,
            format!(
                "python extractor v1 cannot translate name `{}` because it is not a function parameter or extracted constant",
                name
            ),
        ))
    }

    fn python_fn_call(
        &self,
        fn_obj: &FnObj,
        params: &HashSet<String>,
        line_file: &LineFile,
    ) -> Result<String, RuntimeError> {
        if fn_obj.body.len() != 1 {
            return Err(python_extract_error(
                line_file,
                format!(
                    "python extractor v1 does not support curried function call `{}`",
                    fn_obj
                ),
            ));
        }

        let fn_name = match fn_obj.head.as_ref() {
            FnObjHead::Identifier(i) => i.name.as_str(),
            _ => {
                return Err(python_extract_error(
                    line_file,
                    format!(
                        "python extractor v1 supports calls only to named extracted functions; got `{}`",
                        fn_obj.head
                    ),
                ));
            }
        };
        validate_python_name(fn_name, line_file)?;
        if !self.functions.contains(fn_name) {
            return Err(python_extract_error(
                line_file,
                format!(
                    "python extractor v1 cannot call `{}` because it has not been extracted earlier",
                    fn_name
                ),
            ));
        }

        let args = fn_obj.body[0]
            .iter()
            .map(|arg| self.python_expr(arg.as_ref(), params, line_file))
            .collect::<Result<Vec<String>, RuntimeError>>()?;
        Ok(format!("{}({})", fn_name, args.join(", ")))
    }
}

fn extract_python_from_stmts(stmts: &[Stmt]) -> Result<String, RuntimeError> {
    let mut extractor = PythonExtractor::new();
    for stmt in stmts.iter() {
        extractor.extract_stmt(stmt)?;
    }
    Ok(extractor.finish())
}

fn is_real_set_obj(obj: &Obj) -> bool {
    matches!(obj, Obj::StandardSet(StandardSet::R))
}

fn is_numeric_param_type(param_type: &ParamType) -> bool {
    match param_type {
        ParamType::Obj(obj) => is_numeric_set_obj(obj),
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => false,
    }
}

fn is_numeric_set_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::StandardSet(
            StandardSet::NPos
                | StandardSet::N
                | StandardSet::Q
                | StandardSet::Z
                | StandardSet::R
                | StandardSet::QPos
                | StandardSet::RPos
                | StandardSet::QNeg
                | StandardSet::ZNeg
                | StandardSet::RNeg
                | StandardSet::QNz
                | StandardSet::ZNz
                | StandardSet::RNz
        )
    )
}

fn python_float_literal(value: &str) -> String {
    if value.contains('.') || value.contains('e') || value.contains('E') {
        return value.to_string();
    }
    format!("{}.0", value)
}

fn validate_python_name(name: &str, line_file: &LineFile) -> Result<(), RuntimeError> {
    if is_python_identifier(name) {
        return Ok(());
    }
    Err(python_extract_error(
        line_file,
        format!(
            "python extractor v1 cannot emit `{}` as a Python identifier",
            name
        ),
    ))
}

fn is_python_identifier(name: &str) -> bool {
    if is_python_keyword(name) {
        return false;
    }
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if first != '_' && !first.is_ascii_alphabetic() {
        return false;
    }
    for ch in chars {
        if ch != '_' && !ch.is_ascii_alphanumeric() {
            return false;
        }
    }
    true
}

fn is_python_keyword(name: &str) -> bool {
    matches!(
        name,
        "False"
            | "None"
            | "True"
            | "and"
            | "as"
            | "assert"
            | "async"
            | "await"
            | "break"
            | "class"
            | "continue"
            | "def"
            | "del"
            | "elif"
            | "else"
            | "except"
            | "finally"
            | "for"
            | "from"
            | "global"
            | "if"
            | "import"
            | "in"
            | "is"
            | "lambda"
            | "nonlocal"
            | "not"
            | "or"
            | "pass"
            | "raise"
            | "return"
            | "try"
            | "while"
            | "with"
            | "yield"
    )
}

fn python_extract_error(line_file: &LineFile, msg: impl Into<String>) -> RuntimeError {
    RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        msg.into(),
        line_file.clone(),
        None,
        vec![],
    )))
}
