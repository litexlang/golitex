use crate::prelude::*;
use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

pub fn to_python(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let mut tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;

    let mut stmts: Vec<Stmt> = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        run_stmt_at_global_env(&stmt, runtime)?;
        stmts.push(stmt);
    }

    extract_python_from_stmts(&stmts, runtime)
}

pub fn to_python_from_source(source_code: &str, entry_label: &str) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_python(normalized.as_str(), &mut runtime)
}

pub fn to_python_from_file(file_path: &str) -> Result<String, RuntimeError> {
    let resolved_path = resolve_file_path(file_path)?;
    let mut runtime = Runtime::new();
    match discover_repository_for_file(&mut runtime, resolved_path.as_str())? {
        Some(target) => to_python_project_run(&mut runtime, target),
        None => {
            let source = read_source(resolved_path.as_str())?;
            runtime.new_file_path_new_env_new_name_scope(resolved_path.as_str());
            to_python(source.as_str(), &mut runtime)
        }
    }
}

pub fn to_python_from_repository(repository_path: &str) -> Result<String, RuntimeError> {
    let mut runtime = Runtime::new();
    let target = discover_repository(&mut runtime, repository_path)?;
    to_python_project_run(&mut runtime, target)
}

fn to_python_project_run(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> Result<String, RuntimeError> {
    let root_module_id = runtime
        .module_manager
        .entry_module_id
        .expect("discovered project should have an entry module");
    if target == RepositoryFileTarget::Module(root_module_id) {
        return to_python_project_target(runtime, target);
    }
    if !project_target_is_inside_module(runtime, target, root_module_id) {
        return Err(file_error(
            "litex.config",
            "selected target is not inside the entry module export tree".to_string(),
        ));
    }
    to_python_project_prefix(runtime, root_module_id, target)
}

fn to_python_project_prefix(
    runtime: &mut Runtime,
    module_id: ModuleId,
    selected_target: RepositoryFileTarget,
) -> Result<String, RuntimeError> {
    let (module_path, config_imports, run_targets) = {
        let module = runtime
            .module_manager
            .module(module_id)
            .expect("discovered module should exist");
        (
            module.main_file_path.clone(),
            module.config_imports.clone(),
            module.run_targets.clone(),
        )
    };
    let pushed_frame = runtime.current_module_id() != module_id;
    if pushed_frame {
        runtime.push_module_execution_frame(module_id, module_path.as_str());
    }
    let output = (|| {
        let mut fragments = vec![];
        for config_import in config_imports {
            let fragment = to_python_project_target(
                runtime,
                RepositoryFileTarget::Module(config_import.module_id),
            )?;
            push_python_fragment(&mut fragments, fragment);
        }
        for run_target in run_targets {
            let target_matches = repository_target_matches(selected_target, run_target);
            let target_contains = matches!(
                run_target,
                ImportTarget::Module(child_module_id)
                    if project_target_is_inside_module(runtime, selected_target, child_module_id)
            );
            let fragment = if target_contains && !target_matches {
                let ImportTarget::Module(child_module_id) = run_target else {
                    unreachable!("only a module target can contain another target")
                };
                to_python_project_prefix(runtime, child_module_id, selected_target)?
            } else {
                to_python_project_target(runtime, repository_file_target(run_target))?
            };
            push_python_fragment(&mut fragments, fragment);
            if target_matches || target_contains {
                return Ok(fragments.join("\n"));
            }
        }
        Err(file_error(
            module_path.as_str(),
            "selected target is missing from its recursive ordered [export] tree".to_string(),
        ))
    })();
    if pushed_frame {
        runtime.pop_execution_frame();
    }
    output
}

fn to_python_project_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> Result<String, RuntimeError> {
    match target {
        RepositoryFileTarget::Module(module_id) => {
            let (module_path, config_imports, run_targets) = {
                let module = runtime
                    .module_manager
                    .module(module_id)
                    .expect("discovered module should exist");
                (
                    module.main_file_path.clone(),
                    module.config_imports.clone(),
                    module.run_targets.clone(),
                )
            };
            let pushed_frame = runtime.current_module_id() != module_id;
            if pushed_frame {
                runtime.push_module_execution_frame(module_id, module_path.as_str());
            }
            let output = (|| {
                let mut fragments = vec![];
                for config_import in config_imports {
                    let fragment = to_python_project_target(
                        runtime,
                        RepositoryFileTarget::Module(config_import.module_id),
                    )?;
                    push_python_fragment(&mut fragments, fragment);
                }
                for run_target in run_targets {
                    let fragment = match run_target {
                        ImportTarget::File { module_id, file_id } => to_python_project_target(
                            runtime,
                            RepositoryFileTarget::File { module_id, file_id },
                        ),
                        ImportTarget::Module(module_id) => to_python_project_target(
                            runtime,
                            RepositoryFileTarget::Module(module_id),
                        ),
                    }?;
                    push_python_fragment(&mut fragments, fragment);
                }
                Ok(fragments.join("\n"))
            })();
            if pushed_frame {
                runtime.pop_execution_frame();
            }
            output
        }
        RepositoryFileTarget::File { module_id, file_id } => {
            let (source_path, status) = {
                let file = runtime
                    .module_manager
                    .module(module_id)
                    .and_then(|module| module.file(file_id))
                    .expect("registered project file should exist");
                (file.source_path.clone(), file.status)
            };
            if status == FileStatus::Loaded {
                return Ok(String::new());
            }
            if status == FileStatus::Loading {
                return Err(file_error(
                    source_path.as_str(),
                    "cyclic project entry while generating Python".to_string(),
                ));
            }
            runtime
                .module_manager
                .module_mut(module_id)
                .and_then(|module| module.file_mut(file_id))
                .expect("registered project file should exist")
                .status = FileStatus::Loading;
            runtime.push_file_execution_frame(module_id, file_id, source_path.as_str());
            let output = read_source(source_path.as_str())
                .and_then(|source| to_python(source.as_str(), runtime));
            runtime.pop_execution_frame();
            runtime
                .module_manager
                .module_mut(module_id)
                .and_then(|module| module.file_mut(file_id))
                .expect("registered project file should exist")
                .status = if output.is_ok() {
                FileStatus::Loaded
            } else {
                FileStatus::Unloaded
            };
            output
        }
    }
}

fn push_python_fragment(fragments: &mut Vec<String>, fragment: String) {
    if !fragment.trim().is_empty()
        && fragment.trim() != "# No Python-extractable Litex definitions."
    {
        fragments.push(fragment);
    }
}

fn repository_target_matches(target: RepositoryFileTarget, import_target: ImportTarget) -> bool {
    match (target, import_target) {
        (RepositoryFileTarget::Module(target_module), ImportTarget::Module(module_id)) => {
            target_module == module_id
        }
        (
            RepositoryFileTarget::File {
                module_id: target_module,
                file_id: target_file,
            },
            ImportTarget::File { module_id, file_id },
        ) => target_module == module_id && target_file == file_id,
        _ => false,
    }
}

fn repository_file_target(target: ImportTarget) -> RepositoryFileTarget {
    match target {
        ImportTarget::Module(module_id) => RepositoryFileTarget::Module(module_id),
        ImportTarget::File { module_id, file_id } => {
            RepositoryFileTarget::File { module_id, file_id }
        }
    }
}

fn project_target_is_inside_module(
    runtime: &Runtime,
    target: RepositoryFileTarget,
    ancestor_module_id: ModuleId,
) -> bool {
    let mut module_id = Some(match target {
        RepositoryFileTarget::Module(module_id) => module_id,
        RepositoryFileTarget::File { module_id, .. } => module_id,
    });
    while let Some(current) = module_id {
        if current == ancestor_module_id {
            return true;
        }
        module_id = runtime
            .module_manager
            .module(current)
            .and_then(|module| module.parent_module_id);
    }
    false
}

fn resolve_file_path(file_path: &str) -> Result<String, RuntimeError> {
    let path = Path::new(file_path);
    let absolute = if path.is_absolute() {
        PathBuf::from(path)
    } else {
        env::current_dir()
            .map_err(|error| {
                file_error(
                    file_path,
                    format!("failed to get current directory: {}", error),
                )
            })?
            .join(path)
    };
    let canonical = fs::canonicalize(&absolute)
        .map_err(|error| file_error(file_path, format!("could not read file: {}", error)))?;
    canonical
        .to_str()
        .map(str::to_string)
        .ok_or_else(|| file_error(file_path, "file path is not valid UTF-8".to_string()))
}

fn read_source(path: &str) -> Result<String, RuntimeError> {
    fs::read_to_string(path)
        .map(|source| source.replace('\r', ""))
        .map_err(|error| file_error(path, format!("could not read file: {}", error)))
}

fn file_error(path: &str, message: String) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message,
        (0, Rc::from(path)),
    ))
    .into()
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

    fn extract_stmt(&mut self, stmt: &Stmt, runtime: &Runtime) -> Result<(), RuntimeError> {
        match stmt {
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(s)) => {
                self.extract_have_obj_equal_stmt(s)
            }
            Stmt::DefAlgoStmt(s) => self.extract_def_algo_stmt(s, runtime),
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

    fn extract_def_algo_stmt(
        &mut self,
        stmt: &DefAlgoStmt,
        runtime: &Runtime,
    ) -> Result<(), RuntimeError> {
        let function = runtime.declared_identifier_obj(&stmt.name);
        let Some(fn_set) = runtime.get_fn_range_function_body(&function) else {
            return Err(python_extract_error(
                &stmt.line_file,
                format!(
                    "python extractor v1 cannot find the function declaration for implementation `{}`",
                    stmt.name
                ),
            ));
        };
        self.validate_real_function_signature(
            &stmt.name,
            &fn_set.params_def_with_set,
            &fn_set.dom_facts,
            fn_set.ret_set.as_ref(),
            &stmt.line_file,
        )?;

        let expected_params = ParamGroupWithSet::collect_param_names(&fn_set.params_def_with_set);
        if stmt.params.len() != expected_params.len() {
            return Err(python_extract_error(
                &stmt.line_file,
                format!(
                    "python extractor v1 found {} algorithm parameters for `{}`, but its function declaration has {}",
                    stmt.params.len(),
                    stmt.name,
                    expected_params.len()
                ),
            ));
        }
        for param in stmt.params.iter() {
            validate_python_name(param, &stmt.line_file)?;
        }
        if stmt.cases.is_empty() && stmt.default_return.is_none() {
            return Err(python_extract_error(
                &stmt.line_file,
                format!(
                    "python extractor v1 needs a return expression for function implementation `{}`",
                    stmt.name
                ),
            ));
        }

        let params_in_scope: HashSet<String> = stmt.params.iter().cloned().collect();
        self.functions.insert(stmt.name.clone());
        self.push_blank_line_before_function();
        self.lines
            .push(format!("def {}({}):", stmt.name, stmt.params.join(", ")));

        for (index, case) in stmt.cases.iter().enumerate() {
            let condition = self.python_atomic_condition(&case.condition, &params_in_scope)?;
            let expr = self.python_expr(
                &case.return_stmt.value,
                &params_in_scope,
                &case.return_stmt.line_file,
            )?;
            let keyword = if index == 0 { "if" } else { "elif" };
            self.lines.push(format!("    {} {}:", keyword, condition));
            self.lines.push(format!("        return {}", expr));
        }

        if let Some(default_return) = &stmt.default_return {
            let expr = self.python_expr(
                &default_return.value,
                &params_in_scope,
                &default_return.line_file,
            )?;
            self.lines.push(format!("    return {}", expr));
        } else {
            self.lines
                .push("    raise AssertionError(\"unreachable verified Litex cases\")".to_string());
        }
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
            AtomObj::DefAlgo(p) => p.name.as_str(),
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

fn extract_python_from_stmts(stmts: &[Stmt], runtime: &Runtime) -> Result<String, RuntimeError> {
    let mut extractor = PythonExtractor::new();
    for stmt in stmts.iter() {
        extractor.extract_stmt(stmt, runtime)?;
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
