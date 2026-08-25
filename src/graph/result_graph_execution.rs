use super::result_graph::ResultGraph;
use crate::prelude::*;
use std::collections::HashSet;

const GRAPH_NAME: &str = "litex-result-graph";
const GRAPH_VERSION: &str = "2";

#[derive(Default)]
pub struct DepSet {
    pub props: Vec<String>,
    pub fns: Vec<String>,
    pub structs: Vec<String>,
    pub templates: Vec<String>,
}

pub struct DepCollector {
    pub deps: DepSet,
    local_names: HashSet<String>,
}

/// Render a result graph while a runtime is still available for error text.
/// Successful graph semantics come only from `stmt_results`.
pub fn render_graph_from_stmt_results(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    runtime: &Runtime,
    stmt_results: &[StmtResult],
    runtime_error: Option<&RuntimeError>,
) -> (bool, String) {
    let ok = runtime_error.is_none();
    let error = runtime_error.map(|error| display_runtime_error_json(runtime, error, true));
    (
        ok,
        render_result_graph_document(
            target_kind,
            target_label,
            hide_file_paths,
            stmt_results,
            !ok,
            error,
        ),
    )
}

/// Render a completed successful result graph without a live `Runtime`.
pub fn render_result_graph_from_stmt_results(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    stmt_results: &[StmtResult],
) -> String {
    render_result_graph_document(
        target_kind,
        target_label,
        hide_file_paths,
        stmt_results,
        false,
        None,
    )
}

fn render_result_graph_document(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    stmt_results: &[StmtResult],
    partial: bool,
    error: Option<String>,
) -> String {
    let graph = ResultGraph::from_stmt_results(stmt_results);
    let mut fields = vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(GRAPH_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString(if partial { "error" } else { "success" }.to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(!partial)),
        ("partial".to_string(), JsonValue::Bool(partial)),
        (
            "target".to_string(),
            target_json_value(target_kind, target_label, hide_file_paths),
        ),
    ];
    if let Some(error) = error {
        fields.push(("error".to_string(), JsonValue::JsonString(error)));
    } else {
        fields.push(("error".to_string(), JsonValue::Null));
    }
    fields.push(("summary".to_string(), graph.summary_json()));
    fields.push(("nodes".to_string(), graph.nodes_json()));
    fields.push(("edges".to_string(), graph.edges_json()));
    fields.push((
        "mermaid".to_string(),
        JsonValue::JsonString(graph.mermaid()),
    ));

    render_json_value(&JsonValue::Object(fields), 0)
}

pub fn graph_target_error_output(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    message: String,
) -> (bool, String) {
    let output = JsonValue::Object(vec![
        (
            "graph".to_string(),
            JsonValue::JsonString(GRAPH_NAME.to_string()),
        ),
        (
            "graph_version".to_string(),
            JsonValue::JsonString(GRAPH_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString("error".to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(false)),
        ("partial".to_string(), JsonValue::Bool(false)),
        (
            "target".to_string(),
            target_json_value(target_kind, target_label, hide_file_paths),
        ),
        ("error".to_string(), JsonValue::JsonString(message)),
        (
            "summary".to_string(),
            ResultGraph::from_stmt_results(&[]).summary_json(),
        ),
        ("nodes".to_string(), JsonValue::Array(vec![])),
        ("edges".to_string(), JsonValue::Array(vec![])),
        (
            "mermaid".to_string(),
            JsonValue::JsonString("flowchart LR".to_string()),
        ),
    ]);
    (false, render_json_value(&output, 0))
}

fn target_json_value(target_kind: &str, target_label: &str, hide_file_paths: bool) -> JsonValue {
    let label = if hide_file_paths && target_kind != "code" {
        "entry".to_string()
    } else {
        target_label.to_string()
    };

    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString(target_kind.to_string()),
        ),
        ("label".to_string(), JsonValue::JsonString(label)),
    ])
}

impl DepSet {
    fn push_prop(&mut self, name: String) {
        if !self.props.contains(&name) {
            self.props.push(name);
        }
    }

    fn push_fn(&mut self, name: String) {
        if !self.fns.contains(&name) {
            self.fns.push(name);
        }
    }

    fn push_struct(&mut self, name: String) {
        if !self.structs.contains(&name) {
            self.structs.push(name);
        }
    }

    fn push_template(&mut self, name: String) {
        if !self.templates.contains(&name) {
            self.templates.push(name);
        }
    }
}

impl DepCollector {
    pub fn new() -> Self {
        Self {
            deps: DepSet::default(),
            local_names: HashSet::new(),
        }
    }

    pub fn add_local_name(&mut self, name: &str) {
        self.local_names.insert(name.to_string());
    }

    pub fn add_param_def_with_type(&mut self, params: &ParamDefWithType) {
        for name in params.collect_param_names() {
            self.add_local_name(&name);
        }
    }

    pub fn add_param_def_with_set(&mut self, params: &ParamDefWithSet) {
        for name in params.collect_param_names() {
            self.add_local_name(&name);
        }
    }

    pub fn collect_param_def_with_type_deps(&mut self, params: &ParamDefWithType) {
        for group in params.groups.iter() {
            if let ParamType::Obj(obj) = &group.param_type {
                self.collect_obj(obj);
            }
        }
    }

    pub fn collect_param_def_with_set_deps(&mut self, params: &ParamDefWithSet) {
        for group in params.groups.iter() {
            self.collect_obj(&group.param_type);
        }
    }

    pub fn collect_fn_set_clause(&mut self, clause: &FnSetClause) {
        self.collect_param_def_with_set_deps(&clause.params_def_with_set);
        self.add_param_def_with_set(&clause.params_def_with_set);
        for fact in clause.dom_facts.iter() {
            self.collect_quantifier_free_fact(fact);
        }
        self.collect_obj(&clause.ret_set);
    }

    pub fn collect_fn_set_body(&mut self, body: &FnSetBody) {
        self.collect_param_def_with_set_deps(&body.params_def_with_set);
        self.add_param_def_with_set(&body.params_def_with_set);
        for fact in body.dom_facts.iter() {
            self.collect_quantifier_free_fact(fact);
        }
        self.collect_obj(&body.ret_set);
    }

    pub fn collect_anonymous_fn(&mut self, anonymous_fn: &AnonymousFn) {
        let old = self.local_names.clone();
        self.collect_fn_set_body(&anonymous_fn.body);
        self.collect_obj(&anonymous_fn.equal_to);
        self.local_names = old;
    }

    pub fn collect_have_fn_by_induc_case(&mut self, case: &HaveFnByInducCase) {
        self.collect_and_chain_atomic_fact(&case.case_fact);
        match &case.body {
            HaveFnByInducCaseBody::EqualTo(obj) => self.collect_obj(obj),
            HaveFnByInducCaseBody::NestedCases(cases) => {
                for nested in cases.iter() {
                    self.collect_have_fn_by_induc_case(nested);
                }
            }
        }
    }

    pub fn collect_fact(&mut self, fact: &Fact) {
        match fact {
            Fact::AtomicFact(a) => self.collect_atomic_fact(a),
            Fact::ExistFact(e) => self.collect_exist_fact(e),
            Fact::OrFact(o) => self.collect_or_fact(o),
            Fact::AndFact(a) => self.collect_and_fact(a),
            Fact::ChainFact(c) => self.collect_chain_fact(c),
            Fact::ForallFact(f) => self.collect_forall_fact(f),
            Fact::ForallFactWithIff(f) => {
                self.collect_forall_fact(&f.forall_fact);
                for fact in f.iff_facts.iter() {
                    self.collect_exist_or_and_chain_atomic_fact(fact);
                }
            }
            Fact::NotForall(f) => self.collect_forall_fact(&f.forall_fact),
        }
    }

    pub fn collect_forall_fact(&mut self, fact: &ForallFact) {
        let old = self.local_names.clone();
        self.collect_param_def_with_type_deps(&fact.params_def_with_type);
        self.add_param_def_with_type(&fact.params_def_with_type);
        for dom_fact in fact.dom_facts.iter() {
            self.collect_fact(dom_fact);
        }
        for then_fact in fact.then_facts.iter() {
            self.collect_exist_or_and_chain_atomic_fact(then_fact);
        }
        self.local_names = old;
    }

    pub fn collect_exist_fact(&mut self, fact: &ExistFactEnum) {
        let body = fact.spec();
        let old = self.local_names.clone();
        self.collect_param_def_with_type_deps(&body.params_def_with_type);
        self.add_param_def_with_type(&body.params_def_with_type);
        for body_fact in body.facts.iter() {
            self.collect_quantifier_free_fact(body_fact);
        }
        self.local_names = old;
    }

    pub fn collect_quantifier_free_fact(&mut self, fact: &QuantifierFreeFact) {
        match fact {
            QuantifierFreeFact::AtomicFact(a) => self.collect_atomic_fact(a),
            QuantifierFreeFact::AndFact(a) => self.collect_and_fact(a),
            QuantifierFreeFact::ChainFact(c) => self.collect_chain_fact(c),
            QuantifierFreeFact::OrFact(o) => self.collect_or_fact(o),
        }
    }

    pub fn collect_exist_or_and_chain_atomic_fact(&mut self, fact: &ExistOrAndChainAtomicFact) {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => self.collect_atomic_fact(a),
            ExistOrAndChainAtomicFact::AndFact(a) => self.collect_and_fact(a),
            ExistOrAndChainAtomicFact::ChainFact(c) => self.collect_chain_fact(c),
            ExistOrAndChainAtomicFact::OrFact(o) => self.collect_or_fact(o),
            ExistOrAndChainAtomicFact::ExistFact(e) => self.collect_exist_fact(e),
        }
    }

    pub fn collect_and_chain_atomic_fact(&mut self, fact: &AndChainAtomicFact) {
        match fact {
            AndChainAtomicFact::AtomicFact(a) => self.collect_atomic_fact(a),
            AndChainAtomicFact::AndFact(a) => self.collect_and_fact(a),
            AndChainAtomicFact::ChainFact(c) => self.collect_chain_fact(c),
        }
    }

    pub fn collect_and_fact(&mut self, fact: &AndFact) {
        for atomic in fact.facts.iter() {
            self.collect_atomic_fact(atomic);
        }
    }

    pub fn collect_or_fact(&mut self, fact: &OrFact) {
        for branch in fact.facts.iter() {
            self.collect_and_chain_atomic_fact(branch);
        }
    }

    pub fn collect_chain_fact(&mut self, fact: &ChainFact) {
        for prop_name in fact.prop_names.iter() {
            let name = prop_name.to_string();
            if !is_builtin_predicate(&name) {
                self.deps.push_prop(name);
            }
        }
        for obj in fact.objs.iter() {
            self.collect_obj(obj);
        }
    }

    pub fn collect_atomic_fact(&mut self, fact: &AtomicFact) {
        match fact {
            AtomicFact::NormalAtomicFact(f) => {
                let name = f.predicate.to_string();
                if !is_builtin_predicate(&name) {
                    self.deps.push_prop(name);
                }
                for obj in f.body.iter() {
                    self.collect_obj(obj);
                }
            }
            AtomicFact::NotNormalAtomicFact(f) => {
                let name = f.predicate.to_string();
                if !is_builtin_predicate(&name) {
                    self.deps.push_prop(name);
                }
                for obj in f.body.iter() {
                    self.collect_obj(obj);
                }
            }
            _ => {
                for obj in fact.args_ref() {
                    self.collect_obj(obj);
                }
            }
        }
    }

    pub fn collect_obj(&mut self, obj: &Obj) {
        match obj {
            Obj::Atom(_)
            | Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_) => {}
            Obj::FnObj(fn_obj) => {
                self.collect_fn_head(&fn_obj.head);
                for group in fn_obj.body.iter() {
                    for arg in group.iter() {
                        self.collect_obj(arg);
                    }
                }
            }
            Obj::Add(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Sub(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Mul(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Div(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Mod(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Quot(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Gcd(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Lcm(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Min(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Max(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Exp(x) => self.collect_obj(&x.arg),
            Obj::Ln(x) => self.collect_obj(&x.arg),
            Obj::Sign(x) => self.collect_obj(&x.arg),
            Obj::Factorial(x) => self.collect_obj(&x.arg),
            Obj::Pow(x) => self.collect_two_objs(&x.base, &x.exponent),
            Obj::Log(x) => self.collect_two_objs(&x.base, &x.arg),
            Obj::Union(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Intersect(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::SetMinus(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::Range(x) => self.collect_two_objs(&x.start, &x.end),
            Obj::ClosedRange(x) => self.collect_two_objs(&x.start, &x.end),
            Obj::IntervalObj(x) => self.collect_two_objs(x.start(), x.end()),
            Obj::MatrixAdd(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::MatrixSub(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::MatrixMul(x) => self.collect_two_objs(&x.left, &x.right),
            Obj::MatrixScalarMul(x) => self.collect_two_objs(&x.scalar, &x.matrix),
            Obj::MatrixPow(x) => self.collect_two_objs(&x.base, &x.exponent),
            Obj::Proj(x) => self.collect_two_objs(&x.set, &x.dim),
            Obj::ObjAtIndex(x) => self.collect_two_objs(&x.obj, &x.index),
            Obj::FiniteSeqSet(x) => self.collect_two_objs(&x.set, &x.n),
            Obj::MatrixSet(x) => {
                self.collect_obj(&x.set);
                self.collect_obj(&x.row_len);
                self.collect_obj(&x.col_len);
            }
            Obj::Sum(x) => {
                self.collect_obj(&x.start);
                self.collect_obj(&x.end);
                self.collect_obj(&x.func);
            }
            Obj::SumOfFiniteSet(x) => {
                self.collect_obj(&x.set);
                self.collect_obj(&x.func);
            }
            Obj::Product(x) => {
                self.collect_obj(&x.start);
                self.collect_obj(&x.end);
                self.collect_obj(&x.func);
            }
            Obj::ProductOfFiniteSet(x) => {
                self.collect_obj(&x.set);
                self.collect_obj(&x.func);
            }
            Obj::Reduce(x) => {
                for child in [&x.start, &x.end, &x.func, &x.op, &x.seed] {
                    self.collect_obj(child);
                }
            }
            Obj::FiniteSetReduce(x) => {
                for child in [&x.set, &x.func, &x.op, &x.seed] {
                    self.collect_obj(child);
                }
            }
            Obj::Abs(x) => self.collect_obj(&x.arg),
            Obj::Floor(x) => self.collect_obj(&x.arg),
            Obj::Ceil(x) => self.collect_obj(&x.arg),
            Obj::Sin(x) => self.collect_obj(&x.arg),
            Obj::Arcsin(x) => self.collect_obj(&x.arg),
            Obj::Cos(x) => self.collect_obj(&x.arg),
            Obj::Tan(x) => self.collect_obj(&x.arg),
            Obj::Cot(x) => self.collect_obj(&x.arg),
            Obj::RealPart(x) => self.collect_obj(&x.arg),
            Obj::ImaginaryPart(x) => self.collect_obj(&x.arg),
            Obj::ComplexAbs(x) => self.collect_obj(&x.arg),
            Obj::Sqrt(x) => self.collect_obj(&x.arg),
            Obj::BigUnion(x) => self.collect_obj(&x.left),
            Obj::BigIntersect(x) => self.collect_obj(&x.left),
            Obj::IndexUnion(x) => {
                self.collect_obj(&x.index_set);
                self.collect_obj(&x.ambient_set);
                self.collect_obj(&x.family_fn);
            }
            Obj::IndexIntersect(x) => {
                self.collect_obj(&x.index_set);
                self.collect_obj(&x.ambient_set);
                self.collect_obj(&x.family_fn);
            }
            Obj::PowerSet(x) => self.collect_obj(&x.set),
            Obj::FiniteSetSize(x) => self.collect_obj(&x.set),
            Obj::FiniteSetMax(x) => self.collect_obj(&x.set),
            Obj::FiniteSetMin(x) => self.collect_obj(&x.set),
            Obj::FnRange(x) => self.collect_obj(&x.function),
            Obj::Replacement(x) => {
                self.deps.push_prop(x.prop_name.to_string());
                self.collect_obj(&x.source_set);
            }
            Obj::TupleDim(x) => self.collect_obj(&x.arg),
            Obj::CartDim(x) => self.collect_obj(&x.set),
            Obj::OneSideInfinityIntervalObj(x) => self.collect_obj(x.start()),
            Obj::SeqSet(x) => self.collect_obj(&x.set),
            Obj::ListSet(x) => {
                for obj in x.list.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::GeneralCart(x) => {
                self.collect_obj(&x.index_set);
                self.collect_obj(&x.family_set);
                self.collect_obj(&x.family_fn);
            }
            Obj::Cart(x) => {
                for obj in x.args.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::Tuple(x) => {
                for obj in x.args.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::FiniteSeqListObj(x) => {
                for obj in x.objs.iter() {
                    self.collect_obj(obj);
                }
            }
            Obj::MatrixListObj(x) => {
                for row in x.rows.iter() {
                    for obj in row.iter() {
                        self.collect_obj(obj);
                    }
                }
            }
            Obj::SetBuilder(x) => {
                self.collect_obj(&x.param_set);
                let old = self.local_names.clone();
                self.add_local_name(x.param_name());
                for fact in x.facts.iter() {
                    self.collect_quantifier_free_fact(fact);
                }
                self.local_names = old;
            }
            Obj::FnSet(x) => {
                let old = self.local_names.clone();
                self.collect_fn_set_body(&x.body);
                self.local_names = old;
            }
            Obj::AnonymousFn(x) => self.collect_anonymous_fn(x),
            Obj::StructObj(x) => {
                self.deps.push_struct(x.name.to_string());
                for param in x.params.iter() {
                    self.collect_obj(param);
                }
            }
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                self.deps.push_struct(x.struct_obj.name.to_string());
                for param in x.struct_obj.params.iter() {
                    self.collect_obj(param);
                }
                self.collect_obj(&x.obj);
            }
            Obj::InstantiatedTemplateObj(x) => {
                self.deps.push_template(x.template_name.to_string());
                for arg in x.args.iter() {
                    self.collect_obj(arg);
                }
            }
        }
    }

    pub fn collect_fn_head(&mut self, head: &FnObjHead) {
        match head {
            FnObjHead::Identifier(identifier) => {
                if !self.local_names.contains(&identifier.name)
                    && !is_builtin_identifier_name(&identifier.name)
                {
                    self.deps.push_fn(identifier.name.clone());
                }
            }
            FnObjHead::IdentifierWithMod(identifier) => {
                self.deps.push_fn(format!(
                    "{}{}{}",
                    identifier.mod_name, MOD_SIGN, identifier.name
                ));
            }
            FnObjHead::AnonymousFnLiteral(a) => self.collect_anonymous_fn(a),
            FnObjHead::FiniteSeqListObj(list) => {
                for obj in list.objs.iter() {
                    self.collect_obj(obj);
                }
            }
            FnObjHead::ObjAtIndex(obj_at_index) => {
                self.collect_obj(&obj_at_index.obj);
                self.collect_obj(&obj_at_index.index);
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                self.deps
                    .push_struct(field_access.struct_obj.name.to_string());
                for param in field_access.struct_obj.params.iter() {
                    self.collect_obj(param);
                }
                self.collect_obj(&field_access.obj);
            }
            FnObjHead::InstantiatedTemplateObj(template_obj) => {
                self.deps
                    .push_template(template_obj.template_name.to_string());
                for arg in template_obj.args.iter() {
                    self.collect_obj(arg);
                }
            }
            FnObjHead::MatrixOperator(matrix) => self.collect_obj(matrix),
            FnObjHead::Bound(_) => {}
        }
    }

    pub fn collect_two_objs(&mut self, left: &Obj, right: &Obj) {
        self.collect_obj(left);
        self.collect_obj(right);
    }
}

#[cfg(test)]
#[path = "../../tests/unit/graph/result_graph_execution/tests.rs"]
mod tests;
