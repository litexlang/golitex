use crate::prelude::*;
use std::collections::HashSet;

impl FnObjHead {
    pub fn contains_forall_free_param_obj(&self) -> bool {
        let mut collector = FreeParamNameCollector::new(ParamObjType::Forall, false);
        self.collect_free_param_names_into(&mut collector);
        !collector.names.is_empty()
    }

    fn collect_free_param_names_into(&self, collector: &mut FreeParamNameCollector) {
        match self {
            FnObjHead::Identifier(param) => {
                collector.insert(ParamObjType::Identifier, &param.name);
            }
            FnObjHead::Forall(param) => collector.insert(ParamObjType::Forall, &param.name),
            FnObjHead::DefHeader(param) => {
                collector.insert(ParamObjType::DefHeader, &param.name);
            }
            FnObjHead::Exist(param) => collector.insert(ParamObjType::Exist, &param.name),
            FnObjHead::SetBuilder(param) => {
                collector.insert(ParamObjType::SetBuilder, &param.name);
            }
            FnObjHead::FnSet(param) => collector.insert(ParamObjType::FnSet, &param.name),
            FnObjHead::DefStructField(param) => {
                collector.insert(ParamObjType::DefStructField, &param.name);
            }
            FnObjHead::Induc(param) => collector.insert(ParamObjType::Induc, &param.name),
            FnObjHead::DefAlgo(param) => collector.insert(ParamObjType::DefAlgo, &param.name),
            FnObjHead::TupleIndex(param) => {
                collector.insert(ParamObjType::TupleIndex, &param.name);
            }
            FnObjHead::CartIndex(param) => {
                collector.insert(ParamObjType::CartIndex, &param.name);
            }
            FnObjHead::AnonymousFnLiteral(anonymous_fn) => {
                collect_forall_free_param_names_in_fn_set_body(&anonymous_fn.body, collector);
                anonymous_fn
                    .equal_to
                    .collect_free_param_names_into(collector);
            }
            FnObjHead::FiniteSeqListObj(sequence) => {
                collect_forall_free_param_names_in_boxed_objs(&sequence.objs, collector);
            }
            FnObjHead::ObjAtIndex(obj_at_index) => {
                collect_forall_free_param_names_in_pair(
                    &obj_at_index.obj,
                    &obj_at_index.index,
                    collector,
                );
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                collect_forall_free_param_names_in_objs(&field_access.struct_obj.params, collector);
                field_access.obj.collect_free_param_names_into(collector);
            }
            FnObjHead::InstantiatedTemplateObj(template) => {
                collect_forall_free_param_names_in_objs(&template.args, collector);
            }
            FnObjHead::MatrixOperator(matrix) => {
                matrix.collect_free_param_names_into(collector);
            }
            FnObjHead::IdentifierWithMod(_) => {}
        }
    }
}

impl Obj {
    /// Conservatively collect every parameter-object name of `kind`, including binder headers.
    pub fn collect_param_obj_names(&self, kind: ParamObjType) -> HashSet<String> {
        let mut collector = FreeParamNameCollector::new(kind, true);
        self.collect_free_param_names_into(&mut collector);
        collector.names
    }

    /// Historical wrapper; this is an all-name set, not a scope-subtracted free-variable set.
    pub fn collect_forall_free_param_names(&self) -> HashSet<String> {
        self.collect_param_obj_names(ParamObjType::Forall)
    }

    pub fn contains_forall_free_param_obj(&self) -> bool {
        let mut collector = FreeParamNameCollector::new(ParamObjType::Forall, false);
        self.collect_free_param_names_into(&mut collector);
        !collector.names.is_empty()
    }

    fn collect_free_param_names_into(&self, collector: &mut FreeParamNameCollector) {
        match self {
            Obj::Atom(atom) => collector.collect_atom(atom),
            Obj::Number(_) | Obj::StandardSet(_) => {}
            Obj::FnObj(fn_obj) => {
                fn_obj.head.collect_free_param_names_into(collector);
                for args in &fn_obj.body {
                    collect_forall_free_param_names_in_boxed_objs(args, collector);
                }
            }
            Obj::Add(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Sub(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Mul(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Div(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Mod(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Pow(x) => collect_forall_free_param_names_in_pair(&x.base, &x.exponent, collector),
            Obj::Abs(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Sqrt(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Log(x) => collect_forall_free_param_names_in_pair(&x.base, &x.arg, collector),
            Obj::Union(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Intersect(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::SetMinus(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::SetDiff(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::BigUnion(x) => x.left.collect_free_param_names_into(collector),
            Obj::BigIntersect(x) => x.left.collect_free_param_names_into(collector),
            Obj::PowerSet(x) => x.set.collect_free_param_names_into(collector),
            Obj::FiniteSetMax(x) => x.set.collect_free_param_names_into(collector),
            Obj::FiniteSetMin(x) => x.set.collect_free_param_names_into(collector),
            Obj::GeneralCart(x) => {
                x.index_set.collect_free_param_names_into(collector);
                x.family_set.collect_free_param_names_into(collector);
                x.family_fn.collect_free_param_names_into(collector);
            }
            Obj::ListSet(x) => collect_forall_free_param_names_in_boxed_objs(&x.list, collector),
            Obj::SetBuilder(x) => {
                collector.insert_binder(ParamObjType::SetBuilder, &x.param);
                x.param_set.collect_free_param_names_into(collector);
                collect_forall_free_param_names_in_exist_body_facts(&x.facts, collector);
            }
            Obj::FnSet(x) => collect_forall_free_param_names_in_fn_set_body(&x.body, collector),
            Obj::AnonymousFn(x) => {
                collect_forall_free_param_names_in_fn_set_body(&x.body, collector);
                x.equal_to.collect_free_param_names_into(collector);
            }
            Obj::Cart(x) => collect_forall_free_param_names_in_boxed_objs(&x.args, collector),
            Obj::CartDim(x) => x.set.collect_free_param_names_into(collector),
            Obj::Proj(x) => collect_forall_free_param_names_in_pair(&x.set, &x.dim, collector),
            Obj::TupleDim(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Tuple(x) => collect_forall_free_param_names_in_boxed_objs(&x.args, collector),
            Obj::FiniteSetSize(x) => x.set.collect_free_param_names_into(collector),
            Obj::FnRange(x) => x.function.collect_free_param_names_into(collector),
            Obj::Replacement(x) => x.source_set.collect_free_param_names_into(collector),
            Obj::Sum(x) => {
                x.start.collect_free_param_names_into(collector);
                x.end.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::SumOfFiniteSet(x) => {
                x.set.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::Product(x) => {
                x.start.collect_free_param_names_into(collector);
                x.end.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::ProductOfFiniteSet(x) => {
                x.set.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::Range(x) => collect_forall_free_param_names_in_pair(&x.start, &x.end, collector),
            Obj::ClosedRange(x) => {
                collect_forall_free_param_names_in_pair(&x.start, &x.end, collector);
            }
            Obj::FiniteSeqSet(x) => {
                collect_forall_free_param_names_in_pair(&x.set, &x.n, collector);
            }
            Obj::SeqSet(x) => x.set.collect_free_param_names_into(collector),
            Obj::FiniteSeqListObj(x) => {
                collect_forall_free_param_names_in_boxed_objs(&x.objs, collector);
            }
            Obj::ObjAtIndex(x) => {
                collect_forall_free_param_names_in_pair(&x.obj, &x.index, collector);
            }
            Obj::MatrixSet(x) => {
                x.set.collect_free_param_names_into(collector);
                x.row_len.collect_free_param_names_into(collector);
                x.col_len.collect_free_param_names_into(collector);
            }
            Obj::MatrixListObj(x) => {
                for row in &x.rows {
                    collect_forall_free_param_names_in_boxed_objs(row, collector);
                }
            }
            Obj::MatrixAdd(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::MatrixSub(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::MatrixMul(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::MatrixScalarMul(x) => {
                collect_forall_free_param_names_in_pair(&x.scalar, &x.matrix, collector);
            }
            Obj::MatrixPow(x) => {
                collect_forall_free_param_names_in_pair(&x.base, &x.exponent, collector);
            }
            Obj::StructObj(x) => collect_forall_free_param_names_in_objs(&x.params, collector),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                collect_forall_free_param_names_in_objs(&x.struct_obj.params, collector);
                x.obj.collect_free_param_names_into(collector);
            }
            Obj::InstantiatedTemplateObj(x) => {
                collect_forall_free_param_names_in_objs(&x.args, collector);
            }
            Obj::OneSideInfinityIntervalObj(x) => {
                x.start().collect_free_param_names_into(collector);
            }
            Obj::IntervalObj(x) => {
                collect_forall_free_param_names_in_pair(x.start(), x.end(), collector);
            }
        }
    }
}

struct FreeParamNameCollector {
    kind: ParamObjType,
    names: HashSet<String>,
    include_binder_headers: bool,
}

impl FreeParamNameCollector {
    fn new(kind: ParamObjType, include_binder_headers: bool) -> Self {
        FreeParamNameCollector {
            kind,
            names: HashSet::new(),
            include_binder_headers,
        }
    }

    fn insert(&mut self, kind: ParamObjType, name: &str) {
        if self.kind == kind {
            self.names.insert(name.to_string());
        }
    }

    fn insert_binder(&mut self, kind: ParamObjType, name: &str) {
        if self.include_binder_headers {
            self.insert(kind, name);
        }
    }

    fn collect_atom(&mut self, atom: &AtomObj) {
        match atom {
            AtomObj::Identifier(param) => self.insert(ParamObjType::Identifier, &param.name),
            AtomObj::IdentifierWithMod(_) => {}
            AtomObj::Forall(param) => self.insert(ParamObjType::Forall, &param.name),
            AtomObj::Def(param) => self.insert(ParamObjType::DefHeader, &param.name),
            AtomObj::Exist(param) => self.insert(ParamObjType::Exist, &param.name),
            AtomObj::SetBuilder(param) => self.insert(ParamObjType::SetBuilder, &param.name),
            AtomObj::FnSet(param) => self.insert(ParamObjType::FnSet, &param.name),
            AtomObj::Induc(param) => self.insert(ParamObjType::Induc, &param.name),
            AtomObj::DefAlgo(param) => self.insert(ParamObjType::DefAlgo, &param.name),
            AtomObj::DefStructField(param) => {
                self.insert(ParamObjType::DefStructField, &param.name);
            }
            AtomObj::TupleIndex(param) => self.insert(ParamObjType::TupleIndex, &param.name),
            AtomObj::CartIndex(param) => self.insert(ParamObjType::CartIndex, &param.name),
        }
    }
}

fn collect_forall_free_param_names_in_pair(
    left: &Obj,
    right: &Obj,
    collector: &mut FreeParamNameCollector,
) {
    left.collect_free_param_names_into(collector);
    right.collect_free_param_names_into(collector);
}

fn collect_forall_free_param_names_in_objs(objs: &[Obj], collector: &mut FreeParamNameCollector) {
    for obj in objs {
        obj.collect_free_param_names_into(collector);
    }
}

fn collect_forall_free_param_names_in_boxed_objs(
    objs: &[Box<Obj>],
    collector: &mut FreeParamNameCollector,
) {
    for obj in objs {
        obj.collect_free_param_names_into(collector);
    }
}

fn collect_forall_free_param_names_in_obj_refs(
    objs: &[&Obj],
    collector: &mut FreeParamNameCollector,
) {
    for obj in objs {
        obj.collect_free_param_names_into(collector);
    }
}

fn collect_forall_free_param_names_in_fn_set_body(
    body: &FnSetBody,
    collector: &mut FreeParamNameCollector,
) {
    for group in body.params_def_with_set.iter() {
        for name in &group.params {
            collector.insert_binder(ParamObjType::FnSet, name);
        }
        group.param_type.collect_free_param_names_into(collector);
    }
    collect_forall_free_param_names_in_or_and_chain_facts(&body.dom_facts, collector);
    body.ret_set.collect_free_param_names_into(collector);
}

fn collect_forall_free_param_names_in_or_and_chain_facts(
    facts: &[OrAndChainAtomicFact],
    collector: &mut FreeParamNameCollector,
) {
    for fact in facts {
        collect_forall_free_param_names_in_obj_refs(&fact.get_args_from_fact_ref(), collector);
    }
}

fn collect_forall_free_param_names_in_exist_body_facts(
    facts: &[ExistBodyFact],
    collector: &mut FreeParamNameCollector,
) {
    for fact in facts {
        match fact {
            ExistBodyFact::AtomicFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            ExistBodyFact::AndFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            ExistBodyFact::ChainFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            ExistBodyFact::OrFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            ExistBodyFact::InlineForall(fact) => {
                collect_forall_free_param_names_in_forall_fact(fact, collector);
            }
        }
    }
}

fn collect_forall_free_param_names_in_fact(fact: &Fact, collector: &mut FreeParamNameCollector) {
    match fact {
        Fact::AtomicFact(fact) => {
            collect_forall_free_param_names_in_obj_refs(&fact.get_args_from_fact_ref(), collector)
        }
        Fact::ExistFact(fact) => {
            collect_forall_free_param_names_in_param_def(
                fact.params_def_with_type(),
                ParamObjType::Exist,
                collector,
            );
            collect_forall_free_param_names_in_exist_body_facts(fact.facts(), collector);
        }
        Fact::OrFact(fact) => {
            collect_forall_free_param_names_in_obj_refs(&fact.get_args_from_fact_ref(), collector)
        }
        Fact::AndFact(fact) => {
            collect_forall_free_param_names_in_obj_refs(&fact.get_args_from_fact_ref(), collector)
        }
        Fact::ChainFact(fact) => {
            collect_forall_free_param_names_in_obj_refs(&fact.get_args_from_fact_ref(), collector)
        }
        Fact::ForallFact(fact) => {
            collect_forall_free_param_names_in_forall_fact(fact, collector);
        }
        Fact::ForallFactWithIff(fact) => {
            collect_forall_free_param_names_in_forall_fact(&fact.forall_fact, collector);
            collect_forall_free_param_names_in_exist_or_and_chain_facts(&fact.iff_facts, collector);
        }
        Fact::NotForall(fact) => {
            collect_forall_free_param_names_in_forall_fact(&fact.forall_fact, collector);
        }
    }
}

fn collect_forall_free_param_names_in_forall_fact(
    fact: &ForallFact,
    collector: &mut FreeParamNameCollector,
) {
    collect_forall_free_param_names_in_param_def(
        &fact.params_def_with_type,
        ParamObjType::Forall,
        collector,
    );
    for dom_fact in &fact.dom_facts {
        collect_forall_free_param_names_in_fact(dom_fact, collector);
    }
    collect_forall_free_param_names_in_exist_or_and_chain_facts(&fact.then_facts, collector);
}

fn collect_forall_free_param_names_in_exist_or_and_chain_facts(
    facts: &[ExistOrAndChainAtomicFact],
    collector: &mut FreeParamNameCollector,
) {
    for fact in facts {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(fact) => {
                collect_forall_free_param_names_in_obj_refs(
                    &fact.get_args_from_fact_ref(),
                    collector,
                );
            }
            ExistOrAndChainAtomicFact::AndFact(fact) => {
                collect_forall_free_param_names_in_obj_refs(
                    &fact.get_args_from_fact_ref(),
                    collector,
                );
            }
            ExistOrAndChainAtomicFact::ChainFact(fact) => {
                collect_forall_free_param_names_in_obj_refs(
                    &fact.get_args_from_fact_ref(),
                    collector,
                );
            }
            ExistOrAndChainAtomicFact::OrFact(fact) => {
                collect_forall_free_param_names_in_obj_refs(
                    &fact.get_args_from_fact_ref(),
                    collector,
                );
            }
            ExistOrAndChainAtomicFact::ExistFact(fact) => {
                collect_forall_free_param_names_in_param_def(
                    fact.params_def_with_type(),
                    ParamObjType::Exist,
                    collector,
                );
                collect_forall_free_param_names_in_exist_body_facts(fact.facts(), collector);
            }
        }
    }
}

fn collect_forall_free_param_names_in_param_def(
    params: &ParamDefWithType,
    binding_kind: ParamObjType,
    collector: &mut FreeParamNameCollector,
) {
    for group in &params.groups {
        for name in &group.params {
            collector.insert_binder(binding_kind, name);
        }
        if let ParamType::Obj(obj) = &group.param_type {
            obj.collect_free_param_names_into(collector);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_forall_names_through_nested_object_fact_shapes() {
        let nested_exist = ExistFactEnum::ExistFact(
            ExistFactBody::new(
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec!["exist_bound".to_string()],
                    ParamType::Set(Set::new()),
                )]),
                vec![
                    exist_equality("exist_bound").into(),
                    exist_equality("exist_free").into(),
                ],
                default_line_file(),
            )
            .unwrap(),
        );
        let iff_forall = ForallFact::new(
            ParamDefWithType::new(vec![]),
            vec![forall_equality("iff_dom").into()],
            vec![forall_equality("iff_then").into()],
            default_line_file(),
        )
        .unwrap();
        let iff = ForallFactWithIff::new(
            iff_forall,
            vec![forall_equality("iff_reverse").into()],
            default_line_file(),
        )
        .unwrap();
        let negated_forall = ForallFact::new(
            ParamDefWithType::new(vec![]),
            vec![],
            vec![forall_equality("not_forall").into()],
            default_line_file(),
        )
        .unwrap();
        let inline_forall = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec!["bound".to_string()],
                ParamType::Obj(forall_obj("param_type")),
            )]),
            vec![
                iff.into(),
                NotForallFact::new(negated_forall).into(),
                nested_exist.into(),
            ],
            vec![
                forall_equality("bound").into(),
                forall_equality("inline_free").into(),
            ],
            default_line_file(),
        )
        .unwrap();
        let object: Obj = SetBuilder::new(
            "element".to_string(),
            forall_obj("source"),
            vec![ExistBodyFact::InlineForall(inline_forall)],
        )
        .unwrap()
        .into();

        let expected = HashSet::from([
            "source".to_string(),
            "param_type".to_string(),
            "bound".to_string(),
            "iff_dom".to_string(),
            "iff_then".to_string(),
            "iff_reverse".to_string(),
            "not_forall".to_string(),
            "inline_free".to_string(),
        ]);

        assert_eq!(object.collect_forall_free_param_names(), expected);
        assert_eq!(
            object.collect_param_obj_names(ParamObjType::Exist),
            HashSet::from(["exist_bound".to_string(), "exist_free".to_string()])
        );
        assert_eq!(
            object.collect_param_obj_names(ParamObjType::SetBuilder),
            HashSet::from(["element".to_string()])
        );
        assert!(object.contains_forall_free_param_obj());
    }

    #[test]
    fn collects_forall_name_from_function_head() {
        let object: Obj = FnObj::new(
            ForallFreeParamObj::new("function".to_string()).into(),
            vec![vec![Box::new(forall_obj("argument"))]],
        )
        .into();

        assert_eq!(
            object.collect_forall_free_param_names(),
            HashSet::from(["function".to_string(), "argument".to_string()])
        );
    }

    #[test]
    fn separates_set_builder_and_fn_set_function_head_names() {
        let set_builder_head: Obj = FnObj::new(
            SetBuilderFreeParamObj::new("builder_head".to_string()).into(),
            vec![vec![Box::new(
                FnSetFreeParamObj::new("fn_argument".to_string()).into(),
            )]],
        )
        .into();
        let fn_set_head: Obj = FnObj::new(
            FnSetFreeParamObj::new("fn_head".to_string()).into(),
            vec![vec![Box::new(
                SetBuilderFreeParamObj::new("builder_argument".to_string()).into(),
            )]],
        )
        .into();
        let object: Obj = ListSet::new(vec![set_builder_head, fn_set_head]).into();

        assert_eq!(
            object.collect_param_obj_names(ParamObjType::SetBuilder),
            HashSet::from(["builder_head".to_string(), "builder_argument".to_string()])
        );
        assert_eq!(
            object.collect_param_obj_names(ParamObjType::FnSet),
            HashSet::from(["fn_head".to_string(), "fn_argument".to_string()])
        );
    }

    #[test]
    fn collects_fn_set_and_anonymous_function_binder_headers() {
        let fn_set: Obj = FnSet::new(
            vec![ParamGroupWithSet::new(
                vec!["fn_bound".to_string()],
                StandardSet::R.into(),
            )],
            vec![],
            StandardSet::R.into(),
        )
        .unwrap()
        .into();
        let anonymous_fn: Obj = AnonymousFn::new(
            vec![ParamGroupWithSet::new(
                vec!["anonymous_bound".to_string()],
                StandardSet::R.into(),
            )],
            vec![],
            StandardSet::R.into(),
            Number::new("0".to_string()).into(),
        )
        .unwrap()
        .into();
        let object: Obj = ListSet::new(vec![fn_set, anonymous_fn]).into();

        assert_eq!(
            object.collect_param_obj_names(ParamObjType::FnSet),
            HashSet::from(["fn_bound".to_string(), "anonymous_bound".to_string()])
        );
    }

    #[test]
    fn contains_forall_param_checks_occurrences_not_only_binder_headers() {
        let inline_forall = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec!["bound".to_string()],
                ParamType::Set(Set::new()),
            )]),
            vec![],
            vec![],
            default_line_file(),
        )
        .unwrap();
        let object: Obj = SetBuilder::new(
            "element".to_string(),
            StandardSet::R.into(),
            vec![ExistBodyFact::InlineForall(inline_forall)],
        )
        .unwrap()
        .into();

        assert_eq!(
            object.collect_forall_free_param_names(),
            HashSet::from(["bound".to_string()])
        );
        assert!(!object.contains_forall_free_param_obj());
    }

    fn forall_obj(name: &str) -> Obj {
        ForallFreeParamObj::new(name.to_string()).into()
    }

    fn forall_equality(name: &str) -> AtomicFact {
        EqualFact::new(
            forall_obj(name),
            Number::new("0".to_string()).into(),
            default_line_file(),
        )
        .into()
    }

    fn exist_equality(name: &str) -> AtomicFact {
        EqualFact::new(
            ExistFreeParamObj::new(name.to_string()).into(),
            Number::new("0".to_string()).into(),
            default_line_file(),
        )
        .into()
    }
}
