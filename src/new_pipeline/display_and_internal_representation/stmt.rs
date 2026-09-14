//! Stmt and statement variants: internal representation + display_string.

use super::types::StmtInternalRepresentation;
use crate::new_pipeline::ast::fact::ExistFact;
use crate::new_pipeline::ast::stmt::*;
use crate::new_pipeline::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            self.internal_representation().display_string()
        }
    };
}

macro_rules! indent {
    ($text:expr, $n:expr) => {{
        let __prefix = "    ".repeat($n);
        ($text)
            .split('\n')
            .map(|line| format!("{}{}", __prefix, line))
            .collect::<Vec<_>>()
            .join(
                "
",
            )
    }};
}

impl Stmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            Stmt::Fact(x) => StmtInternalRepresentation(x.internal_representation().0),
            Stmt::UnsafeStmt(x) => x.internal_representation(),
            Stmt::Definition(x) => x.internal_representation(),
            Stmt::ReleaseThmStmt(x) => x.internal_representation(),
            Stmt::By(x) => x.internal_representation(),
            Stmt::Witness(x) => x.internal_representation(),
            Stmt::ProofBlock(x) => x.internal_representation(),
            Stmt::Command(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl UnsafeStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            UnsafeStmt::TrustStmt(x) => x.internal_representation(),
            UnsafeStmt::TrustHaveStmt(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl DefinitionStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            DefinitionStmt::LetObjStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveObjInNonemptySetStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveObjEqualStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveObjByExistFactsStmt(x) => x.internal_representation(),
            DefinitionStmt::ObtainObjFromExistFact(x) => x.internal_representation(),
            DefinitionStmt::ObtainObjFromAtomicFact(x) => x.internal_representation(),
            DefinitionStmt::ObtainObjFromThm(x) => x.internal_representation(),
            DefinitionStmt::HaveByPreimageStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveFnEqualStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveFnByInducStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveFnByForallExistUniqueStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveTupleStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveCartStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveSeqStmt(x) => x.internal_representation(),
            DefinitionStmt::HaveFiniteSeqStmt(x) => x.internal_representation(),
            DefinitionStmt::DefPropStmt(x) => x.internal_representation(),
            DefinitionStmt::DefAbstractPropStmt(x) => x.internal_representation(),
            DefinitionStmt::DefSettingStmt(x) => x.internal_representation(),
            DefinitionStmt::DefTemplateStmt(x) => x.internal_representation(),
            DefinitionStmt::DefStructStmt(x) => x.internal_representation(),
            DefinitionStmt::DefAlgoStmt(x) => x.internal_representation(),
            DefinitionStmt::DefThmStmt(x) => x.internal_representation(),
            DefinitionStmt::AxiomStmt(x) => x.internal_representation(),
            DefinitionStmt::DefStrategyStmt(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl ByStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            ByStmt::ByCasesStmt(x) => x.internal_representation(),
            ByStmt::ByContraStmt(x) => x.internal_representation(),
            ByStmt::ByEnumerateFiniteSetStmt(x) => x.internal_representation(),
            ByStmt::ByFiniteSetInducStmt(x) => x.internal_representation(),
            ByStmt::ByInducStmt(x) => x.internal_representation(),
            ByStmt::ByForStmt(x) => x.internal_representation(),
            ByStmt::ByExtensionStmt(x) => x.internal_representation(),
            ByStmt::ByEnumerateRangeStmt(x) => x.internal_representation(),
            ByStmt::ByClosedRangeAsCasesStmt(x) => x.internal_representation(),
            ByStmt::ByTransitivePropStmt(x) => x.internal_representation(),
            ByStmt::BySymmetricPropStmt(x) => x.internal_representation(),
            ByStmt::ByReflexivePropStmt(x) => x.internal_representation(),
            ByStmt::ByAntisymmetricPropStmt(x) => x.internal_representation(),
            ByStmt::ByZornLemmaStmt(x) => x.internal_representation(),
            ByStmt::ByAxiomOfChoiceStmt(x) => x.internal_representation(),
            ByStmt::ByRegularityAxiomStmt(x) => x.internal_representation(),
            ByStmt::ByDefStmt(x) => x.internal_representation(),
            ByStmt::ByStructDefStmt(x) => x.internal_representation(),
            ByStmt::ByThmStmt(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl WitnessStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            WitnessStmt::WitnessExistFact(x) => x.internal_representation(),
            WitnessStmt::WitnessAtomicFact(x) => x.internal_representation(),
            WitnessStmt::WitnessNonemptySet(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl ProofBlockStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            ProofBlockStmt::ClaimStmt(x) => x.internal_representation(),
            ProofBlockStmt::ExampleStmt(x) => x.internal_representation(),
            ProofBlockStmt::SketchStmt(x) => x.internal_representation(),
            ProofBlockStmt::TryStmt(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl CommandStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            CommandStmt::EvalStmt(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl TheoremCall {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = format!("{}", self.name.internal_representation());
        if let TheoremCallArguments::Parenthesized(args) = &self.arguments {
            let parts: Vec<_> = args.iter().map(|a| a.internal_representation()).collect();
            out.push_str(LEFT_PAREN);
            out.push_str(&parts.join(", "));
            out.push_str(RIGHT_PAREN);
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl EvalStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!("{} {}", EVAL, &self.obj_to_eval.internal_representation()))
    }
    impl_display_pair!();
}

impl LetObjStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} #{}#{} {} {}",
            LET,
            self.identifier_id.value(),
            self.name,
            EQUAL,
            &self.value.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!("{} {}", HAVE, self.param_def.internal_representation()))
    }
    impl_display_pair!();
}

impl HaveObjEqualStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let objs: Vec<_> = self
            .objs_equal_to
            .iter()
            .map(|o| o.internal_representation())
            .collect();
        out.push_str(&format!(
            "{} {} {} {}",
            HAVE,
            self.param_def.internal_representation(),
            EQUAL,
            objs.join(", ")
        ));

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveObjByExistFactsStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let facts: Vec<_> = self
            .facts
            .iter()
            .map(|fact| fact.internal_representation())
            .collect();
        out.push_str(&format!(
            "{} {}{}\n{}",
            HAVE,
            self.param_def.internal_representation(),
            COLON,
            indent!(
                &facts.join(
                    "
"
                ),
                1
            )
        ));

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl TrustHaveStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let param_str = self.param_def.internal_representation();
        if self.facts.is_empty() {
            out.push_str(&format!("{} {} {}", TRUST, HAVE, param_str));
        } else {
            out.push_str(&format!(
                "{} {}{}{}\n{}",
                TRUST,
                HAVE,
                param_str,
                COLON,
                indent!(
                    &self
                        .facts
                        .iter()
                        .map(|f| f.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl TrustStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        if self.facts.len() == 1 {
            out.push_str(&format!(
                "{} {}",
                TRUST,
                &self.facts[0].internal_representation()
            ));
        } else {
            out.push_str(&format!(
                "{}{}\n{}",
                TRUST,
                COLON,
                indent!(
                    &self
                        .facts
                        .iter()
                        .map(|f| f.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ObtainObjFromExistFact {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {}",
            OBTAIN,
            self.equal_tos.join(", "),
            FROM,
            self.fact.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl ObtainObjFromAtomicFact {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {}",
            OBTAIN,
            self.equal_tos.join(", "),
            FROM,
            self.fact.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl ObtainObjFromThm {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {}",
            OBTAIN,
            self.equal_tos.join(", "),
            FROM,
            THM,
            self.call.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl HaveByPreimageStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {} {}",
            HAVE,
            BY,
            PREIMAGE,
            self.preimage_names.join(", "),
            FROM,
            self.range_membership.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl FnSetClause {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let params: Vec<_> = self
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.internal_representation())
            .collect();
        let dom: Vec<_> = self
            .dom_facts
            .iter()
            .map(|d| d.internal_representation())
            .collect();
        let mut out = format!("{} ", FN);
        out.push_str(LEFT_PAREN);
        if !params.is_empty() && !dom.is_empty() {
            out.push_str(&params.join(", "));
            out.push_str(&format!("{} ", COLON));
            out.push_str(&dom.join(", "));
        } else if dom.is_empty() {
            out.push_str(&params.join(", "));
        } else if params.is_empty() {
            out.push_str(COLON);
            out.push_str(&dom.join(", "));
        }
        out.push_str(RIGHT_PAREN);
        out.push(' ');
        out.push_str(&self.ret_set.internal_representation());
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveFnEqualStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let body = &self.equal_to_anonymous_fn.body;
        let params: Vec<_> = body
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.internal_representation())
            .collect();
        let dom: Vec<_> = body
            .dom_facts
            .iter()
            .map(|d| d.internal_representation())
            .collect();
        let mut out = format!("{} {} {}", HAVE, FN, self.name);
        out.push_str(LEFT_PAREN);
        if !params.is_empty() && !dom.is_empty() {
            out.push_str(&params.join(", "));
            out.push_str(&format!("{} ", COLON));
            out.push_str(&dom.join(", "));
        } else if dom.is_empty() {
            out.push_str(&params.join(", "));
        } else if params.is_empty() {
            out.push_str(COLON);
            out.push_str(&dom.join(", "));
        }
        out.push_str(RIGHT_PAREN);
        out.push_str(&format!(
            " {} {}",
            EQUAL,
            self.equal_to_anonymous_fn
                .equal_to
                .as_ref()
                .internal_representation()
        ));
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let params: Vec<_> = self
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.internal_representation())
            .collect();
        let dom: Vec<_> = self
            .fn_set_clause
            .dom_facts
            .iter()
            .map(|d| d.internal_representation())
            .collect();
        let mut out = format!("{} {} {}", HAVE, FN, self.name);
        out.push_str(LEFT_PAREN);
        if !params.is_empty() && !dom.is_empty() {
            out.push_str(&params.join(", "));
            out.push_str(&format!("{} ", COLON));
            out.push_str(&dom.join(", "));
        } else if dom.is_empty() {
            out.push_str(&params.join(", "));
        } else if params.is_empty() {
            out.push_str(COLON);
            out.push_str(&dom.join(", "));
        }
        out.push_str(RIGHT_PAREN);
        out.push_str(&format!(
            " {} {} {} {}
",
            self.fn_set_clause.ret_set.internal_representation(),
            BY,
            CASES,
            COLON
        ));
        for (i, case) in self.cases.iter().enumerate() {
            let line = format!(
                "{} {}{} {}",
                CASE,
                case.internal_representation(),
                COLON,
                self.equal_tos[i].internal_representation()
            );
            out.push_str(&indent!(&line, 1));
            if i + 1 < self.cases.len() {
                out.push_str("\n");
            }
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveFnByInducCase {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}",
            CASE,
            &self.case_fact.internal_representation(),
            COLON
        ));
        match &self.body {
            HaveFnByInducCaseBody::EqualTo(obj) => {
                out.push_str(&format!(" {}", obj.internal_representation()));
            }
            HaveFnByInducCaseBody::NestedCases(cases) => {
                out.push_str(&format!("\n"));
                for (i, c) in cases.iter().enumerate() {
                    out.push_str(&format!("{}", indent!(&c.internal_representation(), 1)));
                    if i + 1 < cases.len() {
                        out.push_str(&format!("\n"));
                    }
                }
            }
        }

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveFnByInducStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let params: Vec<_> = self
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.internal_representation())
            .collect();
        let dom: Vec<_> = self
            .fn_set_clause
            .dom_facts
            .iter()
            .map(|d| d.internal_representation())
            .collect();
        let mut out = format!("{} {} {}", HAVE, FN, self.name);
        out.push_str(LEFT_PAREN);
        if !params.is_empty() && !dom.is_empty() {
            out.push_str(&params.join(", "));
            out.push_str(&format!("{} ", COLON));
            out.push_str(&dom.join(", "));
        } else if dom.is_empty() {
            out.push_str(&params.join(", "));
        } else if params.is_empty() {
            out.push_str(COLON);
            out.push_str(&dom.join(", "));
        }
        out.push_str(RIGHT_PAREN);
        out.push_str(&format!(
            " {} {} {} {} {} {}",
            self.fn_set_clause.ret_set.internal_representation(),
            BY,
            INDUC,
            self.measure.internal_representation(),
            FROM,
            self.lower_bound.internal_representation()
        ));
        out.push_str(COLON);
        for case in self.cases.iter() {
            out.push_str("\n");
            out.push_str(&indent!(&case.internal_representation(), 1));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveFnByForallExistUniqueStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {} {} {} {}{}\n{}",
            HAVE,
            FN,
            self.name,
            AS,
            SET,
            COLON,
            indent!(
                &format!(
                    "{} {}",
                    QUESTION_GOAL,
                    self.forall.internal_representation()
                ),
                1
            )
        ));
        if !self.prove_process.is_empty() {
            out.push_str(&format!(
                "\n{}",
                indent!(
                    &self
                        .prove_process
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl HaveTupleStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {} {} {}, {}[{}] {} {}",
            HAVE,
            TUPLE,
            self.name,
            FOR,
            self.index_name,
            LESS_EQUAL,
            &self.dimension.internal_representation(),
            self.name,
            self.index_name,
            EQUAL,
            &self.value.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl HaveCartStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {} {} {}, {}[{}] {} {}",
            HAVE,
            CART,
            self.name,
            FOR,
            self.index_name,
            LESS_EQUAL,
            &self.dimension.internal_representation(),
            self.name,
            self.index_name,
            EQUAL,
            &self.value.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl HaveSeqStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {} {}, {}({}) {} {}",
            HAVE,
            SEQ,
            self.name,
            self.seq_set.internal_representation(),
            FOR,
            self.index_name,
            self.name,
            self.index_name,
            EQUAL,
            &self.value.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl HaveFiniteSeqStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {} {} {} {}, {}({}) {} {}",
            HAVE,
            FINITE_SEQ,
            self.name,
            self.finite_seq_set.internal_representation(),
            FOR,
            self.index_name,
            LESS_EQUAL,
            &self.bound.internal_representation(),
            self.name,
            self.index_name,
            EQUAL,
            &self.value.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl DefPropStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!("{} {}{}", PROP, self.name, LEFT_PAREN));
        out.push_str(&format!(
            "{}{}",
            self.typed_parameters.internal_representation(),
            RIGHT_PAREN
        ));
        if !self.iff_facts.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .iff_facts
                        .iter()
                        .map(|f| f.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl DefAbstractPropStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let params: Vec<_> = self
            .params
            .iter()
            .map(|p| p.internal_representation())
            .collect();
        out.push_str(&format!("{} {}{}", ABSTRACT_PROP, self.name, LEFT_PAREN));
        out.push_str(&format!("{}{}", params.join(", "), RIGHT_PAREN));

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl DefSettingStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}{}{}",
            SETTING,
            self.name,
            LEFT_PAREN,
            self.param_def.internal_representation(),
            RIGHT_PAREN
        ));
        if !self.dom_facts.is_empty() {
            out.push_str(&format!("{}", COLON));
            for fact in self.dom_facts.iter() {
                out.push_str(&format!("\n    {}", fact.internal_representation()));
            }
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl TemplateDefEnum {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            TemplateDefEnum::HaveObjInNonemptySetStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveObjEqualStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveObjByExistFactsStmt(x) => x.internal_representation(),
            TemplateDefEnum::TrustHaveStmt(x) => x.internal_representation(),
            TemplateDefEnum::ObtainObjFromExistFact(x) => x.internal_representation(),
            TemplateDefEnum::ObtainObjFromAtomicFact(x) => x.internal_representation(),
            TemplateDefEnum::ObtainObjFromThm(x) => x.internal_representation(),
            TemplateDefEnum::HaveFnEqualStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveFnByInducStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveTupleStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveCartStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveSeqStmt(x) => x.internal_representation(),
            TemplateDefEnum::HaveFiniteSeqStmt(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl DefTemplateStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = format!(
            "{}{}{}",
            TEMPLATE,
            LESS,
            self.template_arg_def.internal_representation()
        );
        if !self.template_arg_dom.is_empty() {
            let dom: Vec<_> = self
                .template_arg_dom
                .iter()
                .map(|d| d.internal_representation())
                .collect();
            out.push_str(&format!("{} {}", COLON, dom.join(", ")));
        }
        out.push_str(&format!(
            "{}{}
{}",
            GREATER,
            COLON,
            indent!(&self.template_def_stmt.internal_representation(), 1)
        ));
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl StructFieldDef {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {}",
            self.binding,
            &self.field_type.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl DefStructStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match &self.param_def_with_dom {
            Some((param_def, _)) => {
                StmtInternalRepresentation(format!(
                    "{} {}{}{}{}{}",
                    STRUCT,
                    self.name,
                    LESS,
                    param_def.internal_representation(),
                    GREATER,
                    COLON
                ))
            }
            None => StmtInternalRepresentation(format!(
                "{} {}{}",
                STRUCT, self.name, COLON
            )),
        }
    }
    impl_display_pair!();
}

impl AlgoReturn {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(self.value.internal_representation().0)
    }
    impl_display_pair!();
}

impl AlgoCase {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {}{} {}",
            CASE,
            self.condition.internal_representation(),
            COLON,
            indent!(&self.return_stmt.internal_representation(), 1)
        ))
    }
    impl_display_pair!();
}

impl AlgoReturnOrAlgoCase {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            AlgoReturnOrAlgoCase::AlgoReturn(x) => x.internal_representation(),
            AlgoReturnOrAlgoCase::AlgoCase(x) => x.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl DefAlgoStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut body: Vec<_> = self
            .cases
            .iter()
            .map(|c| c.internal_representation())
            .collect();
        if let Some(default_return) = &self.default_return {
            body.push(default_return.internal_representation());
        }
        let mut out = format!("{} {} {} {}", HAVE, ALGO, FOR, self.name);
        out.push_str(LEFT_PAREN);
        out.push_str(&self.param_bindings.join(", "));
        out.push_str(RIGHT_PAREN);
        out.push_str(&format!(
            "{}
{}",
            COLON,
            indent!(
                &body.join(
                    "
"
                ),
                1
            )
        ));
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl DefThmStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}\n{}",
            THM,
            self.name,
            COLON,
            indent!(
                &format!("{} {}", QUESTION_GOAL, &self.fact.internal_representation()),
                1
            )
        ));
        if !self.prove_process.is_empty() {
            out.push_str(&format!(
                "\n{}",
                indent!(
                    &self
                        .prove_process
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl AxiomStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {}{}\n{}",
            AXIOM,
            self.name,
            COLON,
            indent!(
                &format!(
                    "{} {}",
                    QUESTION_GOAL,
                    self.forall_fact.internal_representation()
                ),
                1
            )
        ))
    }
    impl_display_pair!();
}

impl DefStrategyStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}\n{}",
            STRATEGY,
            self.name,
            COLON,
            indent!(
                &format!(
                    "{} {}",
                    QUESTION_GOAL,
                    self.forall_fact.internal_representation()
                ),
                1
            )
        ));
        if !self.prove_process.is_empty() {
            out.push_str(&format!(
                "\n{}",
                indent!(
                    &self
                        .prove_process
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ClaimStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{}{}\n{}\n{}",
            CLAIM,
            COLON,
            indent!(
                &format!("{} {}", QUESTION_GOAL, &self.fact.internal_representation()),
                1
            ),
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            )
        ))
    }
    impl_display_pair!();
}

impl ExampleStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{}{}\n{}\n{}",
            EXAMPLE,
            COLON,
            indent!(
                &format!("{} {}", QUESTION_GOAL, &self.fact.internal_representation()),
                1
            ),
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            )
        ))
    }
    impl_display_pair!();
}

impl SketchStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{}{}\n{}",
            SKETCH,
            COLON,
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            )
        ))
    }
    impl_display_pair!();
}

impl TryStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{}{}\n{}",
            TRY,
            COLON,
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            )
        ))
    }
    impl_display_pair!();
}

impl ReleaseThmStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {}",
            RELEASE,
            THM,
            self.call.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl WitnessExistFact {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let equal_tos: Vec<_> = self
            .equal_tos
            .iter()
            .map(|o| o.internal_representation())
            .collect();
        let spec = match &self.exist_fact_in_witness {
            ExistFact::PlainExistFact(b)
            | ExistFact::ExistUniqueFact(b)
            | ExistFact::NotExistFact(b) => b,
        };
        let facts: Vec<_> = spec
            .facts
            .iter()
            .map(|fact| fact.internal_representation())
            .collect();
        out.push_str(&format!(
            "{} {}{} {} {} {}",
            WITNESS,
            equal_tos.join(", "),
            COLON,
            spec.typed_parameters.internal_representation(),
            ST,
            facts.join(", ")
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl WitnessAtomicFact {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let witnesses: Vec<_> = self
            .witnesses
            .iter()
            .map(|o| o.internal_representation())
            .collect();
        out.push_str(&format!(
            "{} {} {} {}",
            WITNESS,
            self.atomic_fact.internal_representation(),
            FROM,
            witnesses.join(", ")
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl WitnessNonemptySet {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {} {}",
            WITNESS,
            &self.obj.internal_representation(),
            &self.set.internal_representation()
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByCasesStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let question_goals: Vec<_> = self
            .then_facts
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact.internal_representation()))
            .collect();
        let mut case_blocks = Vec::new();
        for ((case, proof), impossible_fact) in self
            .cases
            .iter()
            .zip(self.proofs.iter())
            .zip(self.impossible_facts.iter())
        {
            if let Some(impossible_fact) = impossible_fact {
                let case_header = format!(
                    "{} {}{}",
                    indent!(CASE, 1),
                    case.internal_representation(),
                    COLON
                );
                let impossible_line = format!(
                    "{} {}",
                    indent!(IMPOSSIBLE, 2),
                    impossible_fact.internal_representation()
                );
                if proof.is_empty() {
                    case_blocks.push(format!("{}\n{}", case_header, impossible_line));
                } else {
                    case_blocks.push(format!(
                        "{}\n{}\n{}",
                        case_header,
                        indent!(
                            &proof
                                .iter()
                                .map(|s| s.internal_representation())
                                .collect::<Vec<_>>()
                                .join(
                                    "
"
                                ),
                            2
                        ),
                        impossible_line
                    ));
                }
            } else if proof.is_empty() {
                case_blocks.push(format!(
                    "{} {}",
                    indent!(CASE, 1),
                    case.internal_representation()
                ));
            } else {
                case_blocks.push(format!(
                    "{} {}{}\n{}",
                    indent!(CASE, 1),
                    case.internal_representation(),
                    COLON,
                    indent!(
                        &proof
                            .iter()
                            .map(|s| s.internal_representation())
                            .collect::<Vec<_>>()
                            .join(
                                "
"
                            ),
                        2
                    )
                ));
            }
        }
        out.push_str(&format!(
            "{} {}{}\n{}\n{}",
            BY,
            CASES,
            COLON,
            indent!(
                &question_goals.join(
                    "
"
                ),
                1
            ),
            case_blocks.join(
                "
"
            )
        ));

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByContraStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = format!(
            "{} {}{}
{}",
            BY,
            CONTRA,
            COLON,
            indent!(
                &format!(
                    "{} {}",
                    QUESTION_GOAL,
                    self.to_prove.internal_representation()
                ),
                1
            )
        );
        if !self.proof.is_empty() {
            out.push_str("\n");
            out.push_str(&indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            ));
        }
        out.push_str("\n");
        out.push_str(&format!(
            "{} {}",
            indent!(IMPOSSIBLE, 1),
            self.impossible_fact.internal_representation()
        ));
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

macro_rules! impl_by_prop {
    ($ty:ty, $prop:expr) => {
        impl $ty {
            pub fn internal_representation(&self) -> StmtInternalRepresentation {
                let mut out = format!(
                    "{} {}:
{}",
                    BY,
                    $prop,
                    indent!(
                        &format!(
                            "{} {}",
                            QUESTION_GOAL,
                            self.forall_fact.internal_representation()
                        ),
                        1
                    )
                );
                if !self.proof.is_empty() {
                    out.push_str("\n");
                    out.push_str(&indent!(
                        &self
                            .proof
                            .iter()
                            .map(|s| s.internal_representation())
                            .collect::<Vec<_>>()
                            .join(
                                "
"
                            ),
                        1
                    ));
                }
                StmtInternalRepresentation(out)
            }
            impl_display_pair!();
        }
    };
}

impl_by_prop!(ByTransitivePropStmt, TRANSITIVE_PROP);
impl_by_prop!(BySymmetricPropStmt, SYMMETRIC_PROP);
impl_by_prop!(ByReflexivePropStmt, REFLEXIVE_PROP);
impl_by_prop!(ByAntisymmetricPropStmt, ANTISYMMETRIC_PROP);
impl_by_prop!(ByForStmt, FOR);

impl ByEnumerateFiniteSetStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {} {}:\n{}",
            BY,
            ENUMERATE,
            FINITE_SET,
            indent!(
                &format!(
                    "{} {}",
                    QUESTION_GOAL,
                    self.forall_fact.internal_representation()
                ),
                1
            )
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "\n{}",
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByExtensionStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}\n{}",
            BY,
            EXTENSION,
            COLON,
            indent!(
                &format!(
                    "{} {} {} {}",
                    QUESTION_GOAL,
                    &self.left.internal_representation(),
                    EQUAL,
                    &self.right.internal_representation()
                ),
                1
            )
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "\n{}",
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ClosedRangeOrRange {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        match self {
            ClosedRangeOrRange::ClosedRange(x) => {
                StmtInternalRepresentation(x.internal_representation().0)
            }
            ClosedRangeOrRange::Range(x) => {
                StmtInternalRepresentation(x.internal_representation().0)
            }
        }
    }
    impl_display_pair!();
}

impl ByEnumerateRangeStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        let keyword = match &self.range {
            ClosedRangeOrRange::ClosedRange(_) => CLOSED_RANGE,
            ClosedRangeOrRange::Range(_) => RANGE,
        };
        out.push_str(&format!(
            "{} {} {}{} {} {}{} {}",
            BY,
            ENUMERATE,
            keyword,
            COLON,
            &self.element.internal_representation(),
            FACT_PREFIX,
            IN,
            self.range.internal_representation()
        ));

        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByClosedRangeAsCasesStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {}{} {} {}{} {}",
            BY,
            CLOSED_RANGE,
            AS,
            CASES,
            COLON,
            &self.element.internal_representation(),
            FACT_PREFIX,
            IN,
            self.closed_range.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl ByDefStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!("{} {} {}", BY, DEF, self.fact.internal_representation()))
    }
    impl_display_pair!();
}

impl ByStructDefStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {}",
            BY,
            STRUCT,
            DEF,
            &self.obj.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl ByThmStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {} {} {} {}",
            BY,
            THM,
            self.call.internal_representation(),
            RIGHT_ARROW,
            self.selected_fact.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl ByAxiomOfChoiceStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        if self.proof.is_empty() {
            return StmtInternalRepresentation(format!(
                "{} {}{} {} {}",
                BY,
                AXIOM_OF_CHOICE,
                COLON,
                SET,
                self.family.internal_representation()
            ));
        }
        let mut out = format!(
            "{} {}{} {} {}{}",
            BY,
            AXIOM_OF_CHOICE,
            COLON,
            SET,
            self.family.internal_representation(),
            COLON
        );
        out.push_str("\n");
        out.push_str(&indent!(
            &self
                .proof
                .iter()
                .map(|s| s.internal_representation())
                .collect::<Vec<_>>()
                .join(
                    "
"
                ),
            1
        ));
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByRegularityAxiomStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        StmtInternalRepresentation(format!(
            "{} {}({})",
            BY,
            REGULARITY_AXIOM,
            &self.set.internal_representation()
        ))
    }
    impl_display_pair!();
}

impl ByZornLemmaStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{} {} {}, {} {}, {} {}, {} {}",
            BY,
            ZORN_LEMMA,
            COLON,
            SET,
            &self.set.internal_representation(),
            PROP,
            self.prop_name.internal_representation(),
            PROP,
            self.upper_bound_prop_name.internal_representation(),
            PROP,
            self.maximal_prop_name.internal_representation()
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByInducStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let question_goals: Vec<_> = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact.internal_representation()))
            .collect();
        let keyword = if self.strong { STRONG_INDUC } else { INDUC };
        let has_structured = self.base_proof.is_some() || self.step_proof.is_some();
        if has_structured {
            let step_keyword = if self.strong { STRONG_INDUC } else { INDUC };
            let base_proof = match &self.base_proof {
                Some(proof) => indent!(
                    &proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    2
                ),
                None => String::new(),
            };
            let step_proof = match &self.step_proof {
                Some(proof) => indent!(
                    &proof
                        .iter()
                        .map(|s| s.internal_representation())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    2
                ),
                None => String::new(),
            };
            return StmtInternalRepresentation(format!(
                "{} {} {} {} {}{}
{}
{} {} {} {} {}{}
{}
{} {}{}
{}",
                BY,
                keyword,
                self.param_binding,
                FROM,
                self.induc_from.internal_representation(),
                COLON,
                indent!(
                    &question_goals.join(
                        "
"
                    ),
                    1
                ),
                indent!(QUESTION_GOAL, 1),
                FROM,
                self.param_binding,
                EQUAL,
                self.induc_from.internal_representation(),
                COLON,
                base_proof,
                indent!(QUESTION_GOAL, 1),
                step_keyword,
                COLON,
                step_proof
            ));
        }
        let mut out = format!(
            "{} {} {} {} {}{}
{}",
            BY,
            keyword,
            self.param_binding,
            FROM,
            self.induc_from.internal_representation(),
            COLON,
            indent!(
                &question_goals.join(
                    "
"
                ),
                1
            )
        );
        if !self.proof.is_empty() {
            out.push_str("\n");
            out.push_str(&indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}

impl ByFiniteSetInducStmt {
    pub fn internal_representation(&self) -> StmtInternalRepresentation {
        let question_goals: Vec<_> = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact.internal_representation()))
            .collect();
        let mut out = format!("{} {} {}", BY, INDUC, self.param_binding);
        if let Some(carrier_set) = &self.carrier_set {
            out.push_str(&format!(
                " {} {}",
                IN,
                carrier_set.internal_representation()
            ));
        }
        out.push_str(&format!(
            ":
{}",
            indent!(
                &question_goals.join(
                    "
"
                ),
                1
            )
        ));
        let base_colon = if self.base_proof.is_empty() {
            ""
        } else {
            COLON
        };
        out.push_str("\n");
        out.push_str(&indent!(
            &format!(
                "{} {} {} {} {}{}",
                QUESTION_GOAL, FROM, self.param_binding, EQUAL, "{}", base_colon
            ),
            1
        ));
        if !self.base_proof.is_empty() {
            out.push_str("\n");
            out.push_str(&indent!(
                &self
                    .base_proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                2
            ));
        }
        let step_colon = if self.step_proof.is_empty() {
            ""
        } else {
            COLON
        };
        out.push_str("\n");
        out.push_str(&indent!(
            &format!(
                "{} {} {}, {}{}",
                QUESTION_GOAL,
                INDUC,
                self.element_param_binding,
                self.smaller_set_param_binding,
                step_colon
            ),
            1
        ));
        if !self.step_proof.is_empty() {
            out.push_str("\n");
            out.push_str(&indent!(
                &self
                    .step_proof
                    .iter()
                    .map(|s| s.internal_representation())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                2
            ));
        }
        StmtInternalRepresentation(out)
    }
    impl_display_pair!();
}
