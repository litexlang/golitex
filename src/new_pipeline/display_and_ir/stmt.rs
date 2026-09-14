//! Stmt and statement variants: IR + display_string.

use super::types::StmtIR;
use crate::new_pipeline::ast::fact::ExistFact;
use crate::new_pipeline::ast::stmt::*;
use crate::new_pipeline::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            self.ir().display_string()
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
    pub fn ir(&self) -> StmtIR {
        match self {
            Stmt::Fact(x) => StmtIR(x.ir().0),
            Stmt::UnsafeStmt(x) => x.ir(),
            Stmt::Definition(x) => x.ir(),
            Stmt::ReleaseThmStmt(x) => x.ir(),
            Stmt::By(x) => x.ir(),
            Stmt::Witness(x) => x.ir(),
            Stmt::ProofBlock(x) => x.ir(),
            Stmt::Command(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl UnsafeStmt {
    pub fn ir(&self) -> StmtIR {
        match self {
            UnsafeStmt::TrustStmt(x) => x.ir(),
            UnsafeStmt::TrustHaveStmt(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl DefinitionStmt {
    pub fn ir(&self) -> StmtIR {
        match self {
            DefinitionStmt::LetObjStmt(x) => x.ir(),
            DefinitionStmt::HaveObjInNonemptySetStmt(x) => x.ir(),
            DefinitionStmt::HaveObjEqualStmt(x) => x.ir(),
            DefinitionStmt::HaveObjByExistFactsStmt(x) => x.ir(),
            DefinitionStmt::ObtainObjFromExistFact(x) => x.ir(),
            DefinitionStmt::ObtainObjFromAtomicFact(x) => x.ir(),
            DefinitionStmt::ObtainObjFromThm(x) => x.ir(),
            DefinitionStmt::HaveByPreimageStmt(x) => x.ir(),
            DefinitionStmt::HaveFnEqualStmt(x) => x.ir(),
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(x) => x.ir(),
            DefinitionStmt::HaveFnByInducStmt(x) => x.ir(),
            DefinitionStmt::HaveFnByForallExistUniqueStmt(x) => x.ir(),
            DefinitionStmt::HaveTupleStmt(x) => x.ir(),
            DefinitionStmt::HaveCartStmt(x) => x.ir(),
            DefinitionStmt::HaveSeqStmt(x) => x.ir(),
            DefinitionStmt::HaveFiniteSeqStmt(x) => x.ir(),
            DefinitionStmt::DefPropStmt(x) => x.ir(),
            DefinitionStmt::DefAbstractPropStmt(x) => x.ir(),
            DefinitionStmt::DefSettingStmt(x) => x.ir(),
            DefinitionStmt::DefTemplateStmt(x) => x.ir(),
            DefinitionStmt::DefStructStmt(x) => x.ir(),
            DefinitionStmt::DefAlgoStmt(x) => x.ir(),
            DefinitionStmt::DefThmStmt(x) => x.ir(),
            DefinitionStmt::AxiomStmt(x) => x.ir(),
            DefinitionStmt::DefStrategyStmt(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl ByStmt {
    pub fn ir(&self) -> StmtIR {
        match self {
            ByStmt::ByCasesStmt(x) => x.ir(),
            ByStmt::ByContraStmt(x) => x.ir(),
            ByStmt::ByEnumerateFiniteSetStmt(x) => x.ir(),
            ByStmt::ByFiniteSetInducStmt(x) => x.ir(),
            ByStmt::ByInducStmt(x) => x.ir(),
            ByStmt::ByForStmt(x) => x.ir(),
            ByStmt::ByExtensionStmt(x) => x.ir(),
            ByStmt::ByEnumerateRangeStmt(x) => x.ir(),
            ByStmt::ByClosedRangeAsCasesStmt(x) => x.ir(),
            ByStmt::ByTransitivePropStmt(x) => x.ir(),
            ByStmt::BySymmetricPropStmt(x) => x.ir(),
            ByStmt::ByReflexivePropStmt(x) => x.ir(),
            ByStmt::ByAntisymmetricPropStmt(x) => x.ir(),
            ByStmt::ByZornLemmaStmt(x) => x.ir(),
            ByStmt::ByAxiomOfChoiceStmt(x) => x.ir(),
            ByStmt::ByRegularityAxiomStmt(x) => x.ir(),
            ByStmt::ByDefStmt(x) => x.ir(),
            ByStmt::ByStructDefStmt(x) => x.ir(),
            ByStmt::ByThmStmt(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl WitnessStmt {
    pub fn ir(&self) -> StmtIR {
        match self {
            WitnessStmt::WitnessExistFact(x) => x.ir(),
            WitnessStmt::WitnessAtomicFact(x) => x.ir(),
            WitnessStmt::WitnessNonemptySet(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl ProofBlockStmt {
    pub fn ir(&self) -> StmtIR {
        match self {
            ProofBlockStmt::ClaimStmt(x) => x.ir(),
            ProofBlockStmt::ExampleStmt(x) => x.ir(),
            ProofBlockStmt::SketchStmt(x) => x.ir(),
            ProofBlockStmt::TryStmt(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl CommandStmt {
    pub fn ir(&self) -> StmtIR {
        match self {
            CommandStmt::EvalStmt(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl TheoremCall {
    pub fn ir(&self) -> StmtIR {
        let mut out = format!("{}", self.name.ir());
        if let TheoremCallArguments::Parenthesized(args) = &self.arguments {
            let parts: Vec<_> = args.iter().map(|a| a.ir()).collect();
            out.push_str(LEFT_PAREN);
            out.push_str(&parts.join(", "));
            out.push_str(RIGHT_PAREN);
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl EvalStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!("{} {}", EVAL, &self.obj_to_eval.ir()))
    }
    impl_display_pair!();
}

impl LetObjStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {}",
            LET,
            self.name,
            EQUAL,
            &self.value.ir()
        ))
    }
    impl_display_pair!();
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!("{} {}", HAVE, self.param_def.ir()))
    }
    impl_display_pair!();
}

impl HaveObjEqualStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let objs: Vec<_> = self
            .objs_equal_to
            .iter()
            .map(|o| o.ir())
            .collect();
        out.push_str(&format!(
            "{} {} {} {}",
            HAVE,
            self.param_def.ir(),
            EQUAL,
            objs.join(", ")
        ));

        StmtIR(out)
    }
    impl_display_pair!();
}

impl HaveObjByExistFactsStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let facts: Vec<_> = self
            .facts
            .iter()
            .map(|fact| fact.ir())
            .collect();
        out.push_str(&format!(
            "{} {}{}\n{}",
            HAVE,
            self.param_def.ir(),
            COLON,
            indent!(
                &facts.join(
                    "
"
                ),
                1
            )
        ));

        StmtIR(out)
    }
    impl_display_pair!();
}

impl TrustHaveStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let param_str = self.param_def.ir();
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
                        .map(|f| f.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }

        StmtIR(out)
    }
    impl_display_pair!();
}

impl TrustStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        if self.facts.len() == 1 {
            out.push_str(&format!(
                "{} {}",
                TRUST,
                &self.facts[0].ir()
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
                        .map(|f| f.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }

        StmtIR(out)
    }
    impl_display_pair!();
}

impl ObtainObjFromExistFact {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {}",
            OBTAIN,
            self.equal_tos.join(", "),
            FROM,
            self.fact.ir()
        ))
    }
    impl_display_pair!();
}

impl ObtainObjFromAtomicFact {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {}",
            OBTAIN,
            self.equal_tos.join(", "),
            FROM,
            self.fact.ir()
        ))
    }
    impl_display_pair!();
}

impl ObtainObjFromThm {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {}",
            OBTAIN,
            self.equal_tos.join(", "),
            FROM,
            THM,
            self.call.ir()
        ))
    }
    impl_display_pair!();
}

impl HaveByPreimageStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {} {}",
            HAVE,
            BY,
            PREIMAGE,
            self.preimage_names.join(", "),
            FROM,
            self.range_membership.ir()
        ))
    }
    impl_display_pair!();
}

impl FnSetClause {
    pub fn ir(&self) -> StmtIR {
        let params: Vec<_> = self
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.ir())
            .collect();
        let dom: Vec<_> = self
            .dom_facts
            .iter()
            .map(|d| d.ir())
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
        out.push_str(&self.ret_set.ir());
        StmtIR(out)
    }
    impl_display_pair!();
}

impl HaveFnEqualStmt {
    pub fn ir(&self) -> StmtIR {
        let body = &self.equal_to_anonymous_fn.alpha.body;
        let params: Vec<_> = body
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.ir())
            .collect();
        let dom: Vec<_> = body
            .dom_facts
            .iter()
            .map(|d| d.ir())
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
            self.equal_to_anonymous_fn.alpha.equal_to.as_ref().ir()
        ));
        StmtIR(out)
    }
    pub fn display_string(&self) -> String {
        let body = &self.equal_to_anonymous_fn.surface.body;
        let params: Vec<_> = body
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.display_string())
            .collect();
        let dom: Vec<_> = body
            .dom_facts
            .iter()
            .map(|d| d.display_string())
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
                .surface
                .equal_to
                .as_ref()
                .display_string()
        ));
        out
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn ir(&self) -> StmtIR {
        let params: Vec<_> = self
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.ir())
            .collect();
        let dom: Vec<_> = self
            .fn_set_clause
            .dom_facts
            .iter()
            .map(|d| d.ir())
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
            self.fn_set_clause.ret_set.ir(),
            BY,
            CASES,
            COLON
        ));
        for (i, case) in self.cases.iter().enumerate() {
            let line = format!(
                "{} {}{} {}",
                CASE,
                case.ir(),
                COLON,
                self.equal_tos[i].ir()
            );
            out.push_str(&indent!(&line, 1));
            if i + 1 < self.cases.len() {
                out.push_str("\n");
            }
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl HaveFnByInducCase {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}",
            CASE,
            &self.case_fact.ir(),
            COLON
        ));
        match &self.body {
            HaveFnByInducCaseBody::EqualTo(obj) => {
                out.push_str(&format!(" {}", obj.ir()));
            }
            HaveFnByInducCaseBody::NestedCases(cases) => {
                out.push_str(&format!("\n"));
                for (i, c) in cases.iter().enumerate() {
                    out.push_str(&format!("{}", indent!(&c.ir(), 1)));
                    if i + 1 < cases.len() {
                        out.push_str(&format!("\n"));
                    }
                }
            }
        }

        StmtIR(out)
    }
    impl_display_pair!();
}

impl HaveFnByInducStmt {
    pub fn ir(&self) -> StmtIR {
        let params: Vec<_> = self
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.ir())
            .collect();
        let dom: Vec<_> = self
            .fn_set_clause
            .dom_facts
            .iter()
            .map(|d| d.ir())
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
            self.fn_set_clause.ret_set.ir(),
            BY,
            INDUC,
            self.measure.ir(),
            FROM,
            self.lower_bound.ir()
        ));
        out.push_str(COLON);
        for case in self.cases.iter() {
            out.push_str("\n");
            out.push_str(&indent!(&case.ir(), 1));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl HaveFnByForallExistUniqueStmt {
    pub fn ir(&self) -> StmtIR {
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
                    self.forall.ir()
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl HaveTupleStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {} {} {}, {}[{}] {} {}",
            HAVE,
            TUPLE,
            self.name,
            FOR,
            self.index_name,
            LESS_EQUAL,
            &self.dimension.ir(),
            self.name,
            self.index_name,
            EQUAL,
            &self.value.ir()
        ))
    }
    impl_display_pair!();
}

impl HaveCartStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {} {} {}, {}[{}] {} {}",
            HAVE,
            CART,
            self.name,
            FOR,
            self.index_name,
            LESS_EQUAL,
            &self.dimension.ir(),
            self.name,
            self.index_name,
            EQUAL,
            &self.value.ir()
        ))
    }
    impl_display_pair!();
}

impl HaveSeqStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {} {}, {}({}) {} {}",
            HAVE,
            SEQ,
            self.name,
            self.seq_set.ir(),
            FOR,
            self.index_name,
            self.name,
            self.index_name,
            EQUAL,
            &self.value.ir()
        ))
    }
    impl_display_pair!();
}

impl HaveFiniteSeqStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {} {} {} {}, {}({}) {} {}",
            HAVE,
            FINITE_SEQ,
            self.name,
            self.finite_seq_set.ir(),
            FOR,
            self.index_name,
            LESS_EQUAL,
            &self.bound.ir(),
            self.name,
            self.index_name,
            EQUAL,
            &self.value.ir()
        ))
    }
    impl_display_pair!();
}

impl DefPropStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        out.push_str(&format!("{} {}{}", PROP, self.name, LEFT_PAREN));
        out.push_str(&format!(
            "{}{}",
            self.typed_parameters.ir(),
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
                        .map(|f| f.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl DefAbstractPropStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let params: Vec<_> = self
            .params
            .iter()
            .map(|p| p.ir())
            .collect();
        out.push_str(&format!("{} {}{}", ABSTRACT_PROP, self.name, LEFT_PAREN));
        out.push_str(&format!("{}{}", params.join(", "), RIGHT_PAREN));

        StmtIR(out)
    }
    impl_display_pair!();
}

impl DefSettingStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}{}{}",
            SETTING,
            self.name,
            LEFT_PAREN,
            self.param_def.ir(),
            RIGHT_PAREN
        ));
        if !self.dom_facts.is_empty() {
            out.push_str(&format!("{}", COLON));
            for fact in self.dom_facts.iter() {
                out.push_str(&format!("\n    {}", fact.ir()));
            }
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl TemplateDefEnum {
    pub fn ir(&self) -> StmtIR {
        match self {
            TemplateDefEnum::HaveObjInNonemptySetStmt(x) => x.ir(),
            TemplateDefEnum::HaveObjEqualStmt(x) => x.ir(),
            TemplateDefEnum::HaveObjByExistFactsStmt(x) => x.ir(),
            TemplateDefEnum::TrustHaveStmt(x) => x.ir(),
            TemplateDefEnum::ObtainObjFromExistFact(x) => x.ir(),
            TemplateDefEnum::ObtainObjFromAtomicFact(x) => x.ir(),
            TemplateDefEnum::ObtainObjFromThm(x) => x.ir(),
            TemplateDefEnum::HaveFnEqualStmt(x) => x.ir(),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(x) => x.ir(),
            TemplateDefEnum::HaveFnByInducStmt(x) => x.ir(),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(x) => x.ir(),
            TemplateDefEnum::HaveTupleStmt(x) => x.ir(),
            TemplateDefEnum::HaveCartStmt(x) => x.ir(),
            TemplateDefEnum::HaveSeqStmt(x) => x.ir(),
            TemplateDefEnum::HaveFiniteSeqStmt(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl DefTemplateStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = format!(
            "{}{}{}",
            TEMPLATE,
            LESS,
            self.template_arg_def.ir()
        );
        if !self.template_arg_dom.is_empty() {
            let dom: Vec<_> = self
                .template_arg_dom
                .iter()
                .map(|d| d.ir())
                .collect();
            out.push_str(&format!("{} {}", COLON, dom.join(", ")));
        }
        out.push_str(&format!(
            "{}{}
{}",
            GREATER,
            COLON,
            indent!(&self.template_def_stmt.ir(), 1)
        ));
        StmtIR(out)
    }
    impl_display_pair!();
}

impl StructFieldDef {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {}",
            self.binding,
            &self.field_type.ir()
        ))
    }
    impl_display_pair!();
}

impl DefStructStmt {
    pub fn ir(&self) -> StmtIR {
        match &self.param_def_with_dom {
            Some((param_def, _)) => {
                StmtIR(format!(
                    "{} {}{}{}{}{}",
                    STRUCT,
                    self.name,
                    LESS,
                    param_def.ir(),
                    GREATER,
                    COLON
                ))
            }
            None => StmtIR(format!(
                "{} {}{}",
                STRUCT, self.name, COLON
            )),
        }
    }
    impl_display_pair!();
}

impl AlgoReturn {
    pub fn ir(&self) -> StmtIR {
        StmtIR(self.value.ir().0)
    }
    impl_display_pair!();
}

impl AlgoCase {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {}{} {}",
            CASE,
            self.condition.ir(),
            COLON,
            indent!(&self.return_stmt.ir(), 1)
        ))
    }
    impl_display_pair!();
}

impl AlgoReturnOrAlgoCase {
    pub fn ir(&self) -> StmtIR {
        match self {
            AlgoReturnOrAlgoCase::AlgoReturn(x) => x.ir(),
            AlgoReturnOrAlgoCase::AlgoCase(x) => x.ir(),
        }
    }
    impl_display_pair!();
}

impl DefAlgoStmt {
    pub fn ir(&self) -> StmtIR {
        let mut body: Vec<_> = self
            .cases
            .iter()
            .map(|c| c.ir())
            .collect();
        if let Some(default_return) = &self.default_return {
            body.push(default_return.ir());
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
        StmtIR(out)
    }
    impl_display_pair!();
}

impl DefThmStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{}\n{}",
            THM,
            self.name,
            COLON,
            indent!(
                &format!("{} {}", QUESTION_GOAL, &self.fact.ir()),
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl AxiomStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {}{}\n{}",
            AXIOM,
            self.name,
            COLON,
            indent!(
                &format!(
                    "{} {}",
                    QUESTION_GOAL,
                    self.forall_fact.ir()
                ),
                1
            )
        ))
    }
    impl_display_pair!();
}

impl DefStrategyStmt {
    pub fn ir(&self) -> StmtIR {
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
                    self.forall_fact.ir()
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ClaimStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{}{}\n{}\n{}",
            CLAIM,
            COLON,
            indent!(
                &format!("{} {}", QUESTION_GOAL, &self.fact.ir()),
                1
            ),
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.ir())
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
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{}{}\n{}\n{}",
            EXAMPLE,
            COLON,
            indent!(
                &format!("{} {}", QUESTION_GOAL, &self.fact.ir()),
                1
            ),
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.ir())
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
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{}{}\n{}",
            SKETCH,
            COLON,
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.ir())
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
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{}{}\n{}",
            TRY,
            COLON,
            indent!(
                &self
                    .proof
                    .iter()
                    .map(|s| s.ir())
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
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {}",
            RELEASE,
            THM,
            self.call.ir()
        ))
    }
    impl_display_pair!();
}

impl WitnessExistFact {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let equal_tos: Vec<_> = self
            .equal_tos
            .iter()
            .map(|o| o.ir())
            .collect();
        let spec = match &self.exist_fact_in_witness {
            ExistFact::PlainExistFact(b)
            | ExistFact::ExistUniqueFact(b)
            | ExistFact::NotExistFact(b) => b,
        };
        let facts: Vec<_> = spec
            .facts
            .iter()
            .map(|fact| fact.ir())
            .collect();
        out.push_str(&format!(
            "{} {}{} {} {} {}",
            WITNESS,
            equal_tos.join(", "),
            COLON,
            spec.typed_parameters.ir(),
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl WitnessAtomicFact {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let witnesses: Vec<_> = self
            .witnesses
            .iter()
            .map(|o| o.ir())
            .collect();
        out.push_str(&format!(
            "{} {} {} {}",
            WITNESS,
            self.atomic_fact.ir(),
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl WitnessNonemptySet {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {} {}",
            WITNESS,
            &self.obj.ir(),
            &self.set.ir()
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByCasesStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        let question_goals: Vec<_> = self
            .then_facts
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact.ir()))
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
                    case.ir(),
                    COLON
                );
                let impossible_line = format!(
                    "{} {}",
                    indent!(IMPOSSIBLE, 2),
                    impossible_fact.ir()
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
                                .map(|s| s.ir())
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
                    case.ir()
                ));
            } else {
                case_blocks.push(format!(
                    "{} {}{}\n{}",
                    indent!(CASE, 1),
                    case.ir(),
                    COLON,
                    indent!(
                        &proof
                            .iter()
                            .map(|s| s.ir())
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

        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByContraStmt {
    pub fn ir(&self) -> StmtIR {
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
                    self.to_prove.ir()
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
                    .map(|s| s.ir())
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
            self.impossible_fact.ir()
        ));
        StmtIR(out)
    }
    impl_display_pair!();
}

macro_rules! impl_by_prop {
    ($ty:ty, $prop:expr) => {
        impl $ty {
            pub fn ir(&self) -> StmtIR {
                let mut out = format!(
                    "{} {}:
{}",
                    BY,
                    $prop,
                    indent!(
                        &format!(
                            "{} {}",
                            QUESTION_GOAL,
                            self.forall_fact.ir()
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
                            .map(|s| s.ir())
                            .collect::<Vec<_>>()
                            .join(
                                "
"
                            ),
                        1
                    ));
                }
                StmtIR(out)
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
    pub fn ir(&self) -> StmtIR {
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
                    self.forall_fact.ir()
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByExtensionStmt {
    pub fn ir(&self) -> StmtIR {
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
                    &self.left.ir(),
                    EQUAL,
                    &self.right.ir()
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ClosedRangeOrRange {
    pub fn ir(&self) -> StmtIR {
        match self {
            ClosedRangeOrRange::ClosedRange(x) => {
                StmtIR(x.ir().0)
            }
            ClosedRangeOrRange::Range(x) => {
                StmtIR(x.ir().0)
            }
        }
    }
    impl_display_pair!();
}

impl ByEnumerateRangeStmt {
    pub fn ir(&self) -> StmtIR {
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
            &self.element.ir(),
            FACT_PREFIX,
            IN,
            self.range.ir()
        ));

        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByClosedRangeAsCasesStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {}{} {} {}{} {}",
            BY,
            CLOSED_RANGE,
            AS,
            CASES,
            COLON,
            &self.element.ir(),
            FACT_PREFIX,
            IN,
            self.closed_range.ir()
        ))
    }
    impl_display_pair!();
}

impl ByDefStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!("{} {} {}", BY, DEF, self.fact.ir()))
    }
    impl_display_pair!();
}

impl ByStructDefStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {}",
            BY,
            STRUCT,
            DEF,
            &self.obj.ir()
        ))
    }
    impl_display_pair!();
}

impl ByThmStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {} {} {} {}",
            BY,
            THM,
            self.call.ir(),
            RIGHT_ARROW,
            self.selected_fact.ir()
        ))
    }
    impl_display_pair!();
}

impl ByAxiomOfChoiceStmt {
    pub fn ir(&self) -> StmtIR {
        if self.proof.is_empty() {
            return StmtIR(format!(
                "{} {}{} {} {}",
                BY,
                AXIOM_OF_CHOICE,
                COLON,
                SET,
                self.family.ir()
            ));
        }
        let mut out = format!(
            "{} {}{} {} {}{}",
            BY,
            AXIOM_OF_CHOICE,
            COLON,
            SET,
            self.family.ir(),
            COLON
        );
        out.push_str("\n");
        out.push_str(&indent!(
            &self
                .proof
                .iter()
                .map(|s| s.ir())
                .collect::<Vec<_>>()
                .join(
                    "
"
                ),
            1
        ));
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByRegularityAxiomStmt {
    pub fn ir(&self) -> StmtIR {
        StmtIR(format!(
            "{} {}({})",
            BY,
            REGULARITY_AXIOM,
            &self.set.ir()
        ))
    }
    impl_display_pair!();
}

impl ByZornLemmaStmt {
    pub fn ir(&self) -> StmtIR {
        let mut out = String::new();
        out.push_str(&format!(
            "{} {}{} {} {}, {} {}, {} {}, {} {}",
            BY,
            ZORN_LEMMA,
            COLON,
            SET,
            &self.set.ir(),
            PROP,
            self.prop_name.ir(),
            PROP,
            self.upper_bound_prop_name.ir(),
            PROP,
            self.maximal_prop_name.ir()
        ));
        if !self.proof.is_empty() {
            out.push_str(&format!(
                "{}\n{}",
                COLON,
                indent!(
                    &self
                        .proof
                        .iter()
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    1
                )
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByInducStmt {
    pub fn ir(&self) -> StmtIR {
        let question_goals: Vec<_> = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact.ir()))
            .collect();
        let keyword = if self.strong { STRONG_INDUC } else { INDUC };
        let has_structured = self.base_proof.is_some() || self.step_proof.is_some();
        if has_structured {
            let step_keyword = if self.strong { STRONG_INDUC } else { INDUC };
            let base_proof = match &self.base_proof {
                Some(proof) => indent!(
                    &proof
                        .iter()
                        .map(|s| s.ir())
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
                        .map(|s| s.ir())
                        .collect::<Vec<_>>()
                        .join(
                            "
"
                        ),
                    2
                ),
                None => String::new(),
            };
            return StmtIR(format!(
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
                self.induc_from.ir(),
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
                self.induc_from.ir(),
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
            self.induc_from.ir(),
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
                    .map(|s| s.ir())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                1
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}

impl ByFiniteSetInducStmt {
    pub fn ir(&self) -> StmtIR {
        let question_goals: Vec<_> = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact.ir()))
            .collect();
        let mut out = format!("{} {} {}", BY, INDUC, self.param_binding);
        if let Some(carrier_set) = &self.carrier_set {
            out.push_str(&format!(
                " {} {}",
                IN,
                carrier_set.ir()
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
                    .map(|s| s.ir())
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
                    .map(|s| s.ir())
                    .collect::<Vec<_>>()
                    .join(
                        "
"
                    ),
                2
            ));
        }
        StmtIR(out)
    }
    impl_display_pair!();
}
