use crate::prelude::*;

fn chain_link_infix_latex(prop: &str) -> Option<&'static str> {
    if prop == EQUAL {
        Some("=")
    } else if prop == NOT_EQUAL {
        Some(r"\neq")
    } else if prop == LESS {
        Some("<")
    } else if prop == GREATER {
        Some(">")
    } else if prop == LESS_EQUAL {
        Some(r"\leq")
    } else if prop == GREATER_EQUAL {
        Some(r"\geq")
    } else if prop == IN {
        Some(r"\in")
    } else {
        None
    }
}

fn latex_escape_underscore(s: &str) -> String {
    s.replace('_', r"\_")
}

fn latex_local_ident(name: &str) -> String {
    format!(r"\mathit{{{}}}", latex_escape_underscore(name))
}

fn latex_texttt_escape(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '_' | '%' | '#' | '&' | '$' => {
                out.push('\\');
                out.push(ch);
            }
            '{' => out.push_str(r"\{"),
            '}' => out.push_str(r"\}"),
            '\\' => out.push_str(r"\textbackslash{}"),
            '^' => out.push_str(r"\textasciicircum{}"),
            '~' => out.push_str(r"\textasciitilde{}"),
            _ => out.push(ch),
        }
    }
    out
}

fn fn_set_clause_latex(clause: &FnSetClause) -> String {
    let mut slots: Vec<String> = Vec::new();
    for g in clause.params_def_with_set.iter() {
        let set = fn_param_group_type_to_latex(g);
        for p in &g.params {
            slots.push(format!(r"{} \in {}", latex_local_ident(p), set));
        }
    }
    let dom = clause
        .dom_facts
        .iter()
        .map(|f| f.to_latex_string())
        .collect::<Vec<_>>()
        .join(r", ");
    let ret = clause.ret_set.to_latex_string();
    if dom.is_empty() {
        format!(
            r"\mathrm{{fn}}\left({}\right)\to {}",
            slots.join(r", "),
            ret
        )
    } else {
        format!(
            r"\mathrm{{fn}}\left({} \,\middle|\, {}\right)\to {}",
            slots.join(r", "),
            dom,
            ret
        )
    }
}

fn fn_param_group_type_to_latex(g: &ParamGroupWithSet) -> String {
    g.set_obj().to_latex_string()
}

impl AndChainAtomicFact {
    pub fn to_latex_string(&self) -> String {
        match self {
            AndChainAtomicFact::AtomicFact(x) => x.to_latex_string(),
            AndChainAtomicFact::AndFact(x) => x.to_latex_string(),
            AndChainAtomicFact::ChainFact(x) => x.to_latex_string(),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn to_latex_string(&self) -> String {
        match self {
            OrAndChainAtomicFact::AtomicFact(x) => x.to_latex_string(),
            OrAndChainAtomicFact::AndFact(x) => x.to_latex_string(),
            OrAndChainAtomicFact::ChainFact(x) => x.to_latex_string(),
            OrAndChainAtomicFact::OrFact(x) => x.to_latex_string(),
        }
    }
}

impl AndFact {
    pub fn to_latex_string(&self) -> String {
        self.facts
            .iter()
            .map(|a| a.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ")
    }
}

impl ChainFact {
    pub fn to_latex_string(&self) -> String {
        if self.objs.is_empty() {
            return String::new();
        }
        let mut s = self.objs[0].to_latex_string();
        for (i, obj) in self.objs[1..].iter().enumerate() {
            let pname = self.prop_names[i].to_string();
            let rhs = obj.to_latex_string();
            if let Some(op) = chain_link_infix_latex(&pname) {
                s.push(' ');
                s.push_str(op);
                s.push(' ');
                s.push_str(&rhs);
            } else if is_comparison_str(&pname) {
                s.push(' ');
                s.push_str(&pname);
                s.push(' ');
                s.push_str(&rhs);
            } else {
                s.push_str(&format!(r" \mathrel{{\mathrm{{{}}}}} {}", pname, rhs));
            }
        }
        s
    }
}

impl Abs {
    pub fn to_latex_string(&self) -> String {
        format!(r"\left| {} \right|", self.arg.to_latex_string())
    }
}

impl Sqrt {
    pub fn to_latex_string(&self) -> String {
        format!(r"\sqrt{{{}}}", self.arg.to_latex_string())
    }
}

impl Add {
    pub fn to_latex_string(&self) -> String {
        format!(
            "{} + {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl ByCasesStmt {
    pub fn to_latex_string(&self) -> String {
        let goal = self
            .then_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ");
        let mut rows: Vec<String> = Vec::new();
        rows.push(format!(r"\text{{Proof by cases. Goal:}} & {}", goal));
        for (i, ((case, proof), imposs)) in self
            .cases
            .iter()
            .zip(self.proofs.iter())
            .zip(self.impossible_facts.iter())
            .enumerate()
        {
            rows.push(format!(
                r"\textbf{{\text{{Case {}.}}}} & {}",
                i + 1,
                case.to_latex_string()
            ));
            for st in proof {
                rows.push(format!(r"& \quad {}", st.to_latex_string()));
            }
            if let Some(atom) = imposs {
                rows.push(format!(
                    r"\textbf{{\text{{Impossible.}}}} & {}",
                    atom.to_latex_string()
                ));
            }
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByContraStmt {
    pub fn to_latex_string(&self) -> String {
        let goal = self.to_prove.to_latex_string();
        let mut rows = vec![format!(
            r"\text{{Proof by contradiction. Goal:}} & {}",
            goal
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        rows.push(format!(
            r"\textbf{{\text{{Contradiction.}}}} & {}",
            self.impossible_fact.to_latex_string()
        ));
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByClosedRangeAsCasesStmt {
    pub fn to_latex_string(&self) -> String {
        let a = self.closed_range.start.to_latex_string();
        let b = self.closed_range.end.to_latex_string();
        let x = self.element.to_latex_string();
        let row1 = format!(
            r"&\text{{\textbf{{By closed range as cases}} on }} [\![ {0},{1}]\!]\text{{.}}",
            a, b
        );
        let row2 = format!(
            r"&\text{{Equivalently }} {0} \in \{{{1},\, {1}+1,\, \ldots,\, {2}\}}\text{{ (segment {1}\ldots {2}).}}",
            x, a, b
        );
        let row3 = format!(
            r"&\text{{So }} {0}={1}\lor {0}={1}+1\lor\cdots\lor {0}={2}\text{{.}}",
            x, a, b
        );
        format!("\\begin{{aligned}}\n{row1} \\\\\n{row2} \\\\\n{row3} \n\\end{{aligned}}")
    }
}

impl ByEnumerateRangeStmt {
    pub fn to_latex_string(&self) -> String {
        latex_texttt_escape(&self.to_string())
    }
}

impl ByEnumerateFiniteSetStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{Proof by exhaustive enumeration (finite cases).}} & {}",
            self.forall_fact.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByExtensionStmt {
    pub fn to_latex_string(&self) -> String {
        let l = self.left.to_latex_string();
        let r = self.right.to_latex_string();
        let mut rows = vec![format!(
            r"\text{{\textbf{{By extensionality}}:}} & {}={} \Longleftrightarrow \bigl({}\subseteq {}\land {}\subseteq {}\bigr)\text{{.}}",
            l, r, l, r, r, l
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByForStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by for}}:}} & {}",
            self.forall_fact.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByTransitivePropStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by transitive_prop}}:}} & {}",
            self.forall_fact.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl BySymmetricPropStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by symmetric_prop}}:}} & {}",
            self.forall_fact.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByReflexivePropStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by reflexive_prop}}:}} & {}",
            self.forall_fact.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByAntisymmetricPropStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by antisymmetric_prop}}:}} & {}",
            self.forall_fact.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByZornLemmaStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by zorn_lemma:}}}} \text{{set }} {}, \text{{prop }} {}",
            self.set.to_latex_string(),
            latex_texttt_escape(&self.prop_name.to_string())
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByAxiomOfChoiceStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by axiom_of_choice:}}}} \text{{set }} {}",
            self.family.to_latex_string()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByRegularityAxiomStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\text{{\textbf{{by regularity_axiom}}}}({})",
            self.set.to_latex_string()
        )
    }
}

impl ByInducStmt {
    pub fn to_latex_string(&self) -> String {
        let goals = self
            .to_prove
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ");
        let induc_label = if self.strong {
            r"\text{\textbf{strong induc} on }"
        } else {
            r"\text{\textbf{by induc} on }"
        };
        let mut rows = vec![format!(
            r"{} {} \text{{ from }} {} \texttt{{:}} & {}",
            induc_label,
            latex_local_ident(&self.param),
            self.induc_from.to_latex_string(),
            goals
        )];
        rows.push(r"\text{prove:} &".to_string());
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl Cap {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            CAP,
            self.left.to_latex_string()
        )
    }
}

impl Cart {
    pub fn to_latex_string(&self) -> String {
        let inner = self
            .args
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\operatorname{{{}}}\left( {}\right)", CART, inner)
    }
}

impl CartDim {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            CART_DIM,
            self.set.to_latex_string()
        )
    }
}

impl ClaimStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows = vec![
            format!(
                r"\text{{\textbf{{claim}}:}} & {}",
                self.fact.to_latex_string()
            ),
            r"\text{\textbf{prove}:} &".to_string(),
        ];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ClosedRange {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            CLOSED_RANGE,
            self.start.to_latex_string(),
            self.end.to_latex_string()
        )
    }
}

impl IntervalObj {
    pub fn to_latex_string(&self) -> String {
        let (left, right) = match self {
            IntervalObj::LeftOpenRightOpen(_) => ("(", ")"),
            IntervalObj::LeftOpenRightClosed(_) => ("(", "]"),
            IntervalObj::LeftClosedRightOpen(_) => ("[", ")"),
            IntervalObj::LeftClosedRightClosed(_) => ("[", "]"),
        };
        format!(
            r"\left{} {}, {} \right{}",
            left,
            self.start().to_latex_string(),
            self.end().to_latex_string(),
            right
        )
    }
}

impl OneSideInfinityIntervalObj {
    pub fn to_latex_string(&self) -> String {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(_) => {
                format!(r"\left( {}, \infty \right)", self.start().to_latex_string())
            }
            OneSideInfinityIntervalObj::LeftClosed(_) => {
                format!(r"\left[ {}, \infty \right)", self.start().to_latex_string())
            }
            OneSideInfinityIntervalObj::RightOpen(_) => {
                format!(
                    r"\left( -\infty, {} \right)",
                    self.start().to_latex_string()
                )
            }
            OneSideInfinityIntervalObj::RightClosed(_) => {
                format!(
                    r"\left( -\infty, {} \right]",
                    self.start().to_latex_string()
                )
            }
        }
    }
}

impl Count {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            COUNT,
            self.set.to_latex_string()
        )
    }
}

impl FnRange {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            FN_RANGE,
            self.function.to_latex_string()
        )
    }
}

impl FnRangeOn {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FN_RANGE_ON,
            self.function.to_latex_string(),
            self.set.to_latex_string()
        )
    }
}

impl Replacement {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            REPLACEMENT,
            self.prop_name,
            self.source_set.to_latex_string()
        )
    }
}

impl Sum {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {} \right)",
            SUM,
            self.start.to_latex_string(),
            self.end.to_latex_string(),
            self.func.to_latex_string()
        )
    }
}

impl SumOfFiniteSet {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FINITE_SET_SUM,
            self.set.to_latex_string(),
            self.func.to_latex_string()
        )
    }
}

impl ProductOfFiniteSet {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FINITE_SET_PRODUCT,
            self.set.to_latex_string(),
            self.func.to_latex_string()
        )
    }
}

impl Product {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {} \right)",
            PRODUCT,
            self.start.to_latex_string(),
            self.end.to_latex_string(),
            self.func.to_latex_string()
        )
    }
}

impl Cup {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            CUP,
            self.left.to_latex_string()
        )
    }
}

impl DefAbstractPropStmt {
    pub fn to_latex_string(&self) -> String {
        let ps = self
            .params
            .iter()
            .map(|p| latex_local_ident(p))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"\operatorname{{{}}}\, {}\left\{{ {} \right\}}",
            ABSTRACT_PROP,
            latex_local_ident(&self.name),
            ps
        )
    }
}

impl DefAlgoStmt {
    pub fn to_latex_string(&self) -> String {
        let ps = self
            .params
            .iter()
            .map(|p| latex_local_ident(p))
            .collect::<Vec<_>>()
            .join(", ");
        let mut rows = vec![format!(
            r"\operatorname{{{}}}\, {}\left( {}\right) \texttt{{:}}",
            ALGO,
            latex_local_ident(&self.name),
            ps
        )];
        for c in &self.cases {
            rows.push(format!(
                r"& \quad \mathrm{{case}}\ {} \texttt{{:}}\ {}",
                c.condition.to_latex_string(),
                c.return_stmt.value.to_latex_string()
            ));
        }
        if let Some(dr) = &self.default_return {
            rows.push(format!(
                r"& \quad \mathrm{{default}}\ \texttt{{:}}\ {}",
                dr.value.to_latex_string()
            ));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl DefLetStmt {
    pub fn to_latex_string(&self) -> String {
        match self.facts.len() {
            0 => format!(
                r"\operatorname{{{}}}\, {}",
                LET,
                self.param_def.to_latex_string()
            ),
            _ => {
                let mut rows = vec![format!(
                    r"\operatorname{{{}}}\, {}",
                    LET,
                    self.param_def.to_latex_string()
                )];
                for fact in &self.facts {
                    rows.push(format!(r"& \quad {}", fact.to_latex_string()));
                }
                format!(
                    "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                    rows.join(" \\\\\n")
                )
            }
        }
    }
}

impl DefPropStmt {
    pub fn to_latex_string(&self) -> String {
        match self.iff_facts.len() {
            0 => format!(
                r"\operatorname{{{}}}\, {}\left\{{ {} \right\}}",
                PROP,
                latex_local_ident(&self.name),
                self.params_def_with_type.to_latex_string()
            ),
            _ => {
                let mut rows = vec![format!(
                    r"\operatorname{{{}}}\, {}\left\{{ {} \right\}} \texttt{{:}}",
                    PROP,
                    latex_local_ident(&self.name),
                    self.params_def_with_type.to_latex_string()
                )];
                for fact in &self.iff_facts {
                    rows.push(format!(r"& \quad {}", fact.to_latex_string()));
                }
                format!(
                    "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                    rows.join(" \\\\\n")
                )
            }
        }
    }
}

impl Div {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\frac{{{}}}{{{}}}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl DoNothingStmt {
    pub fn to_latex_string(&self) -> String {
        format!(r"\mathrm{{{}}}", DO_NOTHING)
    }
}

impl ClearStmt {
    pub fn to_latex_string(&self) -> String {
        format!(r"\mathrm{{{}}}", CLEAR)
    }
}

impl StopImportStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\ \operatorname{{{}}}\ {}",
            STOP,
            IMPORT,
            latex_local_ident(&self.module_name)
        )
    }
}

impl EqualFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            "{} = {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl EvalStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\, {}",
            EVAL,
            self.obj_to_eval.to_latex_string()
        )
    }
}

impl EvalByStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\, {} \operatorname{{{}}} {}",
            EVAL,
            self.lhs.to_latex_string(),
            FROM,
            self.rhs.to_latex_string()
        )
    }
}

impl ExistFactEnum {
    pub fn to_latex_string(&self) -> String {
        let head = if self.is_not_exist() {
            r"\nexists"
        } else if self.is_exist_unique() {
            r"\exists!"
        } else {
            r"\exists"
        };
        let params = self.params_def_with_type().to_latex_string();
        let facts = self
            .facts()
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r", ");
        format!(
            r"{}\, \left( {}\right)\, \mathrm{{st}}\, \left\{{ {} \right\}}",
            head, params, facts
        )
    }
}

impl ExistBodyFact {
    pub fn to_latex_string(&self) -> String {
        match self {
            ExistBodyFact::AtomicFact(x) => x.to_latex_string(),
            ExistBodyFact::AndFact(x) => x.to_latex_string(),
            ExistBodyFact::ChainFact(x) => x.to_latex_string(),
            ExistBodyFact::OrFact(x) => x.to_latex_string(),
            ExistBodyFact::InlineForall(x) => x.to_latex_string(),
        }
    }
}

impl ExistOrAndChainAtomicFact {
    pub fn to_latex_string(&self) -> String {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(x) => x.to_latex_string(),
            ExistOrAndChainAtomicFact::AndFact(x) => x.to_latex_string(),
            ExistOrAndChainAtomicFact::ChainFact(x) => x.to_latex_string(),
            ExistOrAndChainAtomicFact::OrFact(x) => x.to_latex_string(),
            ExistOrAndChainAtomicFact::ExistFact(x) => x.to_latex_string(),
        }
    }
}

impl FiniteSeqListObj {
    pub fn to_latex_string(&self) -> String {
        let inner = self
            .objs
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left[ {} \right]", inner)
    }
}

impl FiniteSeqSet {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FINITE_SEQ,
            self.set.to_latex_string(),
            self.n.to_latex_string()
        )
    }
}

impl FnObj {
    pub fn to_latex_string(&self) -> String {
        let head = match self.head.as_ref() {
            FnObjHead::Identifier(i) => i.to_latex_string(),
            FnObjHead::IdentifierWithMod(i) => i.to_latex_string(),
            FnObjHead::Forall(p) => latex_local_ident(&p.name),
            FnObjHead::DefHeader(p) => latex_local_ident(&p.name),
            FnObjHead::Exist(p) => latex_local_ident(&p.name),
            FnObjHead::SetBuilder(p) => latex_local_ident(&p.name),
            FnObjHead::FnSet(p) => latex_local_ident(&p.name),
            FnObjHead::AnonymousFnLiteral(a) => a.to_latex_string(),
            FnObjHead::FiniteSeqListObj(v) => v.to_latex_string(),
            FnObjHead::ObjAtIndex(v) => v.to_latex_string(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => latex_texttt_escape(&v.to_string()),
            FnObjHead::Induc(p) => latex_local_ident(&p.name),
            FnObjHead::DefAlgo(p) => latex_local_ident(&p.name),
            FnObjHead::TupleIndex(p) => latex_local_ident(&p.name),
            FnObjHead::CartIndex(p) => latex_local_ident(&p.name),
            FnObjHead::InstantiatedTemplateObj(t) => latex_texttt_escape(&t.to_string()),
        };
        let mut s = head;
        for group in self.body.iter() {
            let inner = group
                .iter()
                .map(|o| o.to_latex_string())
                .collect::<Vec<_>>()
                .join(", ");
            s.push_str(&format!(r"\left( {} \right)", inner));
        }
        s
    }
}

impl AnonymousFn {
    pub fn to_latex_string(&self) -> String {
        let mut slots: Vec<String> = Vec::new();
        for g in self.body.params_def_with_set.iter() {
            let set = fn_param_group_type_to_latex(g);
            for p in &g.params {
                slots.push(format!(r"{} \in {}", latex_local_ident(p), set));
            }
        }
        let dom = self
            .body
            .dom_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r", ");
        let ret = self.body.ret_set.to_latex_string();
        let body = self.equal_to.to_latex_string();
        let sig = if dom.is_empty() {
            format!(r"\left({}\right)", slots.join(r", "))
        } else {
            format!(r"\left({} \,\middle|\, {}\right)", slots.join(r", "), dom)
        };
        format!(
            r"'\, {} \to {} \mapsto \left\{{ {}\right\}}",
            sig, ret, body
        )
    }
}

impl FnSet {
    pub fn to_latex_string(&self) -> String {
        let mut slots: Vec<String> = Vec::new();
        for g in self.body.params_def_with_set.iter() {
            let set = fn_param_group_type_to_latex(g);
            for p in &g.params {
                slots.push(format!(r"{} \in {}", latex_local_ident(p), set));
            }
        }
        let dom = self
            .body
            .dom_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r", ");
        let ret = self.body.ret_set.to_latex_string();
        if dom.is_empty() {
            format!(
                r"\mathrm{{fn}}\left({}\right)\to {}",
                slots.join(r", "),
                ret
            )
        } else {
            format!(
                r"\mathrm{{fn}}\left({} \,\middle|\, {}\right)\to {}",
                slots.join(r", "),
                dom,
                ret
            )
        }
    }
}

impl ForallFact {
    pub fn to_latex_string(&self) -> String {
        let params = self.params_def_with_type.to_latex_string();
        let then = self
            .then_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ");
        if self.dom_facts.is_empty() {
            format!(r"\forall \left( {}\right),\, {}", params, then)
        } else {
            let dom = self
                .dom_facts
                .iter()
                .map(|f| f.to_latex_string())
                .collect::<Vec<_>>()
                .join(r" \land ");
            format!(
                r"\forall \left( {}\right),\ \left( {}\right) \Rightarrow \left( {}\right)",
                params, dom, then
            )
        }
    }
}

impl ForallFactWithIff {
    pub fn to_latex_string(&self) -> String {
        let iff = self
            .iff_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ");
        format!(
            r"{}\, \Longleftrightarrow\, \left( {}\right)",
            self.forall_fact.to_latex_string(),
            iff
        )
    }
}

impl NotForallFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg\, \left( {}\right)",
            self.forall_fact.to_latex_string()
        )
    }
}

impl GreaterEqualFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \geq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl GreaterFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            "{} > {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl HaveByExistStmt {
    pub fn to_latex_string(&self) -> String {
        let names = self
            .equal_tos
            .iter()
            .map(|s| latex_local_ident(s))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"\mathrm{{have}}\ \mathrm{{by}}\ {} : {}",
            self.exist_fact_in_have_obj_st.to_latex_string(),
            names
        )
    }
}

impl HaveFnByInducStmt {
    pub fn to_latex_string(&self) -> String {
        let mut rows: Vec<String> = Vec::new();
        rows.push(format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ {} \quad \mathrm{{by}}\ \mathrm{{induc}}\ {} \ \mathrm{{from}}\ {}",
            latex_local_ident(&self.name),
            fn_set_clause_latex(&self.fn_set_clause),
            self.measure.to_latex_string(),
            self.lower_bound.to_latex_string(),
        ));
        Self::push_case_rows(&mut rows, &self.cases, 1);
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }

    fn push_case_rows(rows: &mut Vec<String>, cases: &[HaveFnByInducCase], indent: usize) {
        let pad = r"\quad ".repeat(indent);
        for c in cases {
            match &c.body {
                HaveFnByInducCaseBody::EqualTo(eq) => rows.push(format!(
                    r"& {} \mathrm{{case}}\ {} : {}",
                    pad,
                    c.case_fact.to_latex_string(),
                    eq.to_latex_string()
                )),
                HaveFnByInducCaseBody::NestedCases(nested) => {
                    rows.push(format!(
                        r"& {} \mathrm{{case}}\ {} \texttt{{:}}",
                        pad,
                        c.case_fact.to_latex_string()
                    ));
                    Self::push_case_rows(rows, nested, indent + 1);
                }
            }
        }
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn to_latex_string(&self) -> String {
        let head = format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ \mathrm{{by}}\ \mathrm{{cases}}\texttt{{:}}",
            latex_local_ident(&self.name)
        );
        let clause = fn_set_clause_latex(&self.fn_set_clause);
        let mut rows = vec![format!(r"{} & {}", head, clause)];
        for (i, case) in self.cases.iter().enumerate() {
            rows.push(format!(
                r"& \quad \mathrm{{case}}\ {} \texttt{{:}}\ {}",
                case.to_latex_string(),
                self.equal_tos[i].to_latex_string()
            ));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl HaveFnEqualStmt {
    pub fn to_latex_string(&self) -> String {
        let fn_set_clause = FnSetClause::new(
            self.equal_to_anonymous_fn.body.params_def_with_set.clone(),
            self.equal_to_anonymous_fn.body.dom_facts.clone(),
            (*self.equal_to_anonymous_fn.body.ret_set).clone(),
        )
        .expect("anonymous function signature was already validated");
        format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ {} {}",
            latex_local_ident(&self.name),
            fn_set_clause_latex(&fn_set_clause),
            self.equal_to_anonymous_fn.equal_to.to_latex_string()
        )
    }
}

impl HaveFnByForallExistUniqueStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ \mathrm{{as}}\ \mathrm{{set}}:\ {}",
            latex_local_ident(&self.fn_name),
            self.forall.to_latex_string()
        )
    }
}

impl HaveObjEqualStmt {
    pub fn to_latex_string(&self) -> String {
        let rhs = self
            .objs_equal_to
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"\mathrm{{have}}\ {} = {}",
            self.param_def.to_latex_string(),
            rhs
        )
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn to_latex_string(&self) -> String {
        format!(r"\mathrm{{have}}\ {}", self.param_def.to_latex_string())
    }
}

impl HaveObjByExistFactsStmt {
    pub fn to_latex_string(&self) -> String {
        let facts = self
            .facts
            .iter()
            .map(|fact| fact.to_latex_string())
            .collect::<Vec<_>>()
            .join(r"; ");
        format!(
            r"\mathrm{{have}}\ {} : \left\{{ {} \right\}}",
            self.param_def.to_latex_string(),
            facts
        )
    }
}

impl Identifier {
    pub fn to_latex_string(&self) -> String {
        latex_local_ident(&self.name)
    }
}

impl IdentifierWithMod {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{}\mathbin{{\mathrm{{::}}}}{}",
            latex_local_ident(&self.mod_name),
            latex_local_ident(&self.name)
        )
    }
}

impl AtomicName {
    pub fn to_latex_string(&self) -> String {
        match self {
            AtomicName::WithoutMod(s) => latex_local_ident(s),
            AtomicName::WithMod(m, n) => format!(
                r"{}\mathbin{{\mathrm{{::}}}}{}",
                latex_local_ident(m),
                latex_local_ident(n)
            ),
        }
    }
}

impl InFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \in {}",
            self.element.to_latex_string(),
            self.set.to_latex_string()
        )
    }
}

impl Intersect {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \cap {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl IsCartFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_CART,
            self.set.to_latex_string()
        )
    }
}

impl IsFiniteSetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_FINITE_SET,
            self.set.to_latex_string()
        )
    }
}

impl IsNonemptySetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_NONEMPTY_SET,
            self.set.to_latex_string()
        )
    }
}

impl IsSetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_SET,
            self.set.to_latex_string()
        )
    }
}

impl IsTupleFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_TUPLE,
            self.set.to_latex_string()
        )
    }
}

impl ProofDebtStmt {
    pub fn to_latex_string(&self) -> String {
        if self.facts.len() == 1 {
            format!(
                r"\operatorname{{{}}} {}",
                PROOF_DEBT,
                self.facts[0].to_latex_string()
            )
        } else {
            let rows = self
                .facts
                .iter()
                .map(|fact| format!("& {}", fact.to_latex_string()))
                .collect::<Vec<_>>()
                .join(" \\\\\n");
            format!(
                r"\operatorname{{{}}}\colon \begin{{aligned}}{}\end{{aligned}}",
                PROOF_DEBT, rows
            )
        }
    }
}

impl LessEqualFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \leq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl LessFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            "{} < {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl ListSet {
    pub fn to_latex_string(&self) -> String {
        let inner = self
            .list
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left\{{ {} \right\}}", inner)
    }
}

impl Log {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\log_{{{}}} \left( {} \right)",
            self.base.to_latex_string(),
            self.arg.to_latex_string()
        )
    }
}

impl MatrixAdd {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.left.to_latex_string(),
            latex_escape_underscore(MATRIX_ADD),
            self.right.to_latex_string()
        )
    }
}

impl MatrixListObj {
    pub fn to_latex_string(&self) -> String {
        let rows = self
            .rows
            .iter()
            .map(|row| {
                let inner = row
                    .iter()
                    .map(|o| o.to_latex_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(r"\left( {} \right)", inner)
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left[ {} \right]", rows)
    }
}

impl MatrixMul {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.left.to_latex_string(),
            latex_escape_underscore(MATRIX_MUL),
            self.right.to_latex_string()
        )
    }
}

impl MatrixPow {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.base.to_latex_string(),
            latex_escape_underscore(MATRIX_POW),
            self.exponent.to_latex_string()
        )
    }
}

impl MatrixScalarMul {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.scalar.to_latex_string(),
            latex_escape_underscore(MATRIX_SCALAR_MUL),
            self.matrix.to_latex_string()
        )
    }
}

impl MatrixSet {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {} \right)",
            MATRIX,
            self.set.to_latex_string(),
            self.row_len.to_latex_string(),
            self.col_len.to_latex_string()
        )
    }
}

impl MatrixSub {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.left.to_latex_string(),
            latex_escape_underscore(MATRIX_SUB),
            self.right.to_latex_string()
        )
    }
}

impl Max {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\max \left( {}, {} \right)",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl Min {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\min \left( {}, {} \right)",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl Mod {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\left( {} \mathbin{{\mathrm{{mod}}}} {} \right)",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl Mul {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{0} \cdot {1}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NormalAtomicFact {
    pub fn to_latex_string(&self) -> String {
        let pred = self.predicate.to_latex_string();
        let args = self
            .body
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\$ {}\left( {}\right)", pred, args)
    }
}

impl NotEqualFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \neq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NotGreaterEqualFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \ngeq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NotGreaterFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \ngtr {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NotInFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \notin {}",
            self.element.to_latex_string(),
            self.set.to_latex_string()
        )
    }
}

impl NotIsCartFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_CART,
            self.set.to_latex_string()
        )
    }
}

impl NotIsFiniteSetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_FINITE_SET,
            self.set.to_latex_string()
        )
    }
}

impl NotIsNonemptySetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_NONEMPTY_SET,
            self.set.to_latex_string()
        )
    }
}

impl NotIsSetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_SET,
            self.set.to_latex_string()
        )
    }
}

impl NotIsTupleFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_TUPLE,
            self.set.to_latex_string()
        )
    }
}

impl NotLessEqualFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \nleq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NotLessFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \nless {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NotNormalAtomicFact {
    pub fn to_latex_string(&self) -> String {
        let pred = self.predicate.to_latex_string();
        let args = self
            .body
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\neg \left( \$ {}\left( {}\right) \right)", pred, args)
    }
}

impl NotRestrictFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( {} \mathrel{{\$}} \mathrm{{{}}}\, {} \right)",
            self.obj.to_latex_string(),
            RESTRICTS_TO,
            self.obj_cannot_restrict_to_fn_set.to_latex_string()
        )
    }
}

impl NotSubsetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( {} \subseteq {} \right)",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl NotSupersetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\neg \left( {} \supseteq {} \right)",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl Number {
    pub fn to_latex_string(&self) -> String {
        self.normalized_value.clone()
    }
}

impl ObjAtIndex {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{}\left[ {} \right]",
            self.obj.to_latex_string(),
            self.index.to_latex_string()
        )
    }
}

impl OrFact {
    pub fn to_latex_string(&self) -> String {
        self.facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \lor ")
    }
}

impl ParamDefWithType {
    pub fn to_latex_string(&self) -> String {
        self.groups
            .iter()
            .map(|g| g.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl ParamGroupWithParamType {
    pub fn to_latex_string(&self) -> String {
        let names = self
            .params
            .iter()
            .map(|p| latex_local_ident(p))
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"{}, {}", names, self.param_type.to_latex_string())
    }
}

impl ParamType {
    pub fn to_latex_string(&self) -> String {
        match self {
            ParamType::Set(_) => format!(r"\mathrm{{{}}}", SET),
            ParamType::NonemptySet(_) => format!(r"\mathrm{{{}}}", NONEMPTY_SET),
            ParamType::FiniteSet(_) => format!(r"\mathrm{{{}}}", FINITE_SET),
            ParamType::Obj(o) => o.to_latex_string(),
        }
    }
}

impl Pow {
    pub fn to_latex_string(&self) -> String {
        format!(
            "{{{}}}^{{{}}}",
            self.base.to_latex_string(),
            self.exponent.to_latex_string()
        )
    }
}

impl PowerSet {
    pub fn to_latex_string(&self) -> String {
        format!(r"\mathcal{{P}}\left( {}\right)", self.set.to_latex_string())
    }
}

impl Proj {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            PROJ,
            self.set.to_latex_string(),
            self.dim.to_latex_string()
        )
    }
}

impl SketchStmt {
    pub fn to_latex_string(&self) -> String {
        if self.proof.is_empty() {
            return r"\text{\texttt{(empty proof)}}".to_string();
        }
        let rows: Vec<String> = self
            .proof
            .iter()
            .map(|st| format!(r"& \quad {}", st.to_latex_string()))
            .collect();
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl TryStmt {
    pub fn to_latex_string(&self) -> String {
        if self.proof.is_empty() {
            return r"\text{\texttt{(empty proof)}}".to_string();
        }
        let rows: Vec<String> = self
            .proof
            .iter()
            .map(|st| format!(r"& \quad {}", st.to_latex_string()))
            .collect();
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl Range {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            RANGE,
            self.start.to_latex_string(),
            self.end.to_latex_string()
        )
    }
}

impl RestrictFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \mathrel{{\$}} \mathrm{{{}}}\, {}",
            self.obj.to_latex_string(),
            RESTRICTS_TO,
            self.obj_can_restrict_to_fn_set.to_latex_string()
        )
    }
}

impl RunFileStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\ \texttt{{{}}}",
            RUN_FILE,
            latex_texttt_escape(&self.file_path)
        )
    }
}

impl SeqSet {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            SEQ,
            self.set.to_latex_string()
        )
    }
}

impl SetBuilder {
    pub fn to_latex_string(&self) -> String {
        let cond = self
            .facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ");
        format!(
            r"\left\{{ {} \in {} \,\middle|\, {} \right\}}",
            latex_local_ident(&self.param),
            self.param_set.to_latex_string(),
            cond
        )
    }
}

impl SetDiff {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            SET_DIFF,
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl SetMinus {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \setminus {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl Sub {
    pub fn to_latex_string(&self) -> String {
        format!(
            "{} - {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl SubsetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \subseteq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl SupersetFact {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \supseteq {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl Tuple {
    pub fn to_latex_string(&self) -> String {
        let inner = self
            .args
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left( {} \right)", inner)
    }
}

impl TupleDim {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            TUPLE_DIM,
            self.arg.to_latex_string()
        )
    }
}

impl Union {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"{} \cup {}",
            self.left.to_latex_string(),
            self.right.to_latex_string()
        )
    }
}

impl WitnessExistFact {
    pub fn to_latex_string(&self) -> String {
        let names = self
            .equal_tos
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        let facts = self
            .exist_fact_in_witness
            .facts()
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        let head = format!(
            r"\mathrm{{witness}}\ {} : {} \mathrm{{st}} \left\{{ {}\right\}}",
            names,
            self.exist_fact_in_witness
                .params_def_with_type()
                .to_latex_string(),
            facts
        );
        if self.proof.is_empty() {
            head
        } else {
            let mut rows = vec![format!(r"{} &", head)];
            for st in &self.proof {
                rows.push(format!(r"& \quad {}", st.to_latex_string()));
            }
            format!(
                "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                rows.join(" \\\\\n")
            )
        }
    }
}

impl WitnessNonemptySet {
    pub fn to_latex_string(&self) -> String {
        let head = format!(
            r"\mathrm{{witness}}\ {} {}",
            self.obj.to_latex_string(),
            self.set.to_latex_string()
        );
        if self.proof.is_empty() {
            head
        } else {
            let mut rows = vec![format!(r"{} &", head)];
            for st in &self.proof {
                rows.push(format!(r"& \quad {}", st.to_latex_string()));
            }
            format!(
                "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                rows.join(" \\\\\n")
            )
        }
    }
}

impl ImportGlobalModuleStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\ {}",
            IMPORT,
            latex_local_ident(&self.mod_name)
        )
    }
}

impl ImportRelativePathStmt {
    pub fn to_latex_string(&self) -> String {
        let path = latex_texttt_escape(&self.path);
        match &self.as_mod_name {
            Some(m) => format!(
                r"\operatorname{{{}}}\ \texttt{{{}}}\ \mathrm{{as}}\ {}",
                IMPORT,
                path,
                latex_local_ident(m)
            ),
            None => format!(r"\operatorname{{{}}}\ \texttt{{{}}}", IMPORT, path),
        }
    }
}

impl ImportStmt {
    pub fn to_latex_string(&self) -> String {
        match self {
            ImportStmt::ImportRelativePath(s) => s.to_latex_string(),
            ImportStmt::ImportGlobalModule(s) => s.to_latex_string(),
        }
    }
}

impl StandardSet {
    pub fn to_latex_string(&self) -> String {
        match self {
            StandardSet::N => r"\mathbb{N}".to_string(),
            StandardSet::NPos => r"\mathbb{N}_{>0}".to_string(),
            StandardSet::Z => r"\mathbb{Z}".to_string(),
            StandardSet::ZNeg => r"\mathbb{Z}_{<0}".to_string(),
            StandardSet::ZNz => r"\mathbb{Z}\setminus\{0\}".to_string(),
            StandardSet::Q => r"\mathbb{Q}".to_string(),
            StandardSet::QPos => r"\mathbb{Q}_{>0}".to_string(),
            StandardSet::QNeg => r"\mathbb{Q}_{<0}".to_string(),
            StandardSet::QNz => r"\mathbb{Q}\setminus\{0\}".to_string(),
            StandardSet::R => r"\mathbb{R}".to_string(),
            StandardSet::RPos => r"\mathbb{R}_{>0}".to_string(),
            StandardSet::RNeg => r"\mathbb{R}_{<0}".to_string(),
            StandardSet::RNz => r"\mathbb{R}\setminus\{0\}".to_string(),
        }
    }
}

impl Fact {
    pub fn to_latex_string(&self) -> String {
        match self {
            Fact::AtomicFact(x) => x.to_latex_string(),
            Fact::ExistFact(x) => x.to_latex_string(),
            Fact::OrFact(x) => x.to_latex_string(),
            Fact::AndFact(x) => x.to_latex_string(),
            Fact::ChainFact(x) => x.to_latex_string(),
            Fact::ForallFact(x) => x.to_latex_string(),
            Fact::ForallFactWithIff(x) => x.to_latex_string(),
            Fact::NotForall(x) => x.to_latex_string(),
        }
    }
}

impl AtomicFact {
    pub fn to_latex_string(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.to_latex_string(),
            AtomicFact::EqualFact(x) => x.to_latex_string(),
            AtomicFact::LessFact(x) => x.to_latex_string(),
            AtomicFact::GreaterFact(x) => x.to_latex_string(),
            AtomicFact::LessEqualFact(x) => x.to_latex_string(),
            AtomicFact::GreaterEqualFact(x) => x.to_latex_string(),
            AtomicFact::IsSetFact(x) => x.to_latex_string(),
            AtomicFact::IsNonemptySetFact(x) => x.to_latex_string(),
            AtomicFact::IsFiniteSetFact(x) => x.to_latex_string(),
            AtomicFact::InFact(x) => x.to_latex_string(),
            AtomicFact::IsCartFact(x) => x.to_latex_string(),
            AtomicFact::IsTupleFact(x) => x.to_latex_string(),
            AtomicFact::SubsetFact(x) => x.to_latex_string(),
            AtomicFact::SupersetFact(x) => x.to_latex_string(),
            AtomicFact::RestrictFact(x) => x.to_latex_string(),
            AtomicFact::NotRestrictFact(x) => x.to_latex_string(),
            AtomicFact::NotNormalAtomicFact(x) => x.to_latex_string(),
            AtomicFact::NotEqualFact(x) => x.to_latex_string(),
            AtomicFact::NotLessFact(x) => x.to_latex_string(),
            AtomicFact::NotGreaterFact(x) => x.to_latex_string(),
            AtomicFact::NotLessEqualFact(x) => x.to_latex_string(),
            AtomicFact::NotGreaterEqualFact(x) => x.to_latex_string(),
            AtomicFact::NotIsSetFact(x) => x.to_latex_string(),
            AtomicFact::NotIsNonemptySetFact(x) => x.to_latex_string(),
            AtomicFact::NotIsFiniteSetFact(x) => x.to_latex_string(),
            AtomicFact::NotInFact(x) => x.to_latex_string(),
            AtomicFact::NotIsCartFact(x) => x.to_latex_string(),
            AtomicFact::NotIsTupleFact(x) => x.to_latex_string(),
            AtomicFact::NotSubsetFact(x) => x.to_latex_string(),
            AtomicFact::NotSupersetFact(x) => x.to_latex_string(),
            AtomicFact::FnEqualInFact(f) => format!(
                r"\mathsf{{fn\_eq\_in}}({},{},{})",
                f.left.to_latex_string(),
                f.right.to_latex_string(),
                f.set.to_latex_string(),
            ),
            AtomicFact::FnEqualFact(f) => format!(
                r"\mathsf{{fn\_eq}}({},{})",
                f.left.to_latex_string(),
                f.right.to_latex_string(),
            ),
        }
    }
}

impl Obj {
    pub fn to_latex_string(&self) -> String {
        match self {
            Obj::Atom(AtomObj::Identifier(x)) => x.to_latex_string(),
            Obj::Atom(AtomObj::IdentifierWithMod(x)) => x.to_latex_string(),
            Obj::FnObj(x) => x.to_latex_string(),
            Obj::Number(x) => x.to_latex_string(),
            Obj::Add(x) => x.to_latex_string(),
            Obj::Sub(x) => x.to_latex_string(),
            Obj::Mul(x) => x.to_latex_string(),
            Obj::Div(x) => x.to_latex_string(),
            Obj::Mod(x) => x.to_latex_string(),
            Obj::Pow(x) => x.to_latex_string(),
            Obj::Abs(x) => x.to_latex_string(),
            Obj::Sqrt(x) => x.to_latex_string(),
            Obj::Log(x) => x.to_latex_string(),
            Obj::Max(x) => x.to_latex_string(),
            Obj::Min(x) => x.to_latex_string(),
            Obj::Union(x) => x.to_latex_string(),
            Obj::Intersect(x) => x.to_latex_string(),
            Obj::SetMinus(x) => x.to_latex_string(),
            Obj::SetDiff(x) => x.to_latex_string(),
            Obj::Cup(x) => x.to_latex_string(),
            Obj::Cap(x) => x.to_latex_string(),
            Obj::PowerSet(x) => x.to_latex_string(),
            Obj::GeneralCart(x) => x.to_latex_string(),
            Obj::ListSet(x) => x.to_latex_string(),
            Obj::SetBuilder(x) => x.to_latex_string(),
            Obj::FnSet(x) => x.to_latex_string(),
            Obj::AnonymousFn(x) => x.to_latex_string(),
            Obj::Cart(x) => x.to_latex_string(),
            Obj::CartDim(x) => x.to_latex_string(),
            Obj::Proj(x) => x.to_latex_string(),
            Obj::TupleDim(x) => x.to_latex_string(),
            Obj::Tuple(x) => x.to_latex_string(),
            Obj::Count(x) => x.to_latex_string(),
            Obj::FnRange(x) => x.to_latex_string(),
            Obj::FnRangeOn(x) => x.to_latex_string(),
            Obj::Replacement(x) => x.to_latex_string(),
            Obj::Sum(x) => x.to_latex_string(),
            Obj::SumOfFiniteSet(x) => x.to_latex_string(),
            Obj::Product(x) => x.to_latex_string(),
            Obj::ProductOfFiniteSet(x) => x.to_latex_string(),
            Obj::Range(x) => x.to_latex_string(),
            Obj::ClosedRange(x) => x.to_latex_string(),
            Obj::FiniteSeqSet(x) => x.to_latex_string(),
            Obj::SeqSet(x) => x.to_latex_string(),
            Obj::FiniteSeqListObj(x) => x.to_latex_string(),
            Obj::ObjAtIndex(x) => x.to_latex_string(),
            Obj::StandardSet(x) => x.to_latex_string(),
            Obj::StructObj(x) => latex_texttt_escape(&x.to_string()),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => latex_texttt_escape(&x.to_string()),
            Obj::InstantiatedTemplateObj(x) => latex_texttt_escape(&x.to_string()),
            Obj::OneSideInfinityIntervalObj(x) => x.to_latex_string(),
            Obj::IntervalObj(x) => x.to_latex_string(),
            Obj::Atom(AtomObj::Forall(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::Def(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::Exist(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::SetBuilder(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::FnSet(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::Induc(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::DefAlgo(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::DefStructField(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::TupleIndex(x)) => latex_local_ident(&x.name),
            Obj::Atom(AtomObj::CartIndex(x)) => latex_local_ident(&x.name),
            Obj::MatrixSet(x) => x.to_latex_string(),
            Obj::MatrixListObj(x) => x.to_latex_string(),
            Obj::MatrixAdd(x) => x.to_latex_string(),
            Obj::MatrixSub(x) => x.to_latex_string(),
            Obj::MatrixMul(x) => x.to_latex_string(),
            Obj::MatrixScalarMul(x) => x.to_latex_string(),
            Obj::MatrixPow(x) => x.to_latex_string(),
        }
    }
}

impl GeneralCart {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{general\_cart}}\left({}, {}, {}\right)",
            self.index_set.to_latex_string(),
            self.family_set.to_latex_string(),
            self.family_fn.to_latex_string()
        )
    }
}

impl Stmt {
    pub fn to_latex_string(&self) -> String {
        match self {
            Stmt::Fact(x) => x.to_latex_string(),
            Stmt::UnsafeStmt(UnsafeStmt::ProofDebtStmt(x)) => x.to_latex_string(),
            Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveByPreimageStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(x)) => x.to_latex_string(),
            Stmt::DefObjStmt(DefObjStmt::HaveTupleStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::DefObjStmt(DefObjStmt::HaveCartStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::DefObjStmt(DefObjStmt::HaveSeqStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::DefObjStmt(DefObjStmt::HaveFiniteSeqStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::DefObjStmt(DefObjStmt::HaveMatrixStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(x)) => x.to_latex_string(),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(x)) => x.to_latex_string(),
            Stmt::DefAliasStmt(DefAliasStmt::AliasPropStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::DefAliasStmt(DefAliasStmt::AliasThmStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::DefAlgoStmt(x) => x.to_latex_string(),
            Stmt::DefThmStmt(x) => latex_texttt_escape(&x.to_string()),
            Stmt::DefStrategyStmt(x) => latex_texttt_escape(&x.to_string()),
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(x)) => x.to_latex_string(),
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(x)) => x.to_latex_string(),
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::ImportStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::DoNothingStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::ClearStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::StopImportStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::RunFileStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::EvalStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::EvalByStmt(x)) => x.to_latex_string(),
            Stmt::Command(CommandStmt::UseStrategyStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::Command(CommandStmt::StopStrategyStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::Witness(WitnessStmt::WitnessExistFact(x)) => x.to_latex_string(),
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByCasesStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByContraStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByInducStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByForStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByExtensionStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByEnumerateRangeStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByClosedRangeAsCasesStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByTransitivePropStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::BySymmetricPropStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByReflexivePropStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByAntisymmetricPropStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByZornLemmaStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByRegularityAxiomStmt(x)) => x.to_latex_string(),
            Stmt::By(ByStmt::ByThmStmt(x)) => latex_texttt_escape(&x.to_string()),
        }
    }
}
