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
    } else if prop == SUBSET {
        Some(r"\subseteq")
    } else if prop == SUPERSET {
        Some(r"\supseteq")
    } else if prop == PROPER_SUBSET {
        Some(r"\subsetneq")
    } else if prop == PROPER_SUPERSET {
        Some(r"\supsetneq")
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
    for g in clause.set_bound_parameters.iter() {
        let set = fn_param_group_type_to_latex(g);
        for p in &g.params {
            slots.push(format!(r"{} \in {}", latex_local_ident(p.name()), set));
        }
    }
    let dom = clause
        .dom_facts
        .iter()
        .map(|f| f.syntax_rendering())
        .collect::<Vec<_>>()
        .join(r", ");
    let ret = clause.ret_set.syntax_rendering();
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

fn fn_param_group_type_to_latex(g: &SetBoundParameterGroup) -> String {
    g.set_obj().syntax_rendering()
}

impl AndChainAtomicFact {
    pub fn syntax_rendering(&self) -> String {
        match self {
            AndChainAtomicFact::AtomicFact(x) => x.syntax_rendering(),
            AndChainAtomicFact::AndFact(x) => x.syntax_rendering(),
            AndChainAtomicFact::ChainFact(x) => x.syntax_rendering(),
        }
    }
}

impl QuantifierFreeFact {
    pub fn syntax_rendering(&self) -> String {
        match self {
            QuantifierFreeFact::AtomicFact(x) => x.syntax_rendering(),
            QuantifierFreeFact::AndFact(x) => x.syntax_rendering(),
            QuantifierFreeFact::ChainFact(x) => x.syntax_rendering(),
            QuantifierFreeFact::OrFact(x) => x.syntax_rendering(),
        }
    }
}

impl AndFact {
    pub fn syntax_rendering(&self) -> String {
        self.facts
            .iter()
            .map(|a| a.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r" \land ")
    }
}

impl ChainFact {
    pub fn syntax_rendering(&self) -> String {
        if self.objs.is_empty() {
            return String::new();
        }
        let mut s = self.objs[0].syntax_rendering();
        for (i, obj) in self.objs[1..].iter().enumerate() {
            let pname = self.prop_names[i].to_string();
            let rhs = obj.syntax_rendering();
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
    pub fn syntax_rendering(&self) -> String {
        format!(r"\left| {} \right|", self.arg.syntax_rendering())
    }
}

impl Sin {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\sin\left({}\right)", self.arg.syntax_rendering())
    }
}

impl Arcsin {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\arcsin\left({}\right)", self.arg.syntax_rendering())
    }
}

impl Cos {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\cos\left({}\right)", self.arg.syntax_rendering())
    }
}

impl Tan {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\tan\left({}\right)", self.arg.syntax_rendering())
    }
}

impl Cot {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\cot\left({}\right)", self.arg.syntax_rendering())
    }
}

impl Sqrt {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\sqrt{{{}}}", self.arg.syntax_rendering())
    }
}

impl Add {
    pub fn syntax_rendering(&self) -> String {
        format!(
            "{} + {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl ByCasesStmt {
    pub fn syntax_rendering(&self) -> String {
        let goal = self
            .then_facts
            .iter()
            .map(|f| f.syntax_rendering())
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
                case.syntax_rendering()
            ));
            for st in proof {
                rows.push(format!(r"& \quad {}", st.syntax_rendering()));
            }
            if let Some(atom) = imposs {
                rows.push(format!(
                    r"\textbf{{\text{{Impossible.}}}} & {}",
                    atom.syntax_rendering()
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
    pub fn syntax_rendering(&self) -> String {
        let goal = self.to_prove.syntax_rendering();
        let mut rows = vec![format!(
            r"\text{{Proof by contradiction. Goal:}} & {}",
            goal
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        rows.push(format!(
            r"\textbf{{\text{{Contradiction.}}}} & {}",
            self.impossible_fact.syntax_rendering()
        ));
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByClosedRangeAsCasesStmt {
    pub fn syntax_rendering(&self) -> String {
        let a = self.closed_range.start.syntax_rendering();
        let b = self.closed_range.end.syntax_rendering();
        let x = self.element.syntax_rendering();
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
    pub fn syntax_rendering(&self) -> String {
        latex_texttt_escape(&self.to_string())
    }
}

impl ByEnumerateFiniteSetStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{Proof by exhaustive enumeration (finite cases).}} & {}",
            self.forall_fact.syntax_rendering()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByExtensionStmt {
    pub fn syntax_rendering(&self) -> String {
        let l = self.left.syntax_rendering();
        let r = self.right.syntax_rendering();
        let mut rows = vec![format!(
            r"\text{{\textbf{{By extensionality}}:}} & {}={} \Longleftrightarrow \bigl({}\subseteq {}\land {}\subseteq {}\bigr)\text{{.}}",
            l, r, l, r, r, l
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByForStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by for}}:}} & {}",
            self.forall_fact.syntax_rendering()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByTransitivePropStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by transitive_prop}}:}} & {}",
            self.forall_fact.syntax_rendering()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl BySymmetricPropStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by symmetric_prop}}:}} & {}",
            self.forall_fact.syntax_rendering()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByReflexivePropStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by reflexive_prop}}:}} & {}",
            self.forall_fact.syntax_rendering()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByZornLemmaStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by zorn_lemma:}}}} \text{{set }} {}, \text{{prop }} {}, \text{{prop }} {}, \text{{prop }} {}",
            self.set.syntax_rendering(),
            latex_texttt_escape(&self.prop_name.to_string()),
            latex_texttt_escape(&self.upper_bound_prop_name.to_string()),
            latex_texttt_escape(&self.maximal_prop_name.to_string())
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByAxiomOfChoiceStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![format!(
            r"\text{{\textbf{{by axiom_of_choice:}}}} \text{{set }} {}",
            self.family.syntax_rendering()
        )];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ByRegularityAxiomStmt {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\text{{\textbf{{by regularity_axiom}}}}({})",
            self.set.syntax_rendering()
        )
    }
}

impl ByInducStmt {
    pub fn syntax_rendering(&self) -> String {
        let goals = self
            .to_prove
            .iter()
            .map(|f| f.syntax_rendering())
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
            latex_local_ident(self.param()),
            self.induc_from.syntax_rendering(),
            goals
        )];
        rows.push(r"\text{?} &".to_string());
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl BigIntersect {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\bigcap\left( {}\right)", self.left.syntax_rendering())
    }
}

impl Cart {
    pub fn syntax_rendering(&self) -> String {
        let inner = self
            .args
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\operatorname{{{}}}\left( {}\right)", CART, inner)
    }
}

impl CartDim {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            CART_DIM,
            self.set.syntax_rendering()
        )
    }
}

impl ClaimStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![
            r"\text{\textbf{claim}:} &".to_string(),
            format!(r"\text{{\textbf{{?}}}} & {}", self.fact.syntax_rendering()),
        ];
        for st in &self.proof {
            rows.push(format!(r"& \quad {}", st.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl ExampleStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows = vec![
            r"\text{\textbf{example}:} &".to_string(),
            format!(r"\text{{\textbf{{?}}}} & {}", self.fact.syntax_rendering()),
        ];
        for statement in &self.proof {
            rows.push(format!(r"& \quad {}", statement.syntax_rendering()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n+")
        )
    }
}

impl ClosedRange {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            CLOSED_RANGE,
            self.start.syntax_rendering(),
            self.end.syntax_rendering()
        )
    }
}

impl IntervalObj {
    pub fn syntax_rendering(&self) -> String {
        let (left, right) = match self {
            IntervalObj::LeftOpenRightOpen(_) => ("(", ")"),
            IntervalObj::LeftOpenRightClosed(_) => ("(", "]"),
            IntervalObj::LeftClosedRightOpen(_) => ("[", ")"),
            IntervalObj::LeftClosedRightClosed(_) => ("[", "]"),
        };
        format!(
            r"\left{} {}, {} \right{}",
            left,
            self.start().syntax_rendering(),
            self.end().syntax_rendering(),
            right
        )
    }
}

impl OneSideInfinityIntervalObj {
    pub fn syntax_rendering(&self) -> String {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(_) => {
                format!(
                    r"\left( {}, \infty \right)",
                    self.start().syntax_rendering()
                )
            }
            OneSideInfinityIntervalObj::LeftClosed(_) => {
                format!(
                    r"\left[ {}, \infty \right)",
                    self.start().syntax_rendering()
                )
            }
            OneSideInfinityIntervalObj::RightOpen(_) => {
                format!(
                    r"\left( -\infty, {} \right)",
                    self.start().syntax_rendering()
                )
            }
            OneSideInfinityIntervalObj::RightClosed(_) => {
                format!(
                    r"\left( -\infty, {} \right]",
                    self.start().syntax_rendering()
                )
            }
        }
    }
}

impl FiniteSetSize {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            FINITE_SET_SIZE,
            self.set.syntax_rendering()
        )
    }
}

impl FnRange {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            FN_RANGE,
            self.function.syntax_rendering()
        )
    }
}

impl Replacement {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            REPLACEMENT,
            self.prop_name,
            self.source_set.syntax_rendering()
        )
    }
}

impl Sum {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {} \right)",
            SUM,
            self.start.syntax_rendering(),
            self.end.syntax_rendering(),
            self.func.syntax_rendering()
        )
    }
}

impl SumOfFiniteSet {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FINITE_SET_SUM,
            self.set.syntax_rendering(),
            self.func.syntax_rendering()
        )
    }
}

impl ProductOfFiniteSet {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FINITE_SET_PRODUCT,
            self.set.syntax_rendering(),
            self.func.syntax_rendering()
        )
    }
}

impl Product {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {} \right)",
            PRODUCT,
            self.start.syntax_rendering(),
            self.end.syntax_rendering(),
            self.func.syntax_rendering()
        )
    }
}

impl Reduce {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {}, {}, {} \right)",
            REDUCE,
            self.start.syntax_rendering(),
            self.end.syntax_rendering(),
            self.func.syntax_rendering(),
            self.op.syntax_rendering(),
            self.seed.syntax_rendering()
        )
    }
}

impl FiniteSetReduce {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {}, {} \right)",
            FINITE_SET_REDUCE,
            self.set.syntax_rendering(),
            self.func.syntax_rendering(),
            self.op.syntax_rendering(),
            self.seed.syntax_rendering()
        )
    }
}

impl BigUnion {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\bigcup\left( {}\right)", self.left.syntax_rendering())
    }
}

impl IndexUnion {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{index\_union}}\left({}, {}, {}\right)",
            self.index_set.syntax_rendering(),
            self.ambient_set.syntax_rendering(),
            self.family_fn.syntax_rendering()
        )
    }
}

impl IndexIntersect {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{index\_intersect}}\left({}, {}, {}\right)",
            self.index_set.syntax_rendering(),
            self.ambient_set.syntax_rendering(),
            self.family_fn.syntax_rendering()
        )
    }
}

impl DefAbstractPropStmt {
    pub fn syntax_rendering(&self) -> String {
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
    pub fn syntax_rendering(&self) -> String {
        let ps = self
            .param_names()
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
                c.condition.syntax_rendering(),
                c.return_stmt.value.syntax_rendering()
            ));
        }
        if let Some(dr) = &self.default_return {
            rows.push(format!(
                r"& \quad \mathrm{{default}}\ \texttt{{:}}\ {}",
                dr.value.syntax_rendering()
            ));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl TrustHaveStmt {
    pub fn syntax_rendering(&self) -> String {
        match self.facts.len() {
            0 => format!(
                r"\operatorname{{{}}}\, {}",
                format!("{} {}", TRUST, HAVE),
                self.param_def.syntax_rendering()
            ),
            _ => {
                let mut rows = vec![format!(
                    r"\operatorname{{{}}}\, {}",
                    format!("{} {}", TRUST, HAVE),
                    self.param_def.syntax_rendering()
                )];
                for fact in &self.facts {
                    rows.push(format!(r"& \quad {}", fact.syntax_rendering()));
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
    pub fn syntax_rendering(&self) -> String {
        match self.iff_facts.len() {
            0 => format!(
                r"\operatorname{{{}}}\, {}\left\{{ {} \right\}}",
                PROP,
                latex_local_ident(&self.name),
                self.typed_parameters.syntax_rendering()
            ),
            _ => {
                let mut rows = vec![format!(
                    r"\operatorname{{{}}}\, {}\left\{{ {} \right\}} \texttt{{:}}",
                    PROP,
                    latex_local_ident(&self.name),
                    self.typed_parameters.syntax_rendering()
                )];
                for fact in &self.iff_facts {
                    rows.push(format!(r"& \quad {}", fact.syntax_rendering()));
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
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\frac{{{}}}{{{}}}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl EqualFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            "{} = {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl EvalStmt {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\, {}",
            EVAL,
            self.obj_to_eval.syntax_rendering()
        )
    }
}

impl ExistFact {
    pub fn syntax_rendering(&self) -> String {
        let head = if self.is_not_exist() {
            r"\nexists"
        } else if self.is_exist_unique() {
            r"\exists!"
        } else {
            r"\exists"
        };
        let params = self.typed_parameters().syntax_rendering();
        let facts = self
            .facts()
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r", ");
        format!(
            r"{}\, \left( {}\right)\, \mathrm{{st}}\, \left\{{ {} \right\}}",
            head, params, facts
        )
    }
}

impl ExistOrAndChainAtomicFact {
    pub fn syntax_rendering(&self) -> String {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(x) => x.syntax_rendering(),
            ExistOrAndChainAtomicFact::AndFact(x) => x.syntax_rendering(),
            ExistOrAndChainAtomicFact::ChainFact(x) => x.syntax_rendering(),
            ExistOrAndChainAtomicFact::OrFact(x) => x.syntax_rendering(),
            ExistOrAndChainAtomicFact::ExistFact(x) => x.syntax_rendering(),
        }
    }
}

impl FiniteSeqListObj {
    pub fn syntax_rendering(&self) -> String {
        let inner = self
            .objs
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left[ {} \right]", inner)
    }
}

impl FiniteSeqSet {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            FINITE_SEQ,
            self.set.syntax_rendering(),
            self.n.syntax_rendering()
        )
    }
}

impl FnObj {
    pub fn syntax_rendering(&self) -> String {
        let head = match self.head.as_ref() {
            FnObjHead::Identifier(i) => i.syntax_rendering(),
            FnObjHead::IdentifierWithMod(i) => i.syntax_rendering(),
            FnObjHead::Bound(p) => latex_local_ident(p.name()),
            FnObjHead::AnonymousFnLiteral(a) => a.syntax_rendering(),
            FnObjHead::FiniteSeqListObj(v) => v.syntax_rendering(),
            FnObjHead::ObjAtIndex(v) => v.syntax_rendering(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => latex_texttt_escape(&v.to_string()),
            FnObjHead::InstantiatedTemplateObj(t) => latex_texttt_escape(&t.to_string()),
            FnObjHead::MatrixOperator(matrix) => {
                format!("\\left({}\\right)", matrix.syntax_rendering())
            }
        };
        let mut s = head;
        for group in self.body.iter() {
            let inner = group
                .iter()
                .map(|o| o.syntax_rendering())
                .collect::<Vec<_>>()
                .join(", ");
            s.push_str(&format!(r"\left( {} \right)", inner));
        }
        s
    }
}

impl AnonymousFn {
    pub fn syntax_rendering(&self) -> String {
        let mut slots: Vec<String> = Vec::new();
        for g in self.body.set_bound_parameters.iter() {
            let set = fn_param_group_type_to_latex(g);
            for p in &g.params {
                slots.push(format!(r"{} \in {}", latex_local_ident(p.name()), set));
            }
        }
        let dom = self
            .body
            .dom_facts
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r", ");
        let ret = self.body.ret_set.syntax_rendering();
        let body = self.equal_to.syntax_rendering();
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
    pub fn syntax_rendering(&self) -> String {
        let mut slots: Vec<String> = Vec::new();
        for g in self.body.set_bound_parameters.iter() {
            let set = fn_param_group_type_to_latex(g);
            for p in &g.params {
                slots.push(format!(r"{} \in {}", latex_local_ident(p.name()), set));
            }
        }
        let dom = self
            .body
            .dom_facts
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r", ");
        let ret = self.body.ret_set.syntax_rendering();
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
    pub fn syntax_rendering(&self) -> String {
        let params = self.typed_parameters.syntax_rendering();
        let then = self
            .then_facts
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r" \land ");
        if self.dom_facts.is_empty() {
            format!(r"\forall \left( {}\right),\, {}", params, then)
        } else {
            let dom = self
                .dom_facts
                .iter()
                .map(|f| f.syntax_rendering())
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
    pub fn syntax_rendering(&self) -> String {
        let iff = self
            .iff_facts
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r" \land ");
        format!(
            r"{}\, \Longleftrightarrow\, \left( {}\right)",
            self.forall_fact.syntax_rendering(),
            iff
        )
    }
}

impl NotForallFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg\, \left( {}\right)",
            self.forall_fact.syntax_rendering()
        )
    }
}

impl GreaterEqualFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \geq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl GreaterFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            "{} > {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl ObtainObjFromExistFact {
    pub fn syntax_rendering(&self) -> String {
        let names = self
            .equal_tos
            .iter()
            .map(|binding| latex_local_ident(binding.name()))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"\mathrm{{have}}\ \mathrm{{by}}\ {} : {}",
            self.fact.syntax_rendering(),
            names
        )
    }
}

impl ObtainObjFromAtomicFact {
    pub fn syntax_rendering(&self) -> String {
        let names = self
            .equal_tos
            .iter()
            .map(|binding| latex_local_ident(binding.name()))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"\mathrm{{have}}\ \mathrm{{by}}\ {} : {}",
            self.fact.syntax_rendering(),
            names
        )
    }
}

impl ObtainObjFromThm {
    pub fn syntax_rendering(&self) -> String {
        latex_texttt_escape(&self.to_string())
    }
}

impl HaveFnByInducStmt {
    pub fn syntax_rendering(&self) -> String {
        let mut rows: Vec<String> = Vec::new();
        rows.push(format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ {} \quad \mathrm{{by}}\ \mathrm{{induc}}\ {} \ \mathrm{{from}}\ {}",
            latex_local_ident(self.name()),
            fn_set_clause_latex(&self.fn_set_clause),
            self.measure.syntax_rendering(),
            self.lower_bound.syntax_rendering(),
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
                    c.case_fact.syntax_rendering(),
                    eq.syntax_rendering()
                )),
                HaveFnByInducCaseBody::NestedCases(nested) => {
                    rows.push(format!(
                        r"& {} \mathrm{{case}}\ {} \texttt{{:}}",
                        pad,
                        c.case_fact.syntax_rendering()
                    ));
                    Self::push_case_rows(rows, nested, indent + 1);
                }
            }
        }
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn syntax_rendering(&self) -> String {
        let head = format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ \mathrm{{by}}\ \mathrm{{cases}}\texttt{{:}}",
            latex_local_ident(self.name())
        );
        let clause = fn_set_clause_latex(&self.fn_set_clause);
        let mut rows = vec![format!(r"{} & {}", head, clause)];
        for (i, case) in self.cases.iter().enumerate() {
            rows.push(format!(
                r"& \quad \mathrm{{case}}\ {} \texttt{{:}}\ {}",
                case.syntax_rendering(),
                self.equal_tos[i].syntax_rendering()
            ));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl HaveFnEqualStmt {
    pub fn syntax_rendering(&self) -> String {
        let fn_set_clause = FnSetClause::new(
            self.equal_to_anonymous_fn.body.set_bound_parameters.clone(),
            self.equal_to_anonymous_fn.body.dom_facts.clone(),
            (*self.equal_to_anonymous_fn.body.ret_set).clone(),
        )
        .expect("anonymous function signature was already validated");
        format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ {} {}",
            latex_local_ident(self.name()),
            fn_set_clause_latex(&fn_set_clause),
            self.equal_to_anonymous_fn.equal_to.syntax_rendering()
        )
    }
}

impl HaveFnByForallExistUniqueStmt {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ \mathrm{{as}}\ \mathrm{{set}}:\ {}",
            latex_local_ident(self.fn_name()),
            self.forall.syntax_rendering()
        )
    }
}

impl HaveObjEqualStmt {
    pub fn syntax_rendering(&self) -> String {
        let rhs = self
            .objs_equal_to
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"\mathrm{{have}}\ {} = {}",
            self.param_def.syntax_rendering(),
            rhs
        )
    }
}

impl LetObjStmt {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\mathrm{{let}}\ {} = {}",
            latex_local_ident(self.name()),
            self.value.syntax_rendering()
        )
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\mathrm{{have}}\ {}", self.param_def.syntax_rendering())
    }
}

impl HaveObjByExistFactsStmt {
    pub fn syntax_rendering(&self) -> String {
        let facts = self
            .facts
            .iter()
            .map(|fact| fact.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r"; ");
        format!(
            r"\mathrm{{have}}\ {} : \left\{{ {} \right\}}",
            self.param_def.syntax_rendering(),
            facts
        )
    }
}

impl Identifier {
    pub fn syntax_rendering(&self) -> String {
        latex_local_ident(&self.name)
    }
}

impl IdentifierWithMod {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{}\mathbin{{\mathrm{{::}}}}{}",
            latex_local_ident(&self.mod_name),
            latex_local_ident(&self.name)
        )
    }
}

impl AtomicName {
    pub fn syntax_rendering(&self) -> String {
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
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \in {}",
            self.element.syntax_rendering(),
            self.set.syntax_rendering()
        )
    }
}

impl Intersect {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \cap {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl IsCartFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_CART,
            self.set.syntax_rendering()
        )
    }
}

impl IsFiniteSetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_FINITE_SET,
            self.set.syntax_rendering()
        )
    }
}

impl IsNonemptySetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_NONEMPTY_SET,
            self.set.syntax_rendering()
        )
    }
}

impl IsSetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_SET,
            self.set.syntax_rendering()
        )
    }
}

impl IsTupleFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\$ \mathrm{{{}}}\left( {}\right)",
            IS_TUPLE,
            self.set.syntax_rendering()
        )
    }
}

impl TrustStmt {
    pub fn syntax_rendering(&self) -> String {
        if self.facts.len() == 1 {
            format!(
                r"\operatorname{{{}}} {}",
                TRUST,
                self.facts[0].syntax_rendering()
            )
        } else {
            let rows = self
                .facts
                .iter()
                .map(|fact| format!("& {}", fact.syntax_rendering()))
                .collect::<Vec<_>>()
                .join(" \\\\\n");
            format!(
                r"\operatorname{{{}}}\colon \begin{{aligned}}{}\end{{aligned}}",
                TRUST, rows
            )
        }
    }
}

impl LessEqualFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \leq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl LessFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            "{} < {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl ListSet {
    pub fn syntax_rendering(&self) -> String {
        let inner = self
            .list
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left\{{ {} \right\}}", inner)
    }
}

impl Log {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\log_{{{}}} \left( {} \right)",
            self.base.syntax_rendering(),
            self.arg.syntax_rendering()
        )
    }
}

impl MatrixAdd {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.left.syntax_rendering(),
            latex_texttt_escape(MATRIX_ADD),
            self.right.syntax_rendering()
        )
    }
}

impl MatrixListObj {
    pub fn syntax_rendering(&self) -> String {
        let rows = self
            .rows
            .iter()
            .map(|row| {
                let inner = row
                    .iter()
                    .map(|o| o.syntax_rendering())
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
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.left.syntax_rendering(),
            latex_texttt_escape(MATRIX_MUL),
            self.right.syntax_rendering()
        )
    }
}

impl MatrixPow {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.base.syntax_rendering(),
            latex_texttt_escape(MATRIX_POW),
            self.exponent.syntax_rendering()
        )
    }
}

impl MatrixScalarMul {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.scalar.syntax_rendering(),
            latex_texttt_escape(MATRIX_SCALAR_MUL),
            self.matrix.syntax_rendering()
        )
    }
}

impl MatrixSet {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {}, {} \right)",
            MATRIX,
            self.set.syntax_rendering(),
            self.row_len.syntax_rendering(),
            self.col_len.syntax_rendering()
        )
    }
}

impl MatrixSub {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \mathbin{{\mathrm{{{}}}}} {}",
            self.left.syntax_rendering(),
            latex_texttt_escape(MATRIX_SUB),
            self.right.syntax_rendering()
        )
    }
}

impl FiniteSetMax {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\max \left( {} \right)", self.set.syntax_rendering())
    }
}

impl FiniteSetMin {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\min \left( {} \right)", self.set.syntax_rendering())
    }
}

impl Mod {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\left( {} \mathbin{{\mathrm{{mod}}}} {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Quot {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{quot}}\left( {}, {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Gcd {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\gcd\left( {}, {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Lcm {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{lcm}}\left( {}, {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Floor {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\left\lfloor {} \right\rfloor",
            self.arg.syntax_rendering()
        )
    }
}

impl Ceil {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\left\lceil {} \right\rceil", self.arg.syntax_rendering())
    }
}

impl Min {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\min\left( {}, {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Max {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\max\left( {}, {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Exp {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\exp\left( {} \right)", self.arg.syntax_rendering())
    }
}

impl Ln {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\ln\left( {} \right)", self.arg.syntax_rendering())
    }
}

impl Sign {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{sgn}}\left( {} \right)",
            self.arg.syntax_rendering()
        )
    }
}

impl Factorial {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\left( {} \right)!", self.arg.syntax_rendering())
    }
}

impl Mul {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{0} \cdot {1}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NormalAtomicFact {
    pub fn syntax_rendering(&self) -> String {
        if let AtomicName::WithoutMod(name) = &self.predicate {
            if name == PRIME && self.body.len() == 1 {
                return format!(
                    r"\operatorname{{prime}}\left( {} \right)",
                    self.body[0].syntax_rendering()
                );
            }
            if name == COPRIME && self.body.len() == 2 {
                return format!(
                    r"\operatorname{{coprime}}\left( {}, {} \right)",
                    self.body[0].syntax_rendering(),
                    self.body[1].syntax_rendering()
                );
            }
            if self.body.len() == 2 && matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET) {
                let operator = if name == PROPER_SUBSET {
                    r"\subsetneq"
                } else {
                    r"\supsetneq"
                };
                return format!(
                    r"{} {} {}",
                    self.body[0].syntax_rendering(),
                    operator,
                    self.body[1].syntax_rendering()
                );
            }
        }
        let pred = self.predicate.syntax_rendering();
        let args = self
            .body
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\$ {}\left( {}\right)", pred, args)
    }
}

impl NotEqualFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \neq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NotGreaterEqualFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \ngeq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NotGreaterFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \ngtr {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NotInFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \notin {}",
            self.element.syntax_rendering(),
            self.set.syntax_rendering()
        )
    }
}

impl NotIsCartFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_CART,
            self.set.syntax_rendering()
        )
    }
}

impl NotIsFiniteSetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_FINITE_SET,
            self.set.syntax_rendering()
        )
    }
}

impl NotIsNonemptySetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_NONEMPTY_SET,
            self.set.syntax_rendering()
        )
    }
}

impl NotIsSetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_SET,
            self.set.syntax_rendering()
        )
    }
}

impl NotIsTupleFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( \$ \mathrm{{{}}}\left( {}\right) \right)",
            IS_TUPLE,
            self.set.syntax_rendering()
        )
    }
}

impl NotLessEqualFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \nleq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NotLessFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \nless {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NotNormalAtomicFact {
    pub fn syntax_rendering(&self) -> String {
        if let AtomicName::WithoutMod(name) = &self.predicate {
            if name == PRIME && self.body.len() == 1 {
                return format!(
                    r"\neg \operatorname{{prime}}\left( {} \right)",
                    self.body[0].syntax_rendering()
                );
            }
            if name == COPRIME && self.body.len() == 2 {
                return format!(
                    r"\neg \operatorname{{coprime}}\left( {}, {} \right)",
                    self.body[0].syntax_rendering(),
                    self.body[1].syntax_rendering()
                );
            }
            if self.body.len() == 2 && matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET) {
                let operator = if name == PROPER_SUBSET {
                    r"\subsetneq"
                } else {
                    r"\supsetneq"
                };
                return format!(
                    r"\neg \left( {} {} {} \right)",
                    self.body[0].syntax_rendering(),
                    operator,
                    self.body[1].syntax_rendering()
                );
            }
        }
        let pred = self.predicate.syntax_rendering();
        let args = self
            .body
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\neg \left( \$ {}\left( {}\right) \right)", pred, args)
    }
}

impl NotSubsetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( {} \subseteq {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl NotSupersetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\neg \left( {} \supseteq {} \right)",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Number {
    pub fn syntax_rendering(&self) -> String {
        self.normalized_value.clone()
    }
}

impl ObjAtIndex {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{}\left[ {} \right]",
            self.obj.syntax_rendering(),
            self.index.syntax_rendering()
        )
    }
}

impl OrFact {
    pub fn syntax_rendering(&self) -> String {
        self.facts
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r" \lor ")
    }
}

impl TypedParameterList {
    pub fn syntax_rendering(&self) -> String {
        self.groups
            .iter()
            .map(|g| g.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl TypedParameterGroup {
    pub fn syntax_rendering(&self) -> String {
        let names = self
            .params
            .iter()
            .map(|p| latex_local_ident(p.name()))
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"{}, {}", names, self.param_type.syntax_rendering())
    }
}

impl ParamType {
    pub fn syntax_rendering(&self) -> String {
        match self {
            ParamType::Set(_) => format!(r"\mathrm{{{}}}", SET),
            ParamType::NonemptySet(_) => format!(r"\mathrm{{{}}}", NONEMPTY_SET),
            ParamType::FiniteSet(_) => format!(r"\mathrm{{{}}}", FINITE_SET),
            ParamType::Obj(o) => o.syntax_rendering(),
        }
    }
}

impl Pow {
    pub fn syntax_rendering(&self) -> String {
        format!(
            "{{{}}}^{{{}}}",
            self.base.syntax_rendering(),
            self.exponent.syntax_rendering()
        )
    }
}

impl PowerSet {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\mathcal{{P}}\left( {}\right)",
            self.set.syntax_rendering()
        )
    }
}

impl Proj {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            PROJ,
            self.set.syntax_rendering(),
            self.dim.syntax_rendering()
        )
    }
}

impl SketchStmt {
    pub fn syntax_rendering(&self) -> String {
        if self.proof.is_empty() {
            return r"\text{\texttt{(empty proof)}}".to_string();
        }
        let rows: Vec<String> = self
            .proof
            .iter()
            .map(|st| format!(r"& \quad {}", st.syntax_rendering()))
            .collect();
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl TryStmt {
    pub fn syntax_rendering(&self) -> String {
        if self.proof.is_empty() {
            return r"\text{\texttt{(empty proof)}}".to_string();
        }
        let rows: Vec<String> = self
            .proof
            .iter()
            .map(|st| format!(r"& \quad {}", st.syntax_rendering()))
            .collect();
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl Range {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}, {} \right)",
            RANGE,
            self.start.syntax_rendering(),
            self.end.syntax_rendering()
        )
    }
}

impl SeqSet {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            SEQ,
            self.set.syntax_rendering()
        )
    }
}

impl SetBuilder {
    pub fn syntax_rendering(&self) -> String {
        let cond = self
            .facts
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(r" \land ");
        format!(
            r"\left\{{ {} \in {} \,\middle|\, {} \right\}}",
            latex_local_ident(self.param_name()),
            self.param_set.syntax_rendering(),
            cond
        )
    }
}

impl SetMinus {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \setminus {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Sub {
    pub fn syntax_rendering(&self) -> String {
        format!(
            "{} - {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl SubsetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \subseteq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl SupersetFact {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \supseteq {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl Tuple {
    pub fn syntax_rendering(&self) -> String {
        let inner = self
            .args
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\left( {} \right)", inner)
    }
}

impl TupleDim {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            TUPLE_DIM,
            self.arg.syntax_rendering()
        )
    }
}

impl Union {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"{} \cup {}",
            self.left.syntax_rendering(),
            self.right.syntax_rendering()
        )
    }
}

impl WitnessExistFact {
    pub fn syntax_rendering(&self) -> String {
        let names = self
            .equal_tos
            .iter()
            .map(|o| o.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        let facts = self
            .exist_fact_in_witness
            .facts()
            .iter()
            .map(|f| f.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        let head = format!(
            r"\mathrm{{witness}}\ {} : {} \mathrm{{st}} \left\{{ {}\right\}}",
            names,
            self.exist_fact_in_witness
                .typed_parameters()
                .syntax_rendering(),
            facts
        );
        if self.proof.is_empty() {
            head
        } else {
            let mut rows = vec![format!(r"{} &", head)];
            for st in &self.proof {
                rows.push(format!(r"& \quad {}", st.syntax_rendering()));
            }
            format!(
                "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                rows.join(" \\\\\n")
            )
        }
    }
}

impl WitnessAtomicFact {
    pub fn syntax_rendering(&self) -> String {
        let witnesses = self
            .witnesses
            .iter()
            .map(|object| object.syntax_rendering())
            .collect::<Vec<_>>()
            .join(", ");
        let head = format!(
            r"\mathrm{{witness}}\ {}\ \mathrm{{from}}\ {}",
            self.atomic_fact.syntax_rendering(),
            witnesses
        );
        if self.proof.is_empty() {
            head
        } else {
            let mut rows = vec![format!(r"{} &", head)];
            for stmt in &self.proof {
                rows.push(format!(r"& \quad {}", stmt.syntax_rendering()));
            }
            format!(
                "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                rows.join(" \\\\\n")
            )
        }
    }
}

impl WitnessNonemptySet {
    pub fn syntax_rendering(&self) -> String {
        let head = format!(
            r"\mathrm{{witness}}\ {} {}",
            self.obj.syntax_rendering(),
            self.set.syntax_rendering()
        );
        if self.proof.is_empty() {
            head
        } else {
            let mut rows = vec![format!(r"{} &", head)];
            for st in &self.proof {
                rows.push(format!(r"& \quad {}", st.syntax_rendering()));
            }
            format!(
                "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
                rows.join(" \\\\\n")
            )
        }
    }
}

impl StandardSet {
    pub fn syntax_rendering(&self) -> String {
        match self {
            StandardSet::N => r"\mathbb{N}".to_string(),
            StandardSet::NPos => r"\mathbb{N}_{>0}".to_string(),
            StandardSet::Z => r"\mathbb{Z}".to_string(),
            StandardSet::ZNeg => r"\mathbb{Z}_{<0}".to_string(),
            StandardSet::ZStar => r"\mathbb{Z}\setminus\{0\}".to_string(),
            StandardSet::Q => r"\mathbb{Q}".to_string(),
            StandardSet::QPos => r"\mathbb{Q}_{>0}".to_string(),
            StandardSet::QNeg => r"\mathbb{Q}_{<0}".to_string(),
            StandardSet::QStar => r"\mathbb{Q}\setminus\{0\}".to_string(),
            StandardSet::R => r"\mathbb{R}".to_string(),
            StandardSet::C => r"\mathbb{C}".to_string(),
            StandardSet::RPos => r"\mathbb{R}_{>0}".to_string(),
            StandardSet::RNeg => r"\mathbb{R}_{<0}".to_string(),
            StandardSet::RStar => r"\mathbb{R}\setminus\{0\}".to_string(),
            StandardSet::CStar => r"\mathbb{C}\setminus\{0\}".to_string(),
        }
    }
}

impl ImaginaryUnit {
    pub fn syntax_rendering(&self) -> String {
        r"\mathrm{i}".to_string()
    }
}

impl RealPart {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{re}}\left( {} \right)",
            self.arg.syntax_rendering()
        )
    }
}

impl ImaginaryPart {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{img}}\left( {} \right)",
            self.arg.syntax_rendering()
        )
    }
}

impl ComplexAbs {
    pub fn syntax_rendering(&self) -> String {
        format!(r"\left| {} \right|", self.arg.syntax_rendering())
    }
}

impl Fact {
    pub fn syntax_rendering(&self) -> String {
        match self {
            Fact::AtomicFact(x) => x.syntax_rendering(),
            Fact::ExistFact(x) => x.syntax_rendering(),
            Fact::OrFact(x) => x.syntax_rendering(),
            Fact::AndFact(x) => x.syntax_rendering(),
            Fact::ChainFact(x) => x.syntax_rendering(),
            Fact::ForallFact(x) => x.syntax_rendering(),
            Fact::ForallFactWithIff(x) => x.syntax_rendering(),
            Fact::NotForall(x) => x.syntax_rendering(),
        }
    }
}

impl AtomicFact {
    pub fn syntax_rendering(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.syntax_rendering(),
            AtomicFact::EqualFact(x) => x.syntax_rendering(),
            AtomicFact::LessFact(x) => x.syntax_rendering(),
            AtomicFact::GreaterFact(x) => x.syntax_rendering(),
            AtomicFact::LessEqualFact(x) => x.syntax_rendering(),
            AtomicFact::GreaterEqualFact(x) => x.syntax_rendering(),
            AtomicFact::IsSetFact(x) => x.syntax_rendering(),
            AtomicFact::IsNonemptySetFact(x) => x.syntax_rendering(),
            AtomicFact::IsFiniteSetFact(x) => x.syntax_rendering(),
            AtomicFact::InFact(x) => x.syntax_rendering(),
            AtomicFact::IsCartFact(x) => x.syntax_rendering(),
            AtomicFact::IsTupleFact(x) => x.syntax_rendering(),
            AtomicFact::SubsetFact(x) => x.syntax_rendering(),
            AtomicFact::SupersetFact(x) => x.syntax_rendering(),
            AtomicFact::NotNormalAtomicFact(x) => x.syntax_rendering(),
            AtomicFact::NotEqualFact(x) => x.syntax_rendering(),
            AtomicFact::NotLessFact(x) => x.syntax_rendering(),
            AtomicFact::NotGreaterFact(x) => x.syntax_rendering(),
            AtomicFact::NotLessEqualFact(x) => x.syntax_rendering(),
            AtomicFact::NotGreaterEqualFact(x) => x.syntax_rendering(),
            AtomicFact::NotIsSetFact(x) => x.syntax_rendering(),
            AtomicFact::NotIsNonemptySetFact(x) => x.syntax_rendering(),
            AtomicFact::NotIsFiniteSetFact(x) => x.syntax_rendering(),
            AtomicFact::NotInFact(x) => x.syntax_rendering(),
            AtomicFact::NotIsCartFact(x) => x.syntax_rendering(),
            AtomicFact::NotIsTupleFact(x) => x.syntax_rendering(),
            AtomicFact::NotSubsetFact(x) => x.syntax_rendering(),
            AtomicFact::NotSupersetFact(x) => x.syntax_rendering(),
            AtomicFact::FnEqualInFact(f) => format!(
                r"\mathsf{{fn\_eq\_in}}({},{},{})",
                f.left.syntax_rendering(),
                f.right.syntax_rendering(),
                f.set.syntax_rendering(),
            ),
            AtomicFact::FnEqualFact(f) => format!(
                r"\mathsf{{fn\_eq}}({},{})",
                f.left.syntax_rendering(),
                f.right.syntax_rendering(),
            ),
        }
    }
}

impl Obj {
    pub fn syntax_rendering(&self) -> String {
        match self {
            Obj::Atom(AtomObj::Identifier(x)) => x.syntax_rendering(),
            Obj::Atom(AtomObj::IdentifierWithMod(x)) => x.syntax_rendering(),
            Obj::Atom(AtomObj::Bound(x)) => latex_local_ident(x.name()),
            Obj::FnObj(x) => x.syntax_rendering(),
            Obj::Number(x) => x.syntax_rendering(),
            Obj::EulerNumber(_) => r"\mathrm{e}".to_string(),
            Obj::Pi(_) => r"\pi".to_string(),
            Obj::ImaginaryUnit(x) => x.syntax_rendering(),
            Obj::Add(x) => x.syntax_rendering(),
            Obj::Sub(x) => x.syntax_rendering(),
            Obj::Mul(x) => x.syntax_rendering(),
            Obj::Div(x) => x.syntax_rendering(),
            Obj::Mod(x) => x.syntax_rendering(),
            Obj::Quot(x) => x.syntax_rendering(),
            Obj::Gcd(x) => x.syntax_rendering(),
            Obj::Lcm(x) => x.syntax_rendering(),
            Obj::Floor(x) => x.syntax_rendering(),
            Obj::Ceil(x) => x.syntax_rendering(),
            Obj::Min(x) => x.syntax_rendering(),
            Obj::Max(x) => x.syntax_rendering(),
            Obj::Exp(x) => x.syntax_rendering(),
            Obj::Ln(x) => x.syntax_rendering(),
            Obj::Sign(x) => x.syntax_rendering(),
            Obj::Factorial(x) => x.syntax_rendering(),
            Obj::Pow(x) => x.syntax_rendering(),
            Obj::Abs(x) => x.syntax_rendering(),
            Obj::Sin(x) => x.syntax_rendering(),
            Obj::Arcsin(x) => x.syntax_rendering(),
            Obj::Cos(x) => x.syntax_rendering(),
            Obj::Tan(x) => x.syntax_rendering(),
            Obj::Cot(x) => x.syntax_rendering(),
            Obj::RealPart(x) => x.syntax_rendering(),
            Obj::ImaginaryPart(x) => x.syntax_rendering(),
            Obj::ComplexAbs(x) => x.syntax_rendering(),
            Obj::Sqrt(x) => x.syntax_rendering(),
            Obj::Log(x) => x.syntax_rendering(),
            Obj::Union(x) => x.syntax_rendering(),
            Obj::Intersect(x) => x.syntax_rendering(),
            Obj::SetMinus(x) => x.syntax_rendering(),
            Obj::BigUnion(x) => x.syntax_rendering(),
            Obj::BigIntersect(x) => x.syntax_rendering(),
            Obj::IndexUnion(x) => x.syntax_rendering(),
            Obj::IndexIntersect(x) => x.syntax_rendering(),
            Obj::PowerSet(x) => x.syntax_rendering(),
            Obj::GeneralCart(x) => x.syntax_rendering(),
            Obj::ListSet(x) => x.syntax_rendering(),
            Obj::SetBuilder(x) => x.syntax_rendering(),
            Obj::FnSet(x) => x.syntax_rendering(),
            Obj::AnonymousFn(x) => x.syntax_rendering(),
            Obj::Cart(x) => x.syntax_rendering(),
            Obj::CartDim(x) => x.syntax_rendering(),
            Obj::Proj(x) => x.syntax_rendering(),
            Obj::TupleDim(x) => x.syntax_rendering(),
            Obj::Tuple(x) => x.syntax_rendering(),
            Obj::FiniteSetSize(x) => x.syntax_rendering(),
            Obj::FiniteSetMax(x) => x.syntax_rendering(),
            Obj::FiniteSetMin(x) => x.syntax_rendering(),
            Obj::FnRange(x) => x.syntax_rendering(),
            Obj::Replacement(x) => x.syntax_rendering(),
            Obj::Sum(x) => x.syntax_rendering(),
            Obj::SumOfFiniteSet(x) => x.syntax_rendering(),
            Obj::Product(x) => x.syntax_rendering(),
            Obj::ProductOfFiniteSet(x) => x.syntax_rendering(),
            Obj::Reduce(x) => x.syntax_rendering(),
            Obj::FiniteSetReduce(x) => x.syntax_rendering(),
            Obj::Range(x) => x.syntax_rendering(),
            Obj::ClosedRange(x) => x.syntax_rendering(),
            Obj::FiniteSeqSet(x) => x.syntax_rendering(),
            Obj::SeqSet(x) => x.syntax_rendering(),
            Obj::FiniteSeqListObj(x) => x.syntax_rendering(),
            Obj::ObjAtIndex(x) => x.syntax_rendering(),
            Obj::StandardSet(x) => x.syntax_rendering(),
            Obj::StructObj(x) => latex_texttt_escape(&x.to_string()),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => latex_texttt_escape(&x.to_string()),
            Obj::InstantiatedTemplateObj(x) => latex_texttt_escape(&x.to_string()),
            Obj::OneSideInfinityIntervalObj(x) => x.syntax_rendering(),
            Obj::IntervalObj(x) => x.syntax_rendering(),
            Obj::MatrixSet(x) => x.syntax_rendering(),
            Obj::MatrixListObj(x) => x.syntax_rendering(),
            Obj::MatrixAdd(x) => x.syntax_rendering(),
            Obj::MatrixSub(x) => x.syntax_rendering(),
            Obj::MatrixMul(x) => x.syntax_rendering(),
            Obj::MatrixScalarMul(x) => x.syntax_rendering(),
            Obj::MatrixPow(x) => x.syntax_rendering(),
        }
    }
}

impl GeneralCart {
    pub fn syntax_rendering(&self) -> String {
        format!(
            r"\operatorname{{general\_cart}}\left({}, {}, {}\right)",
            self.index_set.syntax_rendering(),
            self.family_set.syntax_rendering(),
            self.family_fn.syntax_rendering()
        )
    }
}

impl Stmt {
    pub fn syntax_rendering(&self) -> String {
        match self {
            Stmt::Fact(x) => x.syntax_rendering(),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(x)) => x.syntax_rendering(),
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::LetObjStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::ObtainObjFromAtomicFact(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::ObtainObjFromThm(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveByPreimageStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveFnByInducStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(x)) => {
                x.syntax_rendering()
            }
            Stmt::Definition(DefinitionStmt::HaveTupleStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::HaveCartStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::HaveSeqStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::Definition(DefinitionStmt::HaveFiniteSeqStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::HaveMatrixStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::DefPropStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::DefAlgoStmt(x)) => x.syntax_rendering(),
            Stmt::Definition(DefinitionStmt::DefThmStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::Definition(DefinitionStmt::AxiomStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::Definition(DefinitionStmt::DefStrategyStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::DefStructStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::DefTemplateStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::Definition(DefinitionStmt::DefSettingStmt(x)) => {
                latex_texttt_escape(&x.to_string())
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(x)) => x.syntax_rendering(),
            Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(x)) => x.syntax_rendering(),
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(x)) => x.syntax_rendering(),
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(x)) => x.syntax_rendering(),
            Stmt::Command(CommandStmt::EvalStmt(x)) => x.syntax_rendering(),
            Stmt::Witness(WitnessStmt::WitnessExistFact(x)) => x.syntax_rendering(),
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(x)) => x.syntax_rendering(),
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByCasesStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByContraStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByFiniteSetInducStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::By(ByStmt::ByInducStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByForStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByExtensionStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByEnumerateRangeStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByClosedRangeAsCasesStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByTransitivePropStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::BySymmetricPropStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByReflexivePropStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByZornLemmaStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByRegularityAxiomStmt(x)) => x.syntax_rendering(),
            Stmt::By(ByStmt::ByDefStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::By(ByStmt::ByStructDefStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::By(ByStmt::ByThmStmt(x)) => latex_texttt_escape(&x.to_string()),
            Stmt::ReleaseThmStmt(x) => latex_texttt_escape(&x.to_string()),
        }
    }
}
