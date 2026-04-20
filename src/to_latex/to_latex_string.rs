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
    for g in &clause.params_def_with_set {
        let set = g.set.to_latex_string();
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
        format!(r"\mathrm{{fn}}\left({}\right)\to {}", slots.join(r", "), ret)
    } else {
        format!(
            r"\mathrm{{fn}}\left({} \,\middle|\, {}\right)\to {}",
            slots.join(r", "),
            dom,
            ret
        )
    }
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
        rows.push(format!(
            r"\text{{Proof by cases. Goal:}} & {}",
            goal
        ));
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

impl ByEnumerateClosedRangeStmt {
    pub fn to_latex_string(&self) -> String {
        let a = self.closed_range.start.to_latex_string();
        let b = self.closed_range.end.to_latex_string();
        let x = self.element.to_latex_string();
        let row1 = format!(
            r"&\text{{\textbf{{By enumeration}} on the closed integer interval }} [\![ {0},{1}]\!]\text{{.}}",
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

impl ByFamilyStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By family}}:}} & \\text{{Use the set-theoretic definition of }} {}\\text{{; obtain the corresponding set characterization.}}\n\\end{{aligned}}",
            self.family_obj.to_latex_string()
        )
    }
}

impl ByFiniteSeqSetStmt {
    pub fn to_latex_string(&self) -> String {
        let o: Obj = self.finite_seq_set.clone().into();
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By finite sequence space}}:}} & \\text{{Use the set-theoretic definition of }} {}\\text{{; obtain the corresponding set characterization.}}\n\\end{{aligned}}",
            o.to_latex_string()
        )
    }
}

impl ByFnSetStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By fn set}}:}} & {} \\in {}\\\\\n& \\quad \\text{{Unfold this membership via the set-theoretic definition of the function space; obtain the corresponding facts.}}\n\\end{{aligned}}",
            self.func.to_latex_string(),
            self.fn_set.to_latex_string()
        )
    }
}

impl ByFnStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By fn}}:}} & \\text{{Use the graph / function definition of }} {}\\text{{.}}\n\\end{{aligned}}",
            self.function.to_latex_string()
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

impl ByInducStmt {
    pub fn to_latex_string(&self) -> String {
        let goals = self
            .to_prove
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r" \land ");
        let mut rows = vec![format!(
            r"\text{{\textbf{{by induc}} on }} {} \text{{ from }} {} \texttt{{:}} & {}",
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

impl ByMatrixSetStmt {
    pub fn to_latex_string(&self) -> String {
        let o: Obj = self.matrix_set.clone().into();
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By matrix space}}:}} & \\text{{Use the set-theoretic definition of }} {}\\text{{; obtain the corresponding set characterization.}}\n\\end{{aligned}}",
            o.to_latex_string()
        )
    }
}

impl BySeqSetStmt {
    pub fn to_latex_string(&self) -> String {
        let o: Obj = self.seq_set.clone().into();
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By sequence space}}:}} & \\text{{Use the set-theoretic definition of }} {}\\text{{; obtain the corresponding set characterization.}}\n\\end{{aligned}}",
            o.to_latex_string()
        )
    }
}

impl ByStructStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By struct}}:}} & \\text{{Use the set-theoretic definition of }} {}\\text{{; obtain the corresponding instance-set characterization.}}\n\\end{{aligned}}",
            self.struct_obj.to_latex_string()
        )
    }
}

impl ByTupleStmt {
    pub fn to_latex_string(&self) -> String {
        format!(
            "\\begin{{aligned}}\n\\text{{\\textbf{{By tuple}}:}} & \\text{{Use the set-theoretic ordered-pair / tuple encoding for }} {}\\text{{; obtain the corresponding set-theoretic facts.}}\n\\end{{aligned}}",
            self.obj.to_latex_string()
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
            format!(r"\text{{\textbf{{claim}}:}} & {}", self.fact.to_latex_string()),
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

impl Count {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            COUNT,
            self.set.to_latex_string()
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

impl Choose {
    pub fn to_latex_string(&self) -> String {
        format!(
            r"\operatorname{{{}}}\left( {}\right)",
            CHOOSE,
            self.set.to_latex_string()
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
        let mut rows =
            vec![format!(r"\operatorname{{{}}}\, {}\left( {}\right) \texttt{{:}}", ALGO, latex_local_ident(&self.name), ps)];
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

impl DefFamilyStmt {
    pub fn to_latex_string(&self) -> String {
        let dom = self
            .dom_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r", ");
        format!(
            r"\operatorname{{{}}}\, {}\left( {} : {} \right) = {}",
            FAMILY,
            latex_local_ident(&self.name),
            self.params_def_with_type.to_latex_string(),
            dom,
            self.equal_to.to_latex_string()
        )
    }
}

impl DefLetStmt {
    pub fn to_latex_string(&self) -> String {
        match self.facts.len() {
            0 => format!(r"\operatorname{{{}}}\, {}", LET, self.param_def.to_latex_string()),
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

impl DefStructStmt {
    pub fn to_latex_string(&self) -> String {
        let implicit_prefix_len = self.param_defs.number_of_params();
        let mut rows = vec![format!(
            r"\operatorname{{{}}}\, {}\left( {}\right) \texttt{{:}}",
            STRUCT,
            latex_local_ident(&self.name),
            self.param_defs.to_latex_string()
        )];
        for (fname, pty) in self.fields.iter().skip(implicit_prefix_len) {
            rows.push(format!(
                r"& \quad {} : {}",
                latex_local_ident(fname),
                pty.to_latex_string()
            ));
        }
        rows.push(r"& \quad \Longleftrightarrow \texttt{:}".to_string());
        for fact in self.facts.iter().skip(implicit_prefix_len) {
            rows.push(format!(r"& \quad {}", fact.to_latex_string()));
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
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

impl ExistFact {
    pub fn to_latex_string(&self) -> String {
        let head = if self.is_exist_unique {
            r"\exists!"
        } else {
            r"\exists"
        };
        let params = self.params_def_with_type.to_latex_string();
        let facts = self
            .facts
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

impl FamilyObj {
    pub fn to_latex_string(&self) -> String {
        let head = self.name.to_latex_string();
        let args = self
            .params
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\operatorname{{{}}}\, {}\left( {}\right)", FAMILY, head, args)
    }
}

impl FieldAccess {
    pub fn to_latex_string(&self) -> String {
        let s = crate::obj::field_access_to_string(&self.name, &self.field);
        format!(r"\text{{{}}}", latex_texttt_escape(&s))
    }
}

impl FieldAccessWithMod {
    pub fn to_latex_string(&self) -> String {
        let s = crate::obj::field_access_with_mod_to_string(
            &self.mod_name,
            &self.name,
            &self.field,
        );
        format!(r"\text{{{}}}", latex_texttt_escape(&s))
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
            Atom::Identifier(i) => i.to_latex_string(),
            Atom::IdentifierWithMod(i) => i.to_latex_string(),
            Atom::FieldAccess(x) => x.to_latex_string(),
            Atom::FieldAccessWithMod(x) => x.to_latex_string(),
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

impl FnSet {
    pub fn to_latex_string(&self) -> String {
        let mut slots: Vec<String> = Vec::new();
        for g in &self.params_def_with_set {
            let set = g.set.to_latex_string();
            for p in &g.params {
                slots.push(format!(r"{} \in {}", latex_local_ident(p), set));
            }
        }
        let dom = self
            .dom_facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(r", ");
        let ret = self.ret_set.to_latex_string();
        if dom.is_empty() {
            format!(r"\mathrm{{fn}}\left({}\right)\to {}", slots.join(r", "), ret)
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
            r"\mathrm{{have}}\ \mathrm{{fn}}\ \mathrm{{by}}\ \mathrm{{induc}}\ \mathrm{{from}}\ {} \texttt{{:}}\ \mathrm{{fn}}\ {}\left( {} : {} \geq {} \right) {}",
            self.induc_from.to_latex_string(),
            latex_local_ident(&self.name),
            latex_local_ident(&self.param),
            Z,
            self.induc_from.to_latex_string(),
            self.ret_set.to_latex_string()
        ));
        for (i, eq) in self.special_cases_equal_tos.iter().enumerate() {
            rows.push(format!(
                r"& \quad \mathrm{{case}}\ {} : {}",
                i,
                eq.to_latex_string()
            ));
        }
        let n = self.special_cases_equal_tos.len();
        match &self.last_case {
            HaveFnByInducLastCase::EqualTo(eq) => {
                rows.push(format!(
                    r"& \quad \mathrm{{case}}\ \geq {} : {}",
                    n,
                    eq.to_latex_string()
                ));
            }
            HaveFnByInducLastCase::NestedCases(nc) => {
                rows.push(format!(r"& \quad \mathrm{{case}}\ \geq {} \texttt{{:}}", n));
                for c in nc {
                    rows.push(format!(
                        r"& \quad \quad \mathrm{{case}}\ {} : {}",
                        c.case_fact.to_latex_string(),
                        c.equal_to.to_latex_string()
                    ));
                }
            }
        }
        format!(
            "\\begin{{aligned}}\n{}\n\\end{{aligned}}",
            rows.join(" \\\\\n")
        )
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn to_latex_string(&self) -> String {
        let head = format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ \texttt{{=}} \texttt{{:}}",
            latex_local_ident(&self.name)
        );
        let clause = fn_set_clause_latex(&self.fn_set_clause);
        let mut rows = vec![format!(r"{} & {}", head, clause)];
        for (i, case) in self.cases.iter().enumerate() {
            rows.push(format!(
                r"& \quad \mathrm{{case}}\ {} \texttt{{:}}\ {} = {}",
                case.to_latex_string(),
                latex_local_ident(&self.name),
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
        format!(
            r"\mathrm{{have}}\ \mathrm{{fn}}\ {}\ {} {}",
            latex_local_ident(&self.name),
            fn_set_clause_latex(&self.fn_set_clause),
            self.equal_to.to_latex_string()
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

impl KnowStmt {
    pub fn to_latex_string(&self) -> String {
        if self.facts.len() == 1 {
            format!(
                r"\operatorname{{{}}} {}",
                KNOW,
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
                KNOW, rows
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
            RESTRICT,
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
            ParamType::Struct(s) => s.to_latex_string(),
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

impl ProveStmt {
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
            RESTRICT,
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

impl StructObj {
    pub fn to_latex_string(&self) -> String {
        let head = self.name.to_latex_string();
        let args = self
            .args
            .iter()
            .map(|o| o.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        format!(r"\operatorname{{{}}}\, {}\left( {}\right)", STRUCT, head, args)
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
            .facts
            .iter()
            .map(|f| f.to_latex_string())
            .collect::<Vec<_>>()
            .join(", ");
        let head = format!(
            r"\mathrm{{witness}}\ {} : {} \mathrm{{st}} \left\{{ {}\right\}}",
            names,
            self.exist_fact_in_witness
                .params_def_with_type
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
        match &self.as_mod_name {
            Some(m) => format!(
                r"\operatorname{{{}}}\ {}\ \mathrm{{as}}\ {}",
                IMPORT,
                latex_local_ident(&self.mod_name),
                latex_local_ident(m)
            ),
            None => format!(
                r"\operatorname{{{}}}\ {}",
                IMPORT,
                latex_local_ident(&self.mod_name)
            ),
        }
    }
}

impl ImportRelativePathStmt {
    pub fn to_latex_string(&self) -> String {
        let path = latex_texttt_escape(&self.path);
        match &self.as_mod_name {
            Some(m) => format!(
                r"\operatorname{{{}}}\ \texttt{{{}}}\ \mathrm{{as}}\ {}",
                IMPORT, path, latex_local_ident(m)
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

impl IdentifierOrIdentifierWithMod {
    pub fn to_latex_string(&self) -> String {
        match self {
            IdentifierOrIdentifierWithMod::Identifier(x) => x.to_latex_string(),
            IdentifierOrIdentifierWithMod::IdentifierWithMod(x) => x.to_latex_string(),
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
        }
    }
}

impl Obj {
    pub fn to_latex_string(&self) -> String {
        match self {
            Obj::Identifier(x) => x.to_latex_string(),
            Obj::IdentifierWithMod(x) => x.to_latex_string(),
            Obj::FieldAccess(x) => x.to_latex_string(),
            Obj::FieldAccessWithMod(x) => x.to_latex_string(),
            Obj::FnObj(x) => x.to_latex_string(),
            Obj::Number(x) => x.to_latex_string(),
            Obj::Add(x) => x.to_latex_string(),
            Obj::Sub(x) => x.to_latex_string(),
            Obj::Mul(x) => x.to_latex_string(),
            Obj::Div(x) => x.to_latex_string(),
            Obj::Mod(x) => x.to_latex_string(),
            Obj::Pow(x) => x.to_latex_string(),
            Obj::Abs(x) => x.to_latex_string(),
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
            Obj::ListSet(x) => x.to_latex_string(),
            Obj::SetBuilder(x) => x.to_latex_string(),
            Obj::FnSet(x) => x.to_latex_string(),
            Obj::Cart(x) => x.to_latex_string(),
            Obj::CartDim(x) => x.to_latex_string(),
            Obj::Proj(x) => x.to_latex_string(),
            Obj::TupleDim(x) => x.to_latex_string(),
            Obj::Tuple(x) => x.to_latex_string(),
            Obj::Count(x) => x.to_latex_string(),
            Obj::Range(x) => x.to_latex_string(),
            Obj::ClosedRange(x) => x.to_latex_string(),
            Obj::FiniteSeqSet(x) => x.to_latex_string(),
            Obj::SeqSet(x) => x.to_latex_string(),
            Obj::FiniteSeqListObj(x) => x.to_latex_string(),
            Obj::Choose(x) => x.to_latex_string(),
            Obj::ObjAtIndex(x) => x.to_latex_string(),
            Obj::StandardSet(x) => x.to_latex_string(),
            Obj::FamilyObj(x) => x.to_latex_string(),
            Obj::StructObj(x) => x.to_latex_string(),
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

impl Stmt {
    pub fn to_latex_string(&self) -> String {
        match self {
            Stmt::Fact(x) => x.to_latex_string(),
            Stmt::DefLetStmt(x) => x.to_latex_string(),
            Stmt::DefPropStmt(x) => x.to_latex_string(),
            Stmt::DefAbstractPropStmt(x) => x.to_latex_string(),
            Stmt::HaveObjInNonemptySetStmt(x) => x.to_latex_string(),
            Stmt::HaveObjEqualStmt(x) => x.to_latex_string(),
            Stmt::HaveByExistStmt(x) => x.to_latex_string(),
            Stmt::HaveFnEqualStmt(x) => x.to_latex_string(),
            Stmt::HaveFnEqualCaseByCaseStmt(x) => x.to_latex_string(),
            Stmt::HaveFnByInducStmt(x) => x.to_latex_string(),
            Stmt::DefStructStmt(x) => x.to_latex_string(),
            Stmt::DefFamilyStmt(x) => x.to_latex_string(),
            Stmt::DefAlgoStmt(x) => x.to_latex_string(),
            Stmt::ClaimStmt(x) => x.to_latex_string(),
            Stmt::KnowStmt(x) => x.to_latex_string(),
            Stmt::ProveStmt(x) => x.to_latex_string(),
            Stmt::ImportStmt(x) => x.to_latex_string(),
            Stmt::DoNothingStmt(x) => x.to_latex_string(),
            Stmt::ClearStmt(x) => x.to_latex_string(),
            Stmt::RunFileStmt(x) => x.to_latex_string(),
            Stmt::EvalStmt(x) => x.to_latex_string(),
            Stmt::WitnessExistFact(x) => x.to_latex_string(),
            Stmt::WitnessNonemptySet(x) => x.to_latex_string(),
            Stmt::ByCasesStmt(x) => x.to_latex_string(),
            Stmt::ByContraStmt(x) => x.to_latex_string(),
            Stmt::ByEnumerateFiniteSetStmt(x) => x.to_latex_string(),
            Stmt::ByInducStmt(x) => x.to_latex_string(),
            Stmt::ByForStmt(x) => x.to_latex_string(),
            Stmt::ByExtensionStmt(x) => x.to_latex_string(),
            Stmt::ByFnStmt(x) => x.to_latex_string(),
            Stmt::ByFamilyStmt(x) => x.to_latex_string(),
            Stmt::ByStructStmt(x) => x.to_latex_string(),
            Stmt::ByTuple(x) => x.to_latex_string(),
            Stmt::ByFnSetStmt(x) => x.to_latex_string(),
            Stmt::ByFiniteSeqSetStmt(x) => x.to_latex_string(),
            Stmt::BySeqSetStmt(x) => x.to_latex_string(),
            Stmt::ByMatrixSetStmt(x) => x.to_latex_string(),
            Stmt::ByEnumerateClosedRangeStmt(x) => x.to_latex_string(),
        }
    }
}
