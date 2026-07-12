use crate::prelude::*;
use std::collections::HashSet;

pub fn to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let mut tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;

    let mut verified_stmts = Vec::new();
    for mut block in blocks {
        let stmt = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&stmt, runtime)?;
        verified_stmts.push(VerifiedStmt::new(stmt, result));
    }

    LeanEmitter::new().emit(&verified_stmts)
}

pub fn to_lean_from_source_after_builtins(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_lean(normalized.as_str(), &mut runtime)
}

struct VerifiedStmt {
    stmt: Stmt,
    result: StmtResult,
}

impl VerifiedStmt {
    fn new(stmt: Stmt, result: StmtResult) -> Self {
        VerifiedStmt { stmt, result }
    }
}

struct LeanEmitter {
    lines: Vec<String>,
    next_fact_id: usize,
}

impl LeanEmitter {
    fn new() -> Self {
        LeanEmitter {
            lines: vec![
                "import Mathlib".to_string(),
                String::new(),
                "namespace LitexGenerated".to_string(),
                String::new(),
                "-- Generated from Litex after Litex verification.".to_string(),
                "-- Proof bodies are conservative Mathlib tactic reconstructions, not proof certificates.".to_string(),
            ],
            next_fact_id: 1,
        }
    }

    fn emit(mut self, verified_stmts: &[VerifiedStmt]) -> Result<String, RuntimeError> {
        for verified_stmt in verified_stmts {
            self.emit_verified_stmt(verified_stmt)?;
        }
        self.push_blank_line();
        self.lines.push("end LitexGenerated".to_string());
        Ok(self.lines.join("\n"))
    }

    fn emit_verified_stmt(&mut self, verified_stmt: &VerifiedStmt) -> Result<(), RuntimeError> {
        if verified_stmt.result.is_unknown() {
            return Err(lean_extract_error(
                &verified_stmt.stmt.line_file(),
                "Lean extractor received an unverified Litex statement",
            ));
        }

        match &verified_stmt.stmt {
            Stmt::Fact(fact) => self.emit_named_fact(fact, &verified_stmt.result),
            Stmt::DefThmStmt(stmt) => self.emit_theorem(stmt, &verified_stmt.result),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(stmt)) => {
                self.emit_named_claim(stmt, &verified_stmt.result)
            }
            other => Err(lean_extract_error(
                &other.line_file(),
                format!(
                    "Lean extractor MVP does not support verified Litex statement `{}` ({})",
                    other,
                    other.stmt_type_name()
                ),
            )),
        }
    }

    fn emit_named_fact(&mut self, fact: &Fact, result: &StmtResult) -> Result<(), RuntimeError> {
        let proposition = self.fact(fact)?;
        let name = format!("litex_fact_{}", self.next_fact_id);
        self.next_fact_id += 1;
        self.push_blank_line();
        self.push_evidence_comment(result, 0);
        self.lines
            .push(format!("theorem {} : {} := by", name, proposition));
        self.emit_fact_proof(fact, 1)?;
        Ok(())
    }

    fn emit_theorem(&mut self, stmt: &DefThmStmt, result: &StmtResult) -> Result<(), RuntimeError> {
        if stmt.is_axiom() {
            return Err(lean_extract_error(
                &stmt.line_file,
                "Lean extractor MVP refuses to emit a Litex axiom as a Lean axiom",
            ));
        }
        if stmt.names.is_empty() {
            return Err(lean_extract_error(
                &stmt.line_file,
                "Lean extractor cannot emit a theorem without a name",
            ));
        }

        for name in &stmt.names {
            self.push_blank_line();
            self.push_evidence_comment(result, 0);
            let signature = self.forall_signature(&stmt.forall_fact)?;
            self.lines.push(format!(
                "theorem {}{} : {} := by",
                lean_name(name),
                signature.binders,
                signature.conclusion
            ));
            self.emit_local_steps(&stmt.prove_process, 1)?;
            self.emit_then_facts_proof(&stmt.forall_fact.then_facts, 1)?;
        }
        Ok(())
    }

    fn emit_named_claim(
        &mut self,
        stmt: &ClaimStmt,
        result: &StmtResult,
    ) -> Result<(), RuntimeError> {
        let proposition = self.fact(&stmt.fact)?;
        let name = format!("litex_fact_{}", self.next_fact_id);
        self.next_fact_id += 1;
        self.push_blank_line();
        self.push_evidence_comment(result, 0);
        self.lines
            .push(format!("theorem {} : {} := by", name, proposition));
        self.emit_claim_proof(stmt, 1)?;
        Ok(())
    }

    fn emit_claim_proof(&mut self, stmt: &ClaimStmt, indent: usize) -> Result<(), RuntimeError> {
        if let Fact::ForallFact(fact) = &stmt.fact {
            self.emit_forall_intros(fact, indent);
            self.emit_local_steps(&stmt.proof, indent)?;
            return self.emit_then_facts_proof(&fact.then_facts, indent);
        }

        self.emit_local_steps(&stmt.proof, indent)?;
        self.emit_fact_proof(&stmt.fact, indent)
    }

    fn emit_local_steps(&mut self, steps: &[Stmt], indent: usize) -> Result<(), RuntimeError> {
        for step in steps {
            match step {
                Stmt::Fact(fact) => {
                    let name = format!("litex_fact_{}", self.next_fact_id);
                    self.next_fact_id += 1;
                    let proposition = self.fact(fact)?;
                    self.lines.push(format!(
                        "{}have {} : {} := by",
                        spaces(indent),
                        name,
                        proposition
                    ));
                    self.emit_fact_proof(fact, indent + 1)?;
                }
                Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(claim)) => {
                    let name = format!("litex_fact_{}", self.next_fact_id);
                    self.next_fact_id += 1;
                    let proposition = self.fact(&claim.fact)?;
                    self.lines.push(format!(
                        "{}have {} : {} := by",
                        spaces(indent),
                        name,
                        proposition
                    ));
                    self.emit_claim_proof(claim, indent + 1)?;
                }
                other => {
                    return Err(lean_extract_error(
                        &other.line_file(),
                        format!(
                            "Lean extractor MVP cannot reconstruct proof step `{}` ({})",
                            other,
                            other.stmt_type_name()
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    fn fact(&self, fact: &Fact) -> Result<String, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => self.atomic_fact(fact),
            Fact::AndFact(fact) => self.and_fact(fact),
            Fact::OrFact(fact) => self.or_fact(fact),
            Fact::ForallFact(fact) => {
                let signature = self.forall_signature(fact)?;
                Ok(format!(
                    "∀{}, {}",
                    signature.binders.trim_start(),
                    signature.conclusion
                ))
            }
            other => Err(lean_extract_error(
                &other.line_file(),
                format!("Lean extractor MVP cannot translate fact `{}`", other),
            )),
        }
    }

    fn atomic_fact(&self, fact: &AtomicFact) -> Result<String, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(fact) => self.binary_fact(&fact.left, "=", &fact.right),
            AtomicFact::NotEqualFact(fact) => self.binary_fact(&fact.left, "≠", &fact.right),
            AtomicFact::LessFact(fact) => self.binary_fact(&fact.left, "<", &fact.right),
            AtomicFact::LessEqualFact(fact) => self.binary_fact(&fact.left, "≤", &fact.right),
            AtomicFact::GreaterFact(fact) => self.binary_fact(&fact.left, ">", &fact.right),
            AtomicFact::GreaterEqualFact(fact) => self.binary_fact(&fact.left, "≥", &fact.right),
            other => Err(lean_extract_error(
                &other.line_file(),
                format!(
                    "Lean extractor MVP cannot translate atomic fact `{}`",
                    other
                ),
            )),
        }
    }

    fn binary_fact(&self, left: &Obj, op: &str, right: &Obj) -> Result<String, RuntimeError> {
        Ok(format!(
            "{} {} {}",
            self.real_expr(left)?,
            op,
            self.real_expr(right)?
        ))
    }

    fn and_fact(&self, fact: &AndFact) -> Result<String, RuntimeError> {
        if fact.facts.is_empty() {
            return Err(lean_extract_error(
                &fact.line_file,
                "Lean extractor MVP cannot translate an empty conjunction",
            ));
        }
        let mut parts = Vec::new();
        for atomic in &fact.facts {
            parts.push(self.atomic_fact(atomic)?);
        }
        Ok(parenthesized_join(&parts, " ∧ "))
    }

    fn or_fact(&self, fact: &OrFact) -> Result<String, RuntimeError> {
        if fact.facts.is_empty() {
            return Err(lean_extract_error(
                &fact.line_file,
                "Lean extractor MVP cannot translate an empty disjunction",
            ));
        }
        let mut parts = Vec::new();
        for branch in &fact.facts {
            parts.push(self.and_chain_atomic_fact(branch)?);
        }
        Ok(parenthesized_join(&parts, " ∨ "))
    }

    fn and_chain_atomic_fact(&self, fact: &AndChainAtomicFact) -> Result<String, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(fact) => self.atomic_fact(fact),
            AndChainAtomicFact::AndFact(fact) => self.and_fact(fact),
            AndChainAtomicFact::ChainFact(fact) => Err(lean_extract_error(
                &fact.line_file,
                format!(
                    "Lean extractor MVP cannot translate calculation chain `{}`",
                    fact
                ),
            )),
        }
    }

    fn forall_signature(&self, fact: &ForallFact) -> Result<ForallSignature, RuntimeError> {
        let mut binder_groups = Vec::new();
        for group in fact.params_def_with_type.iter() {
            match &group.param_type {
                ParamType::Obj(Obj::StandardSet(StandardSet::R)) => {}
                other => {
                    return Err(lean_extract_error(
                        &fact.line_file,
                        format!(
                            "Lean extractor MVP supports only `R` forall parameters; got `{}`",
                            other
                        ),
                    ));
                }
            }
            let mut names = Vec::new();
            for name in &group.params {
                names.push(lean_name(name));
            }
            binder_groups.push(format!("({} : ℝ)", names.join(" ")));
        }

        let mut hypotheses = Vec::new();
        for (index, dom_fact) in fact.dom_facts.iter().enumerate() {
            hypotheses.push(format!("(_h{} : {})", index + 1, self.fact(dom_fact)?));
        }

        let conclusion = self.then_facts(&fact.then_facts)?;
        let mut binders = String::new();
        if !binder_groups.is_empty() {
            binders.push(' ');
            binders.push_str(&binder_groups.join(" "));
        }
        if !hypotheses.is_empty() {
            binders.push(' ');
            binders.push_str(&hypotheses.join(" "));
        }
        Ok(ForallSignature::new(binders, conclusion))
    }

    fn then_facts(&self, facts: &[ExistOrAndChainAtomicFact]) -> Result<String, RuntimeError> {
        if facts.is_empty() {
            return Err(lean_extract_error(
                &default_line_file(),
                "Lean extractor MVP cannot translate a forall without conclusions",
            ));
        }
        let mut parts = Vec::new();
        for fact in facts {
            parts.push(self.fact_inside_forall(fact)?);
        }
        Ok(parenthesized_join(&parts, " ∧ "))
    }

    fn fact_inside_forall(&self, fact: &ExistOrAndChainAtomicFact) -> Result<String, RuntimeError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(fact) => self.atomic_fact(fact),
            ExistOrAndChainAtomicFact::AndFact(fact) => self.and_fact(fact),
            ExistOrAndChainAtomicFact::OrFact(fact) => self.or_fact(fact),
            ExistOrAndChainAtomicFact::ChainFact(fact) => Err(lean_extract_error(
                &fact.line_file,
                format!(
                    "Lean extractor MVP cannot translate calculation chain `{}`",
                    fact
                ),
            )),
            ExistOrAndChainAtomicFact::ExistFact(fact) => Err(lean_extract_error(
                &fact.line_file(),
                format!(
                    "Lean extractor MVP cannot translate existential fact `{}`",
                    fact
                ),
            )),
        }
    }

    fn real_expr(&self, obj: &Obj) -> Result<String, RuntimeError> {
        match obj {
            Obj::Number(number) => Ok(format!("({} : ℝ)", number.normalized_value)),
            Obj::Atom(atom) => self.real_atom(atom),
            Obj::Add(obj) => self.binary_expr(&obj.left, "+", &obj.right),
            Obj::Sub(obj) => self.binary_expr(&obj.left, "-", &obj.right),
            Obj::Mul(obj) => self.binary_expr(&obj.left, "*", &obj.right),
            Obj::Div(obj) => self.binary_expr(&obj.left, "/", &obj.right),
            Obj::Pow(obj) => {
                let base = self.real_expr(obj.base.as_ref())?;
                let exponent = natural_exponent(obj.exponent.as_ref())?;
                Ok(format!("({} ^ {})", base, exponent))
            }
            other => Err(lean_extract_error(
                &default_line_file(),
                format!("Lean extractor MVP cannot translate object `{}`", other),
            )),
        }
    }

    fn binary_expr(&self, left: &Obj, op: &str, right: &Obj) -> Result<String, RuntimeError> {
        Ok(format!(
            "({} {} {})",
            self.real_expr(left)?,
            op,
            self.real_expr(right)?
        ))
    }

    fn real_atom(&self, atom: &AtomObj) -> Result<String, RuntimeError> {
        let name = match atom {
            AtomObj::Identifier(obj) => &obj.name,
            AtomObj::Forall(obj) => &obj.name,
            AtomObj::Def(obj) => &obj.name,
            other => {
                return Err(lean_extract_error(
                    &default_line_file(),
                    format!(
                        "Lean extractor MVP cannot translate object atom `{}`",
                        other
                    ),
                ));
            }
        };
        Ok(lean_name(name))
    }

    fn emit_then_facts_proof(
        &mut self,
        facts: &[ExistOrAndChainAtomicFact],
        indent: usize,
    ) -> Result<(), RuntimeError> {
        if facts.len() == 1 {
            return self.emit_fact_inside_forall_proof(&facts[0], indent);
        }
        if facts.is_empty() {
            return Err(lean_extract_error(
                &default_line_file(),
                "Lean extractor MVP cannot prove a forall without conclusions",
            ));
        }
        self.lines.push(format!("{}constructor", spaces(indent)));
        self.emit_fact_inside_forall_proof(&facts[0], indent + 1)?;
        self.emit_then_facts_proof(&facts[1..], indent + 1)
    }

    fn emit_fact_inside_forall_proof(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        indent: usize,
    ) -> Result<(), RuntimeError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(fact) => self.emit_atomic_tactic(fact, indent),
            ExistOrAndChainAtomicFact::AndFact(fact) => self.emit_and_proof(fact, indent),
            ExistOrAndChainAtomicFact::OrFact(fact) => self.emit_or_proof(fact, indent),
            other => Err(lean_extract_error(
                &other.line_file(),
                format!("Lean extractor MVP cannot reconstruct proof of `{}`", other),
            )),
        }
    }

    fn emit_fact_proof(&mut self, fact: &Fact, indent: usize) -> Result<(), RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => self.emit_atomic_tactic(fact, indent),
            Fact::AndFact(fact) => self.emit_and_proof(fact, indent),
            Fact::OrFact(fact) => self.emit_or_proof(fact, indent),
            Fact::ForallFact(fact) => {
                self.emit_forall_intros(fact, indent);
                self.emit_then_facts_proof(&fact.then_facts, indent)
            }
            other => Err(lean_extract_error(
                &other.line_file(),
                format!("Lean extractor MVP cannot reconstruct proof of `{}`", other),
            )),
        }
    }

    fn emit_forall_intros(&mut self, fact: &ForallFact, indent: usize) {
        let hypothesis_count = fact.dom_facts.len();
        let mut names = fact.params_def_with_type.collect_param_names();
        for index in 0..hypothesis_count {
            names.push(format!("h{}", index + 1));
        }
        if names.is_empty() {
            return;
        }
        let names = names.iter().map(|name| lean_name(name)).collect::<Vec<_>>();
        self.lines
            .push(format!("{}intro {}", spaces(indent), names.join(" ")));
    }

    fn emit_and_proof(&mut self, fact: &AndFact, indent: usize) -> Result<(), RuntimeError> {
        if fact.facts.len() == 1 {
            return self.emit_atomic_tactic(&fact.facts[0], indent);
        }
        if fact.facts.is_empty() {
            return Err(lean_extract_error(
                &fact.line_file,
                "Lean extractor MVP cannot prove an empty conjunction",
            ));
        }
        self.lines.push(format!("{}constructor", spaces(indent)));
        self.emit_atomic_tactic(&fact.facts[0], indent + 1)?;
        let rest = AndFact::new(fact.facts[1..].to_vec(), fact.line_file.clone());
        self.emit_and_proof(&rest, indent + 1)
    }

    fn emit_or_proof(&mut self, fact: &OrFact, indent: usize) -> Result<(), RuntimeError> {
        self.lines.push(format!("{}simp_all", spaces(indent)));
        if fact.facts.is_empty() {
            return Err(lean_extract_error(
                &fact.line_file,
                "Lean extractor MVP cannot prove an empty disjunction",
            ));
        }
        Ok(())
    }

    fn emit_atomic_tactic(&mut self, fact: &AtomicFact, indent: usize) -> Result<(), RuntimeError> {
        self.atomic_fact(fact)?;
        let tactic = if atomic_fact_contains_division(fact) {
            "field_simp [*] <;> ring <;> nlinarith"
        } else if matches!(fact, AtomicFact::EqualFact(_)) {
            "nlinarith"
        } else {
            "norm_num at * <;> nlinarith"
        };
        self.lines.push(format!("{}{}", spaces(indent), tactic));
        Ok(())
    }

    fn push_evidence_comment(&mut self, result: &StmtResult, indent: usize) {
        if let Some(message) = first_builtin_message(result) {
            self.lines.push(format!(
                "{}-- Litex evidence hint: {}",
                spaces(indent),
                one_line_comment(message)
            ));
        }
    }

    fn push_blank_line(&mut self) {
        if self
            .lines
            .last()
            .map(|line| !line.is_empty())
            .unwrap_or(false)
        {
            self.lines.push(String::new());
        }
    }
}

struct ForallSignature {
    binders: String,
    conclusion: String,
}

impl ForallSignature {
    fn new(binders: String, conclusion: String) -> Self {
        ForallSignature {
            binders,
            conclusion,
        }
    }
}

fn natural_exponent(obj: &Obj) -> Result<String, RuntimeError> {
    let Obj::Number(number) = obj else {
        return Err(lean_extract_error(
            &default_line_file(),
            format!(
                "Lean extractor MVP supports only literal natural exponents; got `{}`",
                obj
            ),
        ));
    };
    let value = number.normalized_value.as_str();
    if value.is_empty() || !value.chars().all(|ch| ch.is_ascii_digit()) {
        return Err(lean_extract_error(
            &default_line_file(),
            format!(
                "Lean extractor MVP supports only literal natural exponents; got `{}`",
                value
            ),
        ));
    }
    Ok(value.to_string())
}

fn atomic_fact_contains_division(fact: &AtomicFact) -> bool {
    match fact {
        AtomicFact::EqualFact(fact) => {
            obj_contains_division(&fact.left) || obj_contains_division(&fact.right)
        }
        AtomicFact::NotEqualFact(fact) => {
            obj_contains_division(&fact.left) || obj_contains_division(&fact.right)
        }
        AtomicFact::LessFact(fact) => {
            obj_contains_division(&fact.left) || obj_contains_division(&fact.right)
        }
        AtomicFact::LessEqualFact(fact) => {
            obj_contains_division(&fact.left) || obj_contains_division(&fact.right)
        }
        AtomicFact::GreaterFact(fact) => {
            obj_contains_division(&fact.left) || obj_contains_division(&fact.right)
        }
        AtomicFact::GreaterEqualFact(fact) => {
            obj_contains_division(&fact.left) || obj_contains_division(&fact.right)
        }
        _ => false,
    }
}

fn obj_contains_division(obj: &Obj) -> bool {
    match obj {
        Obj::Div(_) => true,
        Obj::Add(obj) => obj_contains_division(&obj.left) || obj_contains_division(&obj.right),
        Obj::Sub(obj) => obj_contains_division(&obj.left) || obj_contains_division(&obj.right),
        Obj::Mul(obj) => obj_contains_division(&obj.left) || obj_contains_division(&obj.right),
        Obj::Pow(obj) => obj_contains_division(&obj.base),
        _ => false,
    }
}

fn first_builtin_message(result: &StmtResult) -> Option<&str> {
    if let Some(success) = result.factual_success() {
        if let VerifiedByResult::BuiltinRule(builtin) = &success.verified_by {
            return Some(builtin.msg.as_str());
        }
    }
    if let Some(success) = result.non_factual_success() {
        for inside in &success.inside_results {
            if let Some(message) = first_builtin_message(inside) {
                return Some(message);
            }
        }
    }
    None
}

fn one_line_comment(message: &str) -> String {
    message
        .replace('\r', " ")
        .replace('\n', " ")
        .replace("--", "-")
}

fn parenthesized_join(parts: &[String], separator: &str) -> String {
    if parts.len() == 1 {
        return parts[0].clone();
    }
    format!("({})", parts.join(separator))
}

fn spaces(indent: usize) -> String {
    "  ".repeat(indent)
}

fn lean_name(name: &str) -> String {
    let mut output = String::new();
    for ch in name.chars() {
        if ch == '_' || ch.is_ascii_alphanumeric() {
            output.push(ch);
        } else {
            output.push('_');
        }
    }
    if output.is_empty() || output.starts_with(|ch: char| ch.is_ascii_digit()) {
        output.insert_str(0, "litex_");
    }
    if lean_keywords().contains(output.as_str()) {
        output.insert_str(0, "litex_");
    }
    output
}

fn lean_keywords() -> HashSet<&'static str> {
    [
        "axiom",
        "by",
        "def",
        "do",
        "else",
        "end",
        "example",
        "false",
        "for",
        "forall",
        "fun",
        "have",
        "if",
        "import",
        "in",
        "inductive",
        "let",
        "match",
        "namespace",
        "open",
        "opaque",
        "partial",
        "private",
        "protected",
        "structure",
        "theorem",
        "then",
        "true",
        "where",
        "with",
    ]
    .into_iter()
    .collect()
}

fn lean_extract_error(line_file: &LineFile, msg: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        msg.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn translates_verified_closed_arithmetic_fact() {
        run_with_large_stack("translates_verified_closed_arithmetic_fact", || {
            let output = to_lean_from_source_after_builtins("1 + 1 = 2", "to-lean-test").unwrap();

            assert!(output.starts_with("import Mathlib"));
            assert!(output.contains("namespace LitexGenerated"));
            assert!(output.contains("theorem litex_fact_1 : ((1 : ℝ) + (1 : ℝ)) = (2 : ℝ) := by"));
            assert!(output.ends_with("end LitexGenerated"));
            assert!(!output.contains("sorry"));
            assert!(!output.contains("axiom"));
        });
    }

    #[test]
    fn translates_verified_real_theorem() {
        run_with_large_stack("translates_verified_real_theorem", || {
            let source = "thm add_comm:\n    prove:\n        forall a, b R:\n            a + b = b + a\n    a + b = b + a";
            let output = to_lean_from_source_after_builtins(source, "to-lean-test").unwrap();

            assert!(output.contains("theorem add_comm (a b : ℝ)"));
            assert!(output.contains("nlinarith"));
        });
    }

    #[test]
    fn introduces_forall_binders_before_claim_steps() {
        run_with_large_stack("introduces_forall_binders_before_claim_steps", || {
            let source = "claim:\n    prove:\n        forall x R:\n            x = 1\n            =>:\n                x = 1\n    x = 1";
            let output = to_lean_from_source_after_builtins(source, "to-lean-test").unwrap();
            let intro = output.find("intro x h1").unwrap();
            let local_fact = output.find("have litex_fact_2").unwrap();

            assert!(output.contains("(_h1 : x = (1 : ℝ))"));
            assert!(intro < local_fact);
        });
    }

    #[test]
    fn rejects_verified_trust_instead_of_emitting_trust() {
        run_with_large_stack("rejects_verified_trust_instead_of_emitting_trust", || {
            let result = to_lean_from_source_after_builtins("trust 1 = 2", "to-lean-test");

            assert!(result.is_err());
        });
    }

    #[test]
    fn rejects_non_natural_power_exponent() {
        run_with_large_stack("rejects_non_natural_power_exponent", || {
            let source = "thm bad_shape:\n    prove:\n        forall x, y R:\n            x^y = x^y\n    x^y = x^y";
            let result = to_lean_from_source_after_builtins(source, "to-lean-test");

            assert!(result.is_err());
        });
    }

    fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap();
    }
}
