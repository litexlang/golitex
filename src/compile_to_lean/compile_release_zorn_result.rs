use crate::compile_to_lean::helper::{ensure_object, source_subject};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    ExecReleaseZornLemmaStmtResult, ExecReleaseZornLemmaStmtSuccess,
};
use crate::prelude::*;

pub(super) fn zorn_statement(
    statement: &ExecStmtResult,
) -> Option<&ExecReleaseZornLemmaStmtSuccess> {
    match statement {
        ExecStmtResult::ReleaseAndExpand(
            crate::execute::ExecReleaseAndExpandStmtResult::ZornLemma(
                ExecReleaseZornLemmaStmtResult::Success(p),
            ),
        ) => Some(p),
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_zorn(
        &self,
        result: &ExecReleaseZornLemmaStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseZornLemmaStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("Zorn/Failed"));
        };
        if p.statement.proof.len() != p.proof_steps.len() {
            return Err(LeanCompileError::unsupported("Zorn/ProofSteps"));
        }
        for (statement, result) in p.statement.proof.iter().zip(&p.proof_steps) {
            crate::compile_to_lean::helper::validate_statement_capture(statement, result)?;
        }
        let VerifyObjWellDefinedResult::Success(wd) = &p.set_wd else {
            return Err(LeanCompileError::unsupported("Zorn/SetWD"));
        };
        ensure_object(&p.statement.set, wd)?;
        let set = self.compile_wd(wd, position)?;
        if p.obligations.len() != 5 {
            return Err(LeanCompileError::unsupported("Zorn/Obligations"));
        }
        let facts = p
            .obligations
            .iter()
            .map(|o| source_subject(&o.verified))
            .collect::<Result<Vec<_>, _>>()?;
        if !matches!(&facts[0], Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir() == p.statement.set.ir())
        {
            return Err(LeanCompileError::unsupported("Zorn/NonemptySubject"));
        }
        validate_zorn_obligations(&p.statement, &facts)?;
        let Fact::ForallFact(reflexive) = &facts[1] else {
            return Err(LeanCompileError::unsupported("Zorn/Reflexivity"));
        };
        let [ExistOrAndChainAtomicFact::AtomicFact(atom @ AtomicFact::NormalAtomicFact(normal))] =
            reflexive.then_facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Zorn/Relation"));
        };
        if normal.predicate != p.statement.prop_name || normal.body.len() != 2 {
            return Err(LeanCompileError::unsupported("Zorn/Relation"));
        }
        let relation =
            self.compile_atomic_raw_proposition(atom, &["x".into(), "y".into()], position)?;
        let caller = SourcePosition {
            before: 1,
            ..*position
        };
        let scope = SourcePosition::new(Some(&caller), SourceOwner::Zorn(p), 0);
        let mut steps = Vec::new();
        for (i, stmt) in p.proof_steps.iter().enumerate() {
            steps.push(self.compile_statement_in_scope(
                stmt,
                &SourcePosition { before: i, ..scope },
                i + 1,
                true,
            )?);
        }
        for (i, (obligation, source)) in p.obligations.iter().zip(&facts).enumerate() {
            let (formation, store) = obligation
                .stored
                .as_ref()
                .map_err(|_| LeanCompileError::unsupported("Zorn/ObligationStore"))?;
            let stage = p.proof_steps.len() + 3 * i;
            let before = SourcePosition {
                before: stage,
                ..scope
            };
            let compiled = self.compile_verify(&obligation.verified, &before)?;
            self.compile_fact_wd(
                formation,
                source,
                &SourcePosition {
                    before: stage + 1,
                    ..scope
                },
            )?;
            self.validate_store(&store.store, source)?;
            steps.push(self.emit_fact(source, compiled.clone(), i, true, &before)?);
            steps.extend(self.compile_stored_inferences(
                store,
                source,
                &(compiled.0, format!("h_{}", source.fact_id().value())),
                &SourcePosition {
                    before: stage + 3,
                    ..scope
                },
            )?);
        }
        let source = self.resolve_fact(p.stored.primary_fact_id(), position)?;
        let Fact::ExistFact(exist) = &source else {
            return Err(LeanCompileError::unsupported("Zorn/Conclusion"));
        };
        let [group] = exist.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Zorn/ConclusionBinder"));
        };
        let [m] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported("Zorn/ConclusionBinder"));
        };
        if !matches!(&group.param_type, ParamType::Obj(s) if s.ir() == p.statement.set.ir())
            || !matches!(exist.facts.as_slice(), [QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(f))]
                if f.predicate == p.statement.maximal_prop_name && f.body.len() == 1
                && f.body[0].ir() == Obj::Identifier(IdentifierObj::from_bound_name(m)).ir())
        {
            return Err(LeanCompileError::unsupported("Zorn/ConclusionSubject"));
        }
        // The compiled concrete upper-bound and maximal predicates retain their
        // domain witnesses. Lean checks the exact definition when these are unpacked.
        let ids = facts
            .iter()
            .map(|f| format!("h_{}", f.fact_id().value()))
            .collect::<Vec<_>>();
        let obj = |x: &str| format!("(Litex.objectAtLevel {x} (M.member_isSet h{x}))");
        steps.push(format!("have _zorn_refl : ∀ x, M.mem x (Litex.denote {set}) → ((fun x y : M.Value => {relation}) x x) := by\n  intro x hx\n  exact {} {} hx", ids[1], obj("x")));
        let refl = "_zorn_refl";
        let trans = format!(
            "(fun x y z hx hy hz hxy hyz => {} {} hx {} hy {} hz hxy hyz)",
            ids[2],
            obj("x"),
            obj("y"),
            obj("z")
        );
        let anti = format!(
            "(fun x y hx hy hxy hyx => {} {} hx {} hy hxy hyx)",
            ids[3],
            obj("x"),
            obj("y")
        );
        let bound = format!("(by\n  intro c hc hchain\n  obtain ⟨b, hb, hub⟩  := {} (Litex.objectAtLevel (Litex.denote c) (Litex.isSet c)) hc (by\n    intro _ _ x hx _ _ y hy\n    exact hchain (Litex.denote x) (Litex.denote y) hx hy)\n  obtain ⟨_, _, hub⟩ := hub\n  refine ⟨Litex.denote b, hb, ?_⟩\n  intro x hx\n  exact hub {} hx)", ids[4], "(Litex.semanticObject x (M.member_isSet hx))");
        steps.push(format!("obtain ⟨m, hm, hmax⟩ := Litex.zornMaximal {set} (fun x y : M.Value => {relation}) {refl} {trans} {anti} {bound}"));
        steps.push(
            "refine ⟨m, hm, hm, ?_⟩\nintro x hx hmx\nexact hmax (Litex.denote x) hx hmx".into(),
        );
        let outer = SourcePosition {
            before: 2,
            ..*position
        };
        let proposition = self.compile_formed_fact_proposition(&p.stored_wd, &source, &outer)?;
        let term = format!("(by\n  {}\n)", steps.join("\n").replace('\n', "\n  "));
        self.emit_by_completed_fact(
            &source,
            (proposition, term),
            &p.stored,
            position,
            4,
            index,
            local,
        )
    }
}

fn validate_zorn_obligations(
    statement: &crate::ast::stmt::ReleaseZornLemmaStmt,
    facts: &[Fact],
) -> Result<(), LeanCompileError> {
    let fail = || LeanCompileError::unsupported("Zorn/ObligationSubject");
    fn parameters(fact: &ForallFact, set: &Obj, count: usize) -> Option<Vec<Obj>> {
        let mut values = Vec::new();
        for group in &fact.typed_parameters.groups {
            if !matches!(&group.param_type, ParamType::Obj(s) if s.ir() == set.ir()) {
                return None;
            }
            values.extend(
                group
                    .params
                    .iter()
                    .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p))),
            );
        }
        (values.len() == count).then_some(values)
    }
    let normal = |fact: &Fact, name: &AtomicName, args: &[&Obj]| {
        matches!(fact,
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(p)) if &p.predicate == name
        && p.body.len() == args.len() && p.body.iter().zip(args).all(|(a,b)| a.ir() == b.ir()))
    };
    let [Fact::ForallFact(refl), Fact::ForallFact(trans), Fact::ForallFact(anti), Fact::ForallFact(bound)] =
        &facts[1..]
    else {
        return Err(fail());
    };
    let r = &statement.prop_name;
    let v = parameters(refl, &statement.set, 1).ok_or_else(fail)?;
    if !refl.dom_facts.is_empty()
        || refl.then_facts.len() != 1
        || !normal(&refl.then_facts[0].clone().into(), r, &[&v[0], &v[0]])
    {
        return Err(fail());
    }
    let v = parameters(trans, &statement.set, 3).ok_or_else(fail)?;
    if trans.dom_facts.len() != 2
        || trans.then_facts.len() != 1
        || !normal(&trans.dom_facts[0], r, &[&v[0], &v[1]])
        || !normal(&trans.dom_facts[1], r, &[&v[1], &v[2]])
        || !normal(&trans.then_facts[0].clone().into(), r, &[&v[0], &v[2]])
    {
        return Err(fail());
    }
    let v = parameters(anti, &statement.set, 2).ok_or_else(fail)?;
    if anti.dom_facts.len() != 2
        || anti.then_facts.len() != 1
        || !normal(&anti.dom_facts[0], r, &[&v[0], &v[1]])
        || !normal(&anti.dom_facts[1], r, &[&v[1], &v[0]])
        || !matches!(&anti.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) if e.left.ir() == v[0].ir() && e.right.ir() == v[1].ir())
    {
        return Err(fail());
    }
    let power = Obj::SetOperator(SetOperator::PowerSet(PowerSet {
        set: Box::new(statement.set.clone()),
    }));
    let c = parameters(bound, &power, 1).ok_or_else(fail)?;
    let [Fact::ForallFact(chain)] = bound.dom_facts.as_slice() else {
        return Err(fail());
    };
    let xy = parameters(chain, &c[0], 2).ok_or_else(fail)?;
    let [ExistOrAndChainAtomicFact::OrFact(or)] = chain.then_facts.as_slice() else {
        return Err(fail());
    };
    if !chain.dom_facts.is_empty()
        || or.facts.len() != 2
        || !normal(
            &crate::ast::fact::and_chain_as_fact(&or.facts[0]),
            r,
            &[&xy[0], &xy[1]],
        )
        || !normal(
            &crate::ast::fact::and_chain_as_fact(&or.facts[1]),
            r,
            &[&xy[1], &xy[0]],
        )
    {
        return Err(fail());
    }
    let [ExistOrAndChainAtomicFact::ExistFact(exist)] = bound.then_facts.as_slice() else {
        return Err(fail());
    };
    let [group] = exist.typed_parameters.groups.as_slice() else {
        return Err(fail());
    };
    let [u] = group.params.as_slice() else {
        return Err(fail());
    };
    if !matches!(&group.param_type, ParamType::Obj(s) if s.ir() == statement.set.ir())
        || exist.facts.len() != 1
        || !normal(
            &crate::instantiate::quantifier_free_fact_to_fact(exist.facts[0].clone()),
            &statement.upper_bound_prop_name,
            &[&c[0], &Obj::Identifier(IdentifierObj::from_bound_name(u))],
        )
    {
        return Err(fail());
    }
    Ok(())
}
