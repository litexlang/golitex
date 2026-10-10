use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ListSetObjWellDefinedProof, SetBuilderObjWellDefinedProof, SetFormerObjWellDefinedProofByDef,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_former(
        &self,
        set: &SetFormer,
        proof: &SetFormerObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (set, proof) {
            (SetFormer::ListSet(set), SetFormerObjWellDefinedProofByDef::ListSet(wd)) => {
                self.compile_list_set_wd(set, wd, position)
            }
            (SetFormer::SetBuilder(set), SetFormerObjWellDefinedProofByDef::SetBuilder(wd)) => {
                self.compile_set_builder_wd(set, wd, position)
            }
            (SetFormer::ListSet(_) | SetFormer::SetBuilder(_), _) => Err(LeanCompileError::new(
                "SetFormer/WDSubject",
                "Set formation evidence has another constructor family.",
            )),
            (
                SetFormer::Range(_)
                | SetFormer::ClosedRange(_)
                | SetFormer::FiniteSeqSet(_)
                | SetFormer::SeqSet(_)
                | SetFormer::OneSideInfinityIntervalObj(_)
                | SetFormer::IntervalObj(_),
                _,
            ) => Err(LeanCompileError::unsupported("WD/SetFormer")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_list_set_wd(
        &self,
        set: &ListSet,
        proof: &ListSetObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let n = set.list.len();
        if proof.child_obj_well_defined.len() != n
            || proof.requirement_fact_verified.len() != n.saturating_mul(n.saturating_sub(1)) / 2
        {
            return Err(LeanCompileError::new(
                "ListSet/Stages",
                "Enumeration WD needs every ordered child and pairwise inequality.",
            ));
        }
        let mut lines = Vec::new();
        for (i, (element, wd)) in set
            .list
            .iter()
            .zip(&proof.child_obj_well_defined)
            .enumerate()
        {
            ensure_object(element, wd)?;
            let term = self.compile_wd(
                wd,
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )?;
            lines.push(format!("let _setElement_{i} := {term}"));
        }
        let mut inequalities = vec![vec![String::new(); n]; n];
        let mut offset = 0;
        for i in 0..n {
            for j in (i + 1)..n {
                let evidence = &proof.requirement_fact_verified[offset];
                match source_subject(evidence)? {
                    Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if f.left.ir() == set.list[i].ir() && f.right.ir() == set.list[j].ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "ListSet/DistinctSubject",
                            "Pairwise WD proves another element pair or orientation.",
                        ))
                    }
                }
                inequalities[i][j] = self
                    .compile_verify(
                        evidence,
                        &SourcePosition {
                            before: n + offset,
                            ..*position
                        },
                    )?
                    .1;
                offset += 1;
            }
        }
        lines.push(format!("let _setTail_{n} := Litex.emptySet (M := M)"));
        for i in (0..n).rev() {
            let mut fresh = format!("(Litex.notInEmpty _setElement_{i})");
            for j in ((i + 1)..n).rev() {
                fresh = format!("(Litex.notInInsert _setElement_{i} _setElement_{j} _setTail_{} _setFresh_{j} {} {fresh})", j + 1, inequalities[i][j]);
            }
            lines.push(format!(
                "let _setFresh_{i} : ¬ Litex.In _setElement_{i} _setTail_{} := {fresh}",
                i + 1
            ));
            lines.push(format!(
                "let _setTail_{i} := Litex.insert _setElement_{i} _setTail_{} _setFresh_{i}",
                i + 1
            ));
        }
        Ok(format!(
            "({};\n  _setTail_0)",
            lines.join(";\n").replace('\n', "\n  ")
        ))
    }

    pub(in crate::compile_to_lean) fn compile_set_builder_wd(
        &self,
        set: &SetBuilder,
        proof: &SetBuilderObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let scope = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::SetBuilder(set, proof),
            before: 0,
        };
        ensure_object(&set.param_set, &proof.param_set_well_defined)?;
        let bound = self.compile_wd(&proof.param_set_well_defined, &scope)?;
        self.validate_parameter_store_capture(&proof.defined_params)?;
        if proof.defined_params.store_and_infer_results.len() != 1
            || proof.assumed_facts.len() != set.facts.len()
        {
            return Err(LeanCompileError::new(
                "SetBuilder/Stages",
                "Bounded formation needs its original binder and every ordered predicate clause.",
            ));
        }
        let introduced = SourcePosition { before: 2, ..scope };
        let store = &proof.defined_params.store_and_infer_results[0];
        let membership = self.resolve_fact(store.primary_fact_id(), &introduced)?;
        let parameter = Obj::Identifier(IdentifierObj::from_bound_name(&set.param_binding));
        match &membership {
            Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == parameter.ir() && f.set.ir() == set.param_set.ir() => {}
            _ => {
                return Err(LeanCompileError::new(
                    "SetBuilder/BinderSubject",
                    "Captured membership belongs to another binder or bound.",
                ))
            }
        }
        self.validate_store(store, &membership)?;
        let id = set.param_binding.id.value();
        let member_name = format!("h_{}", membership.fact_id().value());
        let member = (
            self.fact_proposition(&membership, &introduced)?,
            member_name.clone(),
        );
        let parameter_definitions =
            self.compile_parameter_inferences(store, &membership, &member, &introduced)?;
        let mut clauses = Vec::new();
        for (i, (source, captured)) in set.facts.iter().zip(&proof.assumed_facts).enumerate() {
            let fact = crate::instantiate::quantifier_free_fact_to_fact(source.clone());
            if !matches!(&fact, Fact::AtomicFact(_)) {
                return Err(LeanCompileError::unsupported(
                    "SetBuilder/CompoundPredicate",
                ));
            }
            let prior = SourcePosition {
                before: 2 + i,
                ..scope
            };
            self.compile_fact_wd(&captured.well_defined, &fact, &prior)?;
            self.validate_store(&captured.store_and_infer, &fact)?;
            let formed = SourcePosition {
                parent: Some(&prior),
                owner: SourceOwner::FactWD(&captured.well_defined),
                before: usize::MAX,
            };
            let clause = (
                self.fact_proposition(&fact, &formed)?,
                format!("h_{}", fact.fact_id().value()),
            );
            let completed = SourcePosition {
                before: 3 + i,
                ..scope
            };
            let mut derived = self.compile_parameter_inferences(
                &captured.store_and_infer,
                &fact,
                &clause,
                &completed,
            )?;
            derived.extend(self.compile_stored_inferences(
                &captured.store_and_infer,
                &fact,
                &clause,
                &completed,
            )?);
            clauses.push((clause.1, clause.0, derived));
        }
        let mut meaning = if let Some((_, last, _)) = clauses.pop() {
            last
        } else {
            "True".into()
        };
        for (name, clause, derived) in clauses.into_iter().rev() {
            meaning = format!(
                "∃ ({name} : {clause}), {}",
                self.scope_proposition(meaning, &derived)
            );
        }
        meaning = self.scope_proposition(meaning, &parameter_definitions);
        Ok(format!("(Litex.setBuilder {bound} (fun (_value_i{id} : Litex.Obj (M := M) M.Value) ({member_name} : Litex.In _value_i{id} {bound}) => {meaning}))"))
    }
}
