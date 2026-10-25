use super::helper::ensure_object;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{
    ExecHaveByReplacementAxiomStmtResult, ExecHaveByReplacementAxiomStmtSuccessResult,
};
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn replacement_statement(
    statement: &ExecStmtResult,
) -> Option<&ExecHaveByReplacementAxiomStmtSuccessResult> {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveByReplacementAxiom(
                ExecHaveByReplacementAxiomStmtResult::Success(p),
            ),
        )) => Some(p),
        _ => None,
    }
}

fn object(parameter: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(parameter))
}

fn forall_store(store: &StoreFactAndInferResult) -> Result<&ForallFact, LeanCompileError> {
    match &store.store {
        StoreFactResult::ForallFact(s)
            if s.fact_id == s.fact.fact_id
                && matches!(
                    &store.infer,
                    None | Some(crate::store_fact_and_infer::InferResult::ForallFact(
                        crate::store_fact_and_infer::InferForallFactResult::NoInfer
                    ))
                ) =>
        {
            Ok(&s.fact)
        }
        _ => Err(LeanCompileError::unsupported("Replacement/ForallStore")),
    }
}

fn object_binder(parameter: &BoundName) -> String {
    let id = parameter.id.value();
    format!("{{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id})")
}

impl LitexToLeanCompiler {
    pub(super) fn compile_replacement(
        &self,
        result: &ExecHaveByReplacementAxiomStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported(
                "Replacement/LocalDeclaration",
            ));
        }
        let ExecHaveByReplacementAxiomStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("Replacement/Failed"));
        };
        self.validate_parameter_store_capture(&p.defined_params)?;
        let [set_store] = p.defined_params.store_and_infer_results.as_slice() else {
            return Err(LeanCompileError::unsupported("Replacement/SetStore"));
        };
        let image = object(&p.statement.name);
        if !matches!(&set_store.store, StoreFactResult::AtomicFact(s)
            if matches!(&s.fact, AtomicFact::IsSetFact(f) if f.set.ir() == image.ir()))
            || !matches!(&set_store.infer, Some(crate::store_fact_and_infer::InferResult::AtomicFact(crate::store_fact_and_infer::InferAtomicFactResult::IsSetFact(r))) if r.is_empty())
        {
            return Err(LeanCompileError::unsupported("Replacement/SetSubject"));
        }
        let ids = p
            .defined_params
            .stored_fact_ids
            .iter()
            .copied()
            .chain(p.introduction.stored_fact_ids())
            .chain(p.elimination.stored_fact_ids())
            .collect::<Vec<_>>();
        if ids != p.stored_fact_ids {
            return Err(LeanCompileError::unsupported("Replacement/StoreCapture"));
        }
        let VerifyObjWellDefinedResult::Success(wd) = &p.source_wd else {
            return Err(LeanCompileError::unsupported("Replacement/SourceWD"));
        };
        ensure_object(&p.statement.source_set, wd)?;
        let domain = self.compile_wd(wd, position)?;
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let (unique, citation) = self.cited_fact_reference(p.uniqueness_fact_id, &formed)?;
        let Fact::ForallFact(unique) = unique else {
            return Err(LeanCompileError::unsupported("Replacement/Uniqueness"));
        };
        if !crate::execute::forall_is_replacement_uniqueness(
            unique,
            &p.statement.prop_name,
            &p.statement.source_set,
        ) {
            return Err(LeanCompileError::unsupported(
                "Replacement/UniquenessSubject",
            ));
        }
        let intro = forall_store(&p.introduction)?;
        let [x_group, y_group] = intro.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "Replacement/IntroductionBinders",
            ));
        };
        let ([x], [y]) = (x_group.params.as_slice(), y_group.params.as_slice()) else {
            return Err(LeanCompileError::unsupported(
                "Replacement/IntroductionBinders",
            ));
        };
        if !matches!(&x_group.param_type, ParamType::Obj(a) if a.ir() == p.statement.source_set.ir())
            || !matches!(y_group.param_type, ParamType::Set(_))
        {
            return Err(LeanCompileError::unsupported(
                "Replacement/IntroductionDomain",
            ));
        }
        let [relation @ Fact::AtomicFact(AtomicFact::NormalAtomicFact(prop))] =
            intro.dom_facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported(
                "Replacement/IntroductionRelation",
            ));
        };
        if prop.predicate != p.statement.prop_name
            || prop.body != vec![object(x), object(y)]
            || !matches!(intro.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f))]
                if f.element.ir() == object(y).ir() && f.set.ir() == image.ir())
        {
            return Err(LeanCompileError::unsupported(
                "Replacement/IntroductionSubject",
            ));
        }
        let raw = self.compile_function_raw_predicate(
            relation,
            &formed,
            &HashMap::from([
                (x.id, "_replacement_x".into()),
                (y.id, "_replacement_y".into()),
            ]),
        )?;
        let uniqueness =
            self.compile_replacement_uniqueness(unique, &citation, &p.statement.source_set)?;
        let name = format!("_object_i{}", p.statement.name.id.value());
        let header = self.context_header(position)?;
        let mut declarations = vec![format!("noncomputable def {name}{header} :=\n  Litex.replacement {domain} (fun _replacement_x _replacement_y => {raw}) {uniqueness}")];
        let image_term = self.context_application(&name, position);
        let set_id = set_store.primary_fact_id().value();
        declarations.push(format!(
            "theorem h_{set_id}{header} : Litex.IsSet {image_term} := Litex.isSet {image_term}"
        ));
        let xi = x.id.value();
        let yi = y.id.value();
        let predicate = self.compile_function_raw_predicate(
            relation,
            &formed,
            &HashMap::from([
                (x.id, format!("(Litex.denote _value_i{xi})")),
                (y.id, format!("(Litex.denote _value_i{yi})")),
            ]),
        )?;
        let h_prop = format!("h_{}", relation.fact_id().value());
        declarations.push(format!("theorem h_{}{header} : ∀ {} (_ : Litex.In _value_i{xi} {domain}) {} (_ : Litex.IsSet _value_i{yi}) ({h_prop} : {predicate}), Litex.In _value_i{yi} {image_term} := by\n  intro _ _ _value_i{xi} hx _ _ _value_i{yi} _ {h_prop}\n  exact Litex.replacementIntro {image_term} _value_i{xi} _value_i{yi} hx {h_prop}", intro.fact_id.value(), object_binder(x), object_binder(y)));
        declarations.push(self.compile_replacement_elimination(
            p,
            &image_term,
            &domain,
            &header,
            &formed,
        )?);
        Ok(declarations.join("\n\n"))
    }

    fn compile_replacement_uniqueness(
        &self,
        fact: &ForallFact,
        citation: &str,
        domain: &Obj,
    ) -> Result<String, LeanCompileError> {
        let mut arguments = Vec::new();
        let mut outputs = Vec::new();
        for group in &fact.typed_parameters.groups {
            for p in &group.params {
                let (value, sethood, membership) = match &group.param_type {
                    ParamType::Obj(a) if a.ir() == domain.ir() => {
                        ("_replacement_x", "(M.member_isSet hx)", "hx")
                    }
                    ParamType::Set(_) if outputs.is_empty() => {
                        outputs.push(p.id);
                        ("_replacement_y", "hy", "hy")
                    }
                    ParamType::Set(_) => {
                        outputs.push(p.id);
                        ("_replacement_z", "hz", "hz")
                    }
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "Replacement/UniquenessBinder",
                        ))
                    }
                };
                arguments.extend([
                    format!("(Litex.semanticObject {value} {sethood})"),
                    membership.into(),
                ]);
            }
        }
        for premise in &fact.dom_facts {
            let Fact::AtomicFact(AtomicFact::NormalAtomicFact(p)) = premise else {
                unreachable!()
            };
            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &p.body[1] else {
                unreachable!()
            };
            arguments.push(if *id == outputs[0] { "hp" } else { "hq" }.into());
        }
        let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
            fact.then_facts.as_slice()
        else {
            unreachable!()
        };
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &eq.left else {
            unreachable!()
        };
        let proof = format!("({citation} {})", arguments.join(" "));
        let proof = if *id == outputs[0] {
            proof
        } else {
            format!("(Litex.Same.symm {proof})")
        };
        Ok(format!("(by\n    intro _replacement_x hx _replacement_y _replacement_z hy hp hz hq\n    exact {proof}\n  )"))
    }

    fn compile_replacement_elimination(
        &self,
        p: &ExecHaveByReplacementAxiomStmtSuccessResult,
        image: &str,
        domain: &str,
        header: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let fact = forall_store(&p.elimination)?;
        let [group] = fact.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "Replacement/EliminationBinder",
            ));
        };
        let [y] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "Replacement/EliminationBinder",
            ));
        };
        if !matches!(&group.param_type, ParamType::Obj(a) if a.ir() == object(&p.statement.name).ir())
            || !fact.dom_facts.is_empty()
        {
            return Err(LeanCompileError::unsupported(
                "Replacement/EliminationDomain",
            ));
        }
        let [ExistOrAndChainAtomicFact::ExistFact(ex)] = fact.then_facts.as_slice() else {
            return Err(LeanCompileError::unsupported("Replacement/EliminationBody"));
        };
        let [x_group] = ex.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Replacement/EliminationBody"));
        };
        let [x] = x_group.params.as_slice() else {
            return Err(LeanCompileError::unsupported("Replacement/EliminationBody"));
        };
        let [QuantifierFreeFact::AtomicFact(AtomicFact::NormalAtomicFact(prop))] =
            ex.facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Replacement/EliminationBody"));
        };
        if !matches!(&x_group.param_type, ParamType::Obj(a) if a.ir() == p.statement.source_set.ir())
            || prop.predicate != p.statement.prop_name
            || prop.body != vec![object(x), object(y)]
        {
            return Err(LeanCompileError::unsupported(
                "Replacement/EliminationSubject",
            ));
        }
        let xi = x.id.value();
        let yi = y.id.value();
        let predicate = self.compile_function_raw_predicate(
            &Fact::AtomicFact(AtomicFact::NormalAtomicFact(prop.clone())),
            position,
            &HashMap::from([
                (x.id, format!("(Litex.denote _value_i{xi})")),
                (y.id, format!("(Litex.denote _value_i{yi})")),
            ]),
        )?;
        Ok(format!("theorem h_{}{header} : ∀ {} (_ : Litex.In _value_i{yi} {image}), ∃ (_value_i{xi} : Litex.Obj (M := M) M.Value), ∃ (_ : Litex.In _value_i{xi} {domain}), {predicate} := by\n  intro _ _ _value_i{yi} hy\n  exact Litex.replacementElim {image} _value_i{yi} hy", fact.fact_id.value(), object_binder(y)))
    }
}
