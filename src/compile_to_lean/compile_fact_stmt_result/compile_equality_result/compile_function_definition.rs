use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{
    AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof,
    FunctionBodyNormalizationProof, FunctionBodySourceProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition,
    EqualitySearchProofByObjectDefinition,
};
use crate::prelude::*;
use std::collections::HashMap;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::{
    ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody,
    ParentEqualitySide,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_definition(
        &self,
        fact: &EqualFact,
        proof: &EqualitySearchProofByObjectDefinition,
        parent_wd: Option<&EqualFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            EqualitySearchProofByObjectDefinition::ByFnApplication(proof) => {
                match proof {
                    EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof) => {
                        let residual = source_subject(&proof.residual_equal)?;
                        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) = &residual else {
                            return Err(LeanCompileError::new(
                                "FunctionDefinition/ResidualFamily",
                                "Function-body replay has a non-equality residual.",
                            ));
                        };
                        if residual.left.ir() != proof.normalization.expanded_body.ir() {
                            return Err(LeanCompileError::new("FunctionDefinition/ResidualBody", "The actual residual does not begin at the recorded normalized body."));
                        }
                        let (original, reversed) = if residual.right.ir() == fact.right.ir() {
                            (&fact.left, false)
                        } else if residual.right.ir() == fact.left.ir() {
                            (&fact.right, true)
                        } else {
                            return Err(LeanCompileError::new("FunctionDefinition/ResidualEndpoint", "The residual does not end at the source's other equality endpoint."));
                        };
                        let normalization = self.compile_function_normalization(
                            original,
                            &proof.normalization,
                            position,
                        )?;
                        let completed = SourcePosition {
                            parent: Some(position),
                            owner: SourceOwner::FunctionNormalization(&proof.normalization),
                            before: usize::MAX,
                        };
                        let residual = self.compile_verify(&proof.residual_equal, &completed)?;
                        let equality = format!("(({normalization}).trans {})", residual.1);
                        Ok(if reversed {
                            format!("({equality}).symm")
                        } else {
                            equality
                        })
                    }
                    EqualitySearchProofByFnApplicationObjectDefinition::BothFunctionBodies(
                        proof,
                    ) => {
                        let left = self.compile_function_normalization(
                            &fact.left,
                            &proof.left_normalization,
                            position,
                        )?;
                        let after_left = SourcePosition {
                            parent: Some(position),
                            owner: SourceOwner::FunctionNormalization(&proof.left_normalization),
                            before: usize::MAX,
                        };
                        let right = self.compile_function_normalization(
                            &fact.right,
                            &proof.right_normalization,
                            &after_left,
                        )?;
                        let completed = SourcePosition {
                            parent: Some(&after_left),
                            owner: SourceOwner::FunctionNormalization(&proof.right_normalization),
                            before: usize::MAX,
                        };
                        match source_subject(&proof.residual_equal)? {
                        Fact::AtomicFact(AtomicFact::EqualFact(residual))
                            if residual.left.ir() == proof.left_normalization.expanded_body.ir()
                                && residual.right.ir() == proof.right_normalization.expanded_body.ir() => {}
                        _ => return Err(LeanCompileError::new("FunctionDefinition/ResidualEndpoints", "The two-body residual differs from the exact ordered normalized bodies.")),
                    }
                        let residual = self.compile_verify(&proof.residual_equal, &completed)?;
                        Ok(format!(
                            "(({left}).trans (({}).trans ({right}).symm))",
                            residual.1
                        ))
                    }
                    EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqualCaseByCase(
                        _,
                    ) => Err(LeanCompileError::unsupported("FunctionDefinition/Cases")),
                    EqualitySearchProofByFnApplicationObjectDefinition::HaveFnByInduc(proof) => {
                        self.compile_recursive_unfold_result(fact, proof, parent_wd, position)
                    }
                    EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                        proof,
                    ) => {
                        let parent_wd = parent_wd.ok_or_else(|| LeanCompileError::new(
                            "FunctionDefinition/ParentFormation",
                            "Parent-checked beta requires this equality's original formation result.",
                        ))?;
                        self.compile_parent_checked_beta(fact, proof, parent_wd, position)
                    }
                }
            }
            EqualitySearchProofByObjectDefinition::CartesianDefinition(_) => Err(
                LeanCompileError::unsupported("FunctionDefinition/Cartesian"),
            ),
            EqualitySearchProofByObjectDefinition::ByIdentifier(_) => Err(
                LeanCompileError::unsupported("FunctionDefinition/Identifier"),
            ),
            EqualitySearchProofByObjectDefinition::ByTemplate(_) => {
                Err(LeanCompileError::unsupported("FunctionDefinition/Template"))
            }
        }
    }

    fn compile_parent_checked_beta(
        &self,
        fact: &EqualFact,
        proof: &ByParentCheckedBetaObjectDefinitionProof,
        parent_wd: &EqualFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_object(&fact.left, &parent_wd.left)?;
        ensure_object(&fact.right, &parent_wd.right)?;
        match proof {
            ByParentCheckedBetaObjectDefinitionProof::OneSide(proof) => {
                let (application, other, wd, reversed) = match proof.parent_well_defined_side {
                    ParentEqualitySide::Left => (&fact.left, &fact.right, &parent_wd.left, false),
                    ParentEqualitySide::Right => (&fact.right, &fact.left, &parent_wd.right, true),
                };
                if proof.residual_equal.left.ir() != proof.expanded_body.ir()
                    || proof.residual_equal.right.ir() != other.ir()
                {
                    return Err(LeanCompileError::new(
                        "FunctionDefinition/ParentResidual",
                        "The parent-checked residual differs from the exact expanded and other endpoints.",
                    ));
                }
                let beta = self.compile_parent_checked_function_body(
                    application,
                    wd,
                    &proof.function_body,
                    &proof.expanded_body,
                    position,
                )?;
                let residual = self.compile_equality_search(
                    &proof.residual_equal,
                    &proof.residual_proof,
                    position,
                )?;
                let equality = format!("(({beta}).trans {residual})");
                Ok(if reversed {
                    format!("({equality}).symm")
                } else {
                    equality
                })
            }
            ByParentCheckedBetaObjectDefinitionProof::TwoSides(proof) => {
                if proof.residual_equal.left.ir() != proof.left_expanded_body.ir()
                    || proof.residual_equal.right.ir() != proof.right_expanded_body.ir()
                {
                    return Err(LeanCompileError::new(
                        "FunctionDefinition/ParentResidual",
                        "The two-sided parent residual differs from the ordered expanded endpoints.",
                    ));
                }
                let left = self.compile_parent_checked_function_body(
                    &fact.left,
                    &parent_wd.left,
                    &proof.left_function_body,
                    &proof.left_expanded_body,
                    position,
                )?;
                let right = self.compile_parent_checked_function_body(
                    &fact.right,
                    &parent_wd.right,
                    &proof.right_function_body,
                    &proof.right_expanded_body,
                    position,
                )?;
                let residual = self.compile_equality_search(
                    &proof.residual_equal,
                    &proof.residual_proof,
                    position,
                )?;
                Ok(format!(
                    "(({left}).trans (({residual}).trans ({right}).symm))"
                ))
            }
        }
    }

    fn compile_parent_checked_function_body(
        &self,
        application: &Obj,
        parent_wd: &ObjWellDefinedProof,
        source: &ParentCheckedBetaFunctionBody,
        expanded: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(call) = application else {
            return Err(LeanCompileError::new(
                "FunctionDefinition/ParentApplication",
                "The parent beta endpoint is not a function application.",
            ));
        };
        let ObjWellDefinedProof::ByDef {
            obj,
            proof: ObjWellDefinedProofByDef::FnObj(call_wd),
        } = parent_wd
        else {
            return Err(LeanCompileError::new(
                "FunctionDefinition/ParentCallWD",
                "Parent beta has no original selected call constructor.",
            ));
        };
        if obj.ir() != application.ir() {
            return Err(LeanCompileError::new(
                "FunctionDefinition/ParentCallWD",
                "The selected parent constructor certifies another application.",
            ));
        }
        let actual_domain = match call_wd.domain_fn_set.as_ref() {
            Some(FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. })
            | Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }) => fn_set,
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/ParentCallDomain",
                ))
            }
        };
        let (function, known_path) = match source {
            ParentCheckedBetaFunctionBody::KnownAnonymousFunction {
                function,
                function_equal,
                checked_domain,
            } => {
                if checked_domain != actual_domain {
                    return Err(LeanCompileError::new("FunctionDefinition/ParentDomain", "The beta body's checked domain differs from the exact parent call evidence."));
                }
                if !matches!(call.head.as_ref(), FnObjHead::Identifier(_)) {
                    return Err(LeanCompileError::new(
                        "FunctionDefinition/ParentHead",
                        "A known-body beta proof has another source head family.",
                    ));
                }
                (function, Some(function_equal))
            }
            ParentCheckedBetaFunctionBody::AnonymousLiteral => {
                let FnObjHead::AnonymousFnLiteral(function) = call.head.as_ref() else {
                    return Err(LeanCompileError::new(
                        "FunctionDefinition/ParentHead",
                        "Literal beta evidence has another original head family.",
                    ));
                };
                (function.as_ref(), None)
            }
            ParentCheckedBetaFunctionBody::TemplateAnonymousFunction { .. } => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/ParentTemplate",
                ))
            }
            ParentCheckedBetaFunctionBody::KnownFiniteFunctionCoordinate { .. }
            | ParentCheckedBetaFunctionBody::ReturnedFiniteFunctionCoordinate { .. } => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/ParentFiniteCoordinate",
                ))
            }
            ParentCheckedBetaFunctionBody::ReturnedAnonymousFunctionApplication { .. }
            | ParentCheckedBetaFunctionBody::ReturnedKnownFunctionApplication { .. } => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/ParentReturnedFunction",
                ))
            }
        };
        if !function_domains_alpha_equal(&function.body, actual_domain)
            || call.body.len() != 1
            || !(1..=2).contains(&call.body[0].len())
        {
            return Err(LeanCompileError::new("FunctionDefinition/ParentDomain", "The selected literal does not match the parent's complete one/two-argument domain."));
        }
        let parameters = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if parameters.len() != call.body[0].len() {
            return Err(LeanCompileError::new(
                "FunctionDefinition/ParentArguments",
                "The original beta arguments differ from the literal's ordered parameters.",
            ));
        }
        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(&call.body[0]) {
            if substitution
                .insert(parameter.id, argument.as_ref().clone())
                .is_some()
            {
                return Err(LeanCompileError::new(
                    "FunctionDefinition/ParentParameterIdentity",
                    "The selected literal repeats a source binder identity.",
                ));
            }
        }
        if !instantiated_object_matches(&function.equal_to, expanded, &substitution) {
            return Err(LeanCompileError::new("FunctionDefinition/ParentSubstitution", "The captured beta endpoint is not the exact binder-ID substitution of the selected body."));
        }
        let actual = self.compile_wd(parent_wd, position)?;
        let (literal, head_equal) = if let Some(path) = known_path {
            let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
            let head = function_head_object(call.head.as_ref())?;
            let equality = self.compile_equality_path(&head, &literal, path, position)?;
            (self.compile_object_reference(&literal, position)?, equality)
        } else {
            (
                "_litex_original.val.function".to_string(),
                "rfl".to_string(),
            )
        };
        let (constructor_arguments, target) =
            self.compile_function_constructor_arguments(&function.body, position)?;
        let guard = self.compile_function_guard_template(&function.body, position)?;
        let body = self.compile_function_body_template(function, position)?;
        let endpoint = self.compile_normalization_value(expanded, position)?;
        let application_value = self.compile_normalization_value(application, position)?;
        let (argument, domain_proof, body_equality) = if parameters.len() == 1 {
            (
                "(Litex.denote _litex_original.val.argument)".to_string(),
                format!("((Litex.FunctionSignature.{} {constructor_arguments} {guard} _).mpr _litex_original.wd.2)", if target { "oneTarget_domain" } else { "one_domain" }),
                format!("(show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = {endpoint} from rfl)"),
            )
        } else {
            (
                "(Litex.FunctionSemantics.pairValue (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))".to_string(),
                format!("((Litex.FunctionSignature.{} {constructor_arguments} {guard} _ _).mpr _litex_original.wd.2)", if target { "twoTarget_domain" } else { "two_domain" }),
                format!("(by change {body} (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))).1 (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))).2 = {endpoint}; simp only [Litex.FunctionSemantics.unpair_pair])"),
            )
        };
        Ok(format!("(show {application_value} = {endpoint} from by\n  let _litex_original := {actual}\n  let _litex_formula := {literal}\n  have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := {head_equal}\n  have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f {argument}) _litex_head_eq\n  have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd {argument} {domain_proof}\n  exact _litex_call_eq.trans (_litex_beta.trans {body_equality})\n)"))
    }

    fn compile_function_normalization(
        &self,
        original: &Obj,
        proof: &FunctionBodyNormalizationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.expansions.is_empty() || proof.expansions.len() > 64 {
            return Err(LeanCompileError::new(
                "FunctionDefinition/ExpansionArity",
                "Body normalization needs its nonempty bounded chronological beta steps.",
            ));
        }
        // This temporary AST is only the certificate's successive substitution
        // endpoint. It is never a new source producer or a compiler object world.
        let mut current = original.clone();
        let original_value = self.compile_normalization_value(original, position)?;
        let mut equality = format!("(Eq.refl {original_value})");
        let normalization = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::FunctionNormalization(proof),
            before: 0,
        };
        for (index, expansion) in proof.expansions.iter().enumerate() {
            let prior = SourcePosition {
                before: index,
                ..normalization
            };
            let FunctionBodyExpansionProof::Anonymous(expansion) = expansion else {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/FiniteCoordinate",
                ));
            };
            let beta = self.compile_anonymous_function_expansion(expansion, &prior)?;
            let completed = SourcePosition {
                parent: Some(&prior),
                owner: SourceOwner::FunctionExpansion(expansion),
                before: 3,
            };
            let Some((next, embedded)) = self.embed_recorded_function_expansion(
                &current,
                &expansion.application,
                &expansion.continued_body,
                &beta,
                &completed,
            )?
            else {
                return Err(LeanCompileError::new("FunctionDefinition/ExpansionOrder", "The recorded application is absent from the current chronological substitution endpoint."));
            };
            equality = format!("(({equality}).trans {embedded})");
            current = next;
        }
        if current.ir() != proof.expanded_body.ir() {
            return Err(LeanCompileError::new(
                "FunctionDefinition/NormalizedEndpoint",
                "The recorded beta substitutions do not produce the declared normalized body.",
            ));
        }
        Ok(equality)
    }

    pub(in crate::compile_to_lean) fn compile_anonymous_function_expansion(
        &self,
        proof: &AnonymousFunctionBodyExpansionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(application) = &proof.application else {
            return Err(LeanCompileError::new(
                "FunctionDefinition/Application",
                "An anonymous beta step must own its actual function application.",
            ));
        };
        let Obj::FnObj(literal_application) = proof.body_application_well_defined.obj() else {
            return Err(LeanCompileError::new(
                "FunctionDefinition/LiteralApplication",
                "Selected-body WD certifies another object family.",
            ));
        };
        let FnObjHead::AnonymousFnLiteral(function) = literal_application.head.as_ref() else {
            return Err(LeanCompileError::new(
                "FunctionDefinition/LiteralHead",
                "Selected-body WD does not contain the checked anonymous function literal.",
            ));
        };
        if application.body.len() != 1
            || literal_application.body != application.body
            || proof.continued_body.ir() != proof.expanded_body.ir()
        {
            return Err(LeanCompileError::unsupported(
                "FunctionDefinition/CurriedApplication",
            ));
        }
        let parameters = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        let arguments = &application.body[0];
        if parameters.len() != arguments.len() || !(1..=2).contains(&arguments.len()) {
            return Err(LeanCompileError::new(
                "FunctionDefinition/Arguments",
                "Beta arguments differ from the selected literal's ordered parameters.",
            ));
        }
        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            if substitution
                .insert(parameter.id, argument.as_ref().clone())
                .is_some()
            {
                return Err(LeanCompileError::new(
                    "FunctionDefinition/ParameterIdentity",
                    "The selected literal repeats a source binder identity.",
                ));
            }
        }
        if !instantiated_object_matches(&function.equal_to, &proof.expanded_body, &substitution) {
            return Err(LeanCompileError::new("FunctionDefinition/Substitution", "The captured expanded body is not the exact binder-ID substitution of the selected literal."));
        }
        let step = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::FunctionExpansion(proof),
            before: 0,
        };
        ensure_object(&proof.application, &proof.application_well_defined)?;
        let actual = self.compile_wd(&proof.application_well_defined, &step)?;
        let path_position = SourcePosition { before: 1, ..step };
        let head = function_head_object(application.head.as_ref())?;
        let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone()));
        let head_equal = match &proof.function_body {
            FunctionBodySourceProof::KnownEquality(path) => {
                self.compile_equality_path(&head, &literal, path, &path_position)?
            }
            FunctionBodySourceProof::Template { .. } => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/TemplateBody",
                ))
            }
        };
        let literal_position = SourcePosition { before: 2, ..step };
        let selected = self.compile_wd(&proof.body_application_well_defined, &literal_position)?;
        let completed = SourcePosition { before: 3, ..step };
        let (constructor_arguments, target) =
            self.compile_function_constructor_arguments(&function.body, &completed)?;
        let guard = self.compile_function_guard_template(&function.body, &completed)?;
        let body = self.compile_function_body_template(function, &completed)?;
        let expanded = self.compile_normalization_value(&proof.expanded_body, &completed)?;
        let names = format!("let _litex_original := {actual}\nlet _litex_literal := {selected}");
        if arguments.len() == 1 {
            let domain_law = if target {
                "oneTarget_domain"
            } else {
                "one_domain"
            };
            let beta_law = if target {
                "callFormulaTarget_denote"
            } else {
                "callFormula_denote"
            };
            let return_proof = format!("(by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.{domain_law} {constructor_arguments} {guard} _x).mpr ⟨_hx, _hg⟩))");
            Ok(format!("(by\n  {}\n  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.argument)\n  have _litex_beta := Litex.{beta_law} {constructor_arguments} {guard} {body} {return_proof} _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2\n  exact _litex_call_eq.trans (_litex_beta.trans (show {body} (Litex.denote _litex_literal.val.argument) = {expanded} from rfl))\n)", names.replace('\n', "\n  ")))
        } else {
            let domain_law = if target {
                "twoTarget_domain"
            } else {
                "two_domain"
            };
            let beta_law = if target {
                "callFormula2Target_denote"
            } else {
                "callFormula2_denote"
            };
            let output = if target {
                format!(
                    "(Litex.denote {})",
                    self.compile_object_reference(&function.body.ret_set, &completed)?
                )
            } else {
                let output = self.compile_numeric_carrier(&function.body.ret_set, &completed)?;
                format!(
                    "(M.standard Litex.StandardSetValue.{})",
                    standard_value_constructor(&output)?
                )
            };
            let return_proof = format!("(by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FunctionSemantics.pairValue (M := M) _x _y) ((Litex.FunctionSignature.{domain_law} {constructor_arguments} {guard} _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ({body} (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).1 (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).2) {output} at _h; simpa only [Litex.FunctionSemantics.unpair_pair] using _h)");
            Ok(format!("(by\n  {}\n  have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)\n  have _litex_beta := Litex.{beta_law} {constructor_arguments} {guard} {body} {return_proof} _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2\n  exact _litex_call_eq.trans (_litex_beta.trans (show {body} (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = {expanded} from rfl))\n)", names.replace('\n', "\n  ")))
        }
    }

    pub(in crate::compile_to_lean) fn compile_normalization_value(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match object {
            Obj::Literal(Literal::Number(number)) => {
                Ok(format!("(M.number {})", number_literal(number, "ℂ")?))
            }
            Obj::ArithmeticOperator(operator) => {
                let (operation, children) = normalization_arithmetic_children(operator)?;
                let values = children
                    .into_iter()
                    .map(|child| self.compile_normalization_value(child, position))
                    .collect::<Result<Vec<_>, _>>()?;
                let operation = arithmetic_operation_term(operation);
                Ok(format!("({operation} {})", values.join(" ")))
            }
            Obj::FnObj(application)
                if application.body.len() == 1 && (1..=2).contains(&application.body[0].len()) =>
            {
                let head = function_head_object(application.head.as_ref())?;
                let function = self.compile_normalization_value(&head, position)?;
                let values = application.body[0]
                    .iter()
                    .map(|argument| self.compile_normalization_value(argument, position))
                    .collect::<Result<Vec<_>, _>>()?;
                let argument = if values.len() == 1 {
                    values[0].clone()
                } else {
                    format!(
                        "(Litex.FunctionSemantics.pairValue (M := M) {} {})",
                        values[0], values[1]
                    )
                };
                Ok(format!(
                    "(Litex.FunctionSemantics.callValue (M := M) {function} {argument})"
                ))
            }
            _ => Ok(format!(
                "(Litex.denote {})",
                self.compile_object_reference(object, position)?
            )),
        }
    }

    fn embed_recorded_function_expansion(
        &self,
        current: &Obj,
        application: &Obj,
        replacement: &Obj,
        beta: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(Obj, String)>, LeanCompileError> {
        if current.ir() == application.ir() {
            return Ok(Some((replacement.clone(), beta.to_string())));
        }
        match current {
            Obj::ArithmeticOperator(operator) => {
                let (operation, _) = normalization_arithmetic_children(operator)?;
                let operation = arithmetic_operation_term(operation);
                let mut rebuilt = operator.clone();
                let children = normalization_arithmetic_children_mut(&mut rebuilt)?;
                let count = children.len();
                for (index, child) in children.into_iter().enumerate() {
                    if let Some((next, equality)) = self.embed_recorded_function_expansion(
                        child,
                        application,
                        replacement,
                        beta,
                        position,
                    )? {
                        **child = next;
                        let proof = if count == 1 {
                            format!("(congrArg {operation} {equality})")
                        } else if index == 0 {
                            format!("(congrArg₂ {operation} {equality} rfl)")
                        } else {
                            format!("(congrArg₂ {operation} rfl {equality})")
                        };
                        return Ok(Some((Obj::ArithmeticOperator(rebuilt), proof)));
                    }
                }
                Ok(None)
            }
            Obj::FnObj(call) if call.body.len() == 1 && (1..=2).contains(&call.body[0].len()) => {
                let function = self.compile_normalization_value(
                    &function_head_object(call.head.as_ref())?,
                    position,
                )?;
                let mut rebuilt = call.clone();
                let count = rebuilt.body[0].len();
                for (index, child) in rebuilt.body[0].iter_mut().enumerate() {
                    if let Some((next, equality)) = self.embed_recorded_function_expansion(
                        child,
                        application,
                        replacement,
                        beta,
                        position,
                    )? {
                        **child = next;
                        let proof = if count == 1 {
                            format!("(congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) {function} _x) {equality})")
                        } else {
                            let pair = if index == 0 {
                                format!("(congrArg₂ (Litex.FunctionSemantics.pairValue (M := M)) {equality} rfl)")
                            } else {
                                format!("(congrArg₂ (Litex.FunctionSemantics.pairValue (M := M)) rfl {equality})")
                            };
                            format!("(congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) {function} _x) {pair})")
                        };
                        return Ok(Some((Obj::FnObj(rebuilt), proof)));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }
}

fn function_head_object(head: &FnObjHead) -> Result<Obj, LeanCompileError> {
    match head {
        FnObjHead::Identifier(head) => Ok(Obj::Identifier(head.clone())),
        FnObjHead::AnonymousFnLiteral(function) => Ok(Obj::FunctionSpace(
            FunctionSpace::AnonymousFn(function.as_ref().clone()),
        )),
        FnObjHead::Object(object) => Ok(object.as_ref().clone()),
        FnObjHead::FieldAccess(_) | FnObjHead::InstantiatedTemplateObj(_) => {
            Err(LeanCompileError::unsupported("FunctionDefinition/Head"))
        }
    }
}

fn normalization_arithmetic_children(
    operator: &ArithmeticOperator,
) -> Result<(&'static str, Vec<&Obj>), LeanCompileError> {
    match operator {
        ArithmeticOperator::Add(value) => Ok(("addValue", vec![&value.left, &value.right])),
        ArithmeticOperator::Sub(value) => Ok(("subValue", vec![&value.left, &value.right])),
        ArithmeticOperator::Mul(value) => Ok(("mulValue", vec![&value.left, &value.right])),
        ArithmeticOperator::Div(value) => Ok(("divValue", vec![&value.left, &value.right])),
        ArithmeticOperator::Pow(value) => Ok(("powValue", vec![&value.base, &value.exponent])),
        ArithmeticOperator::Neg(value) => Ok(("negValue", vec![&value.arg])),
        ArithmeticOperator::Abs(value) => Ok(("absValue", vec![&value.arg])),
        _ => Err(LeanCompileError::unsupported(
            "FunctionDefinition/ArithmeticContext",
        )),
    }
}

fn normalization_arithmetic_children_mut(
    operator: &mut ArithmeticOperator,
) -> Result<Vec<&mut Box<Obj>>, LeanCompileError> {
    match operator {
        ArithmeticOperator::Add(value) => Ok(vec![&mut value.left, &mut value.right]),
        ArithmeticOperator::Sub(value) => Ok(vec![&mut value.left, &mut value.right]),
        ArithmeticOperator::Mul(value) => Ok(vec![&mut value.left, &mut value.right]),
        ArithmeticOperator::Div(value) => Ok(vec![&mut value.left, &mut value.right]),
        ArithmeticOperator::Pow(value) => Ok(vec![&mut value.base, &mut value.exponent]),
        ArithmeticOperator::Neg(value) => Ok(vec![&mut value.arg]),
        ArithmeticOperator::Abs(value) => Ok(vec![&mut value.arg]),
        _ => Err(LeanCompileError::unsupported(
            "FunctionDefinition/ArithmeticContext",
        )),
    }
}
