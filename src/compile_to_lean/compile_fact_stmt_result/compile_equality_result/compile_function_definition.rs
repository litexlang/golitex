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
                        let equality_type = format!(
                            "{} = {}",
                            self.compile_normalization_value(original, position)?,
                            self.compile_normalization_value(&residual.right, &completed)?,
                        );
                        let compiled_residual =
                            self.compile_verify(&proof.residual_equal, &completed)?;
                        let residual_type = format!(
                            "{} = {}",
                            self.compile_normalization_value(&residual.left, &completed)?,
                            self.compile_normalization_value(&residual.right, &completed)?,
                        );
                        let equality = format!(
                            "(show {equality_type} from by\n  have _litex_residual : {} := {}\n  exact ({normalization}).trans _litex_residual)",
                            residual_type.replace('\n', "\n  "), compiled_residual.1.replace('\n', "\n  "),
                        );
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
                        let residual_subject = source_subject(&proof.residual_equal)?;
                        let residual = match &residual_subject {
                        Fact::AtomicFact(AtomicFact::EqualFact(residual))
                            if residual.left.ir() == proof.left_normalization.expanded_body.ir()
                                && residual.right.ir() == proof.right_normalization.expanded_body.ir() => residual,
                        _ => return Err(LeanCompileError::new("FunctionDefinition/ResidualEndpoints", "The two-body residual differs from the exact ordered normalized bodies.")),
                    };
                        let compiled_residual =
                            self.compile_verify(&proof.residual_equal, &completed)?;
                        let equality_type = format!(
                            "{} = {}",
                            self.compile_normalization_value(&fact.left, position)?,
                            self.compile_normalization_value(&fact.right, &after_left)?,
                        );
                        let residual_type = format!(
                            "{} = {}",
                            self.compile_normalization_value(&residual.left, &completed)?,
                            self.compile_normalization_value(&residual.right, &completed)?,
                        );
                        Ok(format!(
                            "(show {equality_type} from by\n  have _litex_residual : {} := {}\n  exact ({left}).trans (_litex_residual.trans ({right}).symm))",
                            residual_type.replace('\n', "\n  "), compiled_residual.1.replace('\n', "\n  "),
                        ))
                    }
                    EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqualCaseByCase(
                        proof,
                    ) => self.compile_piecewise_unfold_result(fact, proof, parent_wd, position),
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
            EqualitySearchProofByObjectDefinition::NativeMatrix(_) => Err(
                LeanCompileError::unsupported("FunctionDefinition/NativeMatrix"),
            ),
            EqualitySearchProofByObjectDefinition::CartesianDefinition(proof) => {
                self.compile_cartesian_definition(fact, proof, position)
            }
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
        if let ParentCheckedBetaFunctionBody::Composition {
            composition,
            function_equal,
        } = source
        {
            return self.compile_composition_beta(
                application,
                parent_wd,
                composition,
                function_equal,
                expanded,
                position,
            );
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
            ParentCheckedBetaFunctionBody::NativeMatrix(_) => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/NativeMatrix",
                ))
            }
            ParentCheckedBetaFunctionBody::Composition { .. } => {
                return Err(LeanCompileError::unsupported(
                    "function definition/Composition",
                ))
            }
            ParentCheckedBetaFunctionBody::StructField(_) => {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/StructField",
                ))
            }
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
            || !(1..=3).contains(&call.body[0].len())
        {
            return Err(LeanCompileError::new("FunctionDefinition/ParentDomain", "The selected literal does not match the parent's complete ordered argument domain."));
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
        if !Self::function_uses_numeric_interface(&function.body) {
            let endpoint = self.compile_normalization_value(expanded, position)?;
            let application_value = self.compile_normalization_value(application, position)?;
            let body_equality = self.compile_packed_function_body_equality(
                function,
                &call.body[0],
                "_litex_original.val.argument",
                &endpoint,
                position,
            )?;
            return Ok(format!("(show {application_value} = {endpoint} from by\n  let _litex_original := {actual}\n  let _litex_formula := {literal}\n  have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := {head_equal}\n  have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq\n  have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) _litex_original.wd.2\n  exact _litex_call_eq.trans (_litex_beta.trans {body_equality})\n)"));
        }
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
                "(Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))".to_string(),
                format!("((Litex.FunctionSignature.{} {constructor_arguments} {guard} _ _).mpr _litex_original.wd.2)", if target { "twoTarget_domain" } else { "two_domain" }),
                format!("(by change {body} (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))).2 = {endpoint}; simp only [Litex.FiniteFunction.unpack_pack2])"),
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
            let (application, expanded, continued, beta, owner, before) = match expansion {
                FunctionBodyExpansionProof::Anonymous(step) => (
                    &step.application,
                    &step.expanded_body,
                    &step.continued_body,
                    self.compile_anonymous_function_expansion(step, &prior)?,
                    SourceOwner::FunctionExpansion(step),
                    3,
                ),
                FunctionBodyExpansionProof::FiniteCoordinate(step) => (
                    &step.application,
                    &step.expanded_body,
                    &step.continued_body,
                    self.compile_finite_coordinate_expansion(step, &prior)?,
                    SourceOwner::FiniteExpansion(step),
                    1,
                ),
                FunctionBodyExpansionProof::Composition(step) => {
                    if step.expanded_body.ir() != step.continued_body.ir() {
                        return Err(LeanCompileError::unsupported("Composition/Continuation"));
                    }
                    (
                        &step.application,
                        &step.expanded_body,
                        &step.continued_body,
                        self.compile_composition_beta(
                            &step.application,
                            &step.application_well_defined,
                            &step.composition,
                            &step.function_equal,
                            &step.expanded_body,
                            &prior,
                        )?,
                        SourceOwner::CompositionExpansion(step),
                        1,
                    )
                }
            };
            let completed = SourcePosition {
                parent: Some(&prior),
                owner,
                before,
            };
            let Some((next, embedded)) = self.embed_recorded_function_expansion(
                &current,
                application,
                expanded,
                continued,
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
        if application.body.len() != 1 || literal_application.body != application.body {
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
        if parameters.len() != arguments.len() || !(1..=3).contains(&arguments.len()) {
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
        // A beta proof can be the receiver of .trans, with no expected type.
        // Keep its original endpoints explicit for every function interface.
        let application_value = self.compile_normalization_value(&proof.application, &step)?;
        let expanded = self.compile_normalization_value(&proof.expanded_body, &completed)?;
        if !Self::function_uses_numeric_interface(&function.body) {
            let body_equality = self.compile_packed_function_body_equality(
                function,
                arguments,
                "_litex_literal.val.argument",
                &expanded,
                &completed,
            )?;
            return Ok(format!("(show {application_value} = {expanded} from by\n  let _litex_original := {actual}\n  let _litex_literal := {selected}\n  have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.argument)\n  have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2\n  exact _litex_call_eq.trans (_litex_beta.trans {body_equality})\n)"));
        }
        let (constructor_arguments, target) =
            self.compile_function_constructor_arguments(&function.body, &completed)?;
        let guard = self.compile_function_guard_template(&function.body, &completed)?;
        let body = self.compile_function_body_template(function, &completed)?;
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
            Ok(format!("(show {application_value} = {expanded} from by\n  {}\n  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.argument)\n  have _litex_beta := Litex.{beta_law} {constructor_arguments} {guard} {body} {return_proof} _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2\n  exact _litex_call_eq.trans (_litex_beta.trans (show {body} (Litex.denote _litex_literal.val.argument) = {expanded} from rfl))\n)", names.replace('\n', "\n  ")))
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
            let return_proof = format!("(by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.{domain_law} {constructor_arguments} {guard} _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ({body} (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) {output} at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h)");
            Ok(format!("(show {application_value} = {expanded} from by\n  {}\n  have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)\n  have _litex_beta := Litex.{beta_law} {constructor_arguments} {guard} {body} {return_proof} _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2\n  exact _litex_call_eq.trans (_litex_beta.trans (show {body} (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = {expanded} from rfl))\n)", names.replace('\n', "\n  ")))
        }
    }

    fn compile_packed_function_body_equality(
        &self,
        function: &AnonymousFn,
        arguments: &[Box<Obj>],
        packed: &str,
        expanded: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let packed_body = self.compile_function_packed_body_template(function, position)?;
        let body = self.compile_function_body_template(function, position)?;
        let values = arguments
            .iter()
            .map(|argument| self.compile_normalization_value(argument, position))
            .collect::<Result<Vec<_>, _>>()?;
        let equality = self.compile_function_packed_application_equality(&body, &values)?;
        Ok(format!(
            "(by change {packed_body} (Litex.denote {packed}) = {expanded}; exact {equality})"
        ))
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
            Obj::ProductShape(shape) => {
                let (constructor, children) = match shape {
                    ProductShape::Tuple(value) => ("tupleValue", &value.args),
                    ProductShape::Cart(value) => ("cartValue", &value.args),
                };
                let values = children
                    .iter()
                    .map(|child| self.compile_normalization_value(child, position))
                    .collect::<Result<Vec<_>, _>>()?;
                let vector = if values.is_empty() {
                    "(fun i : Fin 0 => Fin.elim0 i)".into()
                } else {
                    format!("![{}]", values.join(", "))
                };
                Ok(format!(
                    "(Litex.FiniteFunction.{constructor} (M := M) {vector})"
                ))
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                // A recorded beta substitution supplies a semantic endpoint,
                // not a new source constructor with a second WD registration.
                self.compile_function_literal_value(function, position, &HashMap::new())
            }
            Obj::SetFormer(SetFormer::SetBuilder(_)) => {
                // Beta compares semantic values. The selected literal and the
                // equality endpoints retain their separately checked WD; this
                // internal substitution endpoint needs no second constructor.
                self.compile_function_raw_expression_bound(object, position, &HashMap::new())
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(value)) => Ok(format!(
                "(Litex.sqrtValue (M := M) {})",
                self.compile_normalization_value(&value.arg, position)?
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(value)) => Ok(format!(
                "(Litex.absValue (M := M) {})",
                self.compile_normalization_value(&value.arg, position)?
            )),
            Obj::ArithmeticOperator(_) | Obj::IntegerOperator(_) => {
                let (operation, children) = normalization_operation_children(object)?;
                let values = children
                    .into_iter()
                    .map(|child| self.compile_normalization_value(child, position))
                    .collect::<Result<Vec<_>, _>>()?;
                let operation = arithmetic_operation_term(operation);
                Ok(format!("({operation} {})", values.join(" ")))
            }
            Obj::FnObj(application)
                if !application.body.is_empty()
                    && application
                        .body
                        .iter()
                        .all(|group| (1..=3).contains(&group.len())) =>
            {
                let head = function_head_object(application.head.as_ref())?;
                let mut function = self.compile_normalization_value(&head, position)?;
                for group in &application.body {
                    let values = group
                        .iter()
                        .map(|argument| self.compile_normalization_value(argument, position))
                        .collect::<Result<Vec<_>, _>>()?;
                    let argument = if values.len() == 1 {
                        values[0].clone()
                    } else {
                        format!(
                            "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                            values.join(", ")
                        )
                    };
                    function = format!(
                        "(Litex.FunctionSemantics.callValue (M := M) {function} {argument})"
                    );
                }
                Ok(function)
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
        continued: &Obj,
        beta: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Option<(Obj, String)>, LeanCompileError> {
        if current.ir() == application.ir() {
            if replacement.ir() != continued.ir() {
                return Err(LeanCompileError::unsupported(
                    "FunctionDefinition/Continuation",
                ));
            }
            return Ok(Some((replacement.clone(), beta.to_string())));
        }
        if let (Obj::FnObj(call), Obj::FnObj(prefix)) = (current, application) {
            if prefix.body.len() == 1
                && call.body.len() > 1
                && call.head == prefix.head
                && call.body[0] == prefix.body[0]
            {
                let Obj::FnObj(next) = continued else {
                    return Err(LeanCompileError::unsupported(
                        "FunctionDefinition/Continuation",
                    ));
                };
                let (head_matches, prior_groups) = match replacement {
                    Obj::FnObj(value) => (value.head == next.head, value.body.as_slice()),
                    _ => (
                        function_head_object(next.head.as_ref())?.ir() == replacement.ir(),
                        &[][..],
                    ),
                };
                if !head_matches
                    || !prior_groups
                        .iter()
                        .chain(&call.body[1..])
                        .eq(next.body.iter())
                {
                    return Err(LeanCompileError::unsupported(
                        "FunctionDefinition/Continuation",
                    ));
                }
                let mut equality = beta.to_string();
                for group in &call.body[1..] {
                    if !(1..=3).contains(&group.len()) {
                        return Err(LeanCompileError::unsupported(
                            "FunctionDefinition/Arguments",
                        ));
                    }
                    let values = group
                        .iter()
                        .map(|x| self.compile_normalization_value(x, position))
                        .collect::<Result<Vec<_>, _>>()?;
                    let input = if values.len() == 1 {
                        values[0].clone()
                    } else {
                        format!(
                            "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                            values.join(", ")
                        )
                    };
                    equality = format!("(congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f {input}) {equality})");
                }
                return Ok(Some((continued.clone(), equality)));
            }
        }
        match current {
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(value)) => {
                if let Some((argument, equality)) = self.embed_recorded_function_expansion(
                    &value.arg,
                    application,
                    replacement,
                    continued,
                    beta,
                    position,
                )? {
                    let mut rebuilt = value.clone();
                    rebuilt.arg = Box::new(argument);
                    return Ok(Some((
                        Obj::ExpLogOperator(ExpLogOperator::Sqrt(rebuilt)),
                        format!("(congrArg (Litex.sqrtValue (M := M)) {equality})"),
                    )));
                }
                Ok(None)
            }
            Obj::ArithmeticOperator(_) | Obj::IntegerOperator(_) => {
                let (operation, _) = normalization_operation_children(current)?;
                let operation = arithmetic_operation_term(operation);
                let mut rebuilt = current.clone();
                let children = normalization_operation_children_mut(&mut rebuilt)?;
                let count = children.len();
                for (index, child) in children.into_iter().enumerate() {
                    if let Some((next, equality)) = self.embed_recorded_function_expansion(
                        child,
                        application,
                        replacement,
                        continued,
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
                        return Ok(Some((rebuilt, proof)));
                    }
                }
                Ok(None)
            }
            Obj::FnObj(call) if call.body.len() == 1 && (1..=3).contains(&call.body[0].len()) => {
                let function = self.compile_normalization_value(
                    &function_head_object(call.head.as_ref())?,
                    position,
                )?;
                let values = call.body[0]
                    .iter()
                    .map(|argument| self.compile_normalization_value(argument, position))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut rebuilt = call.clone();
                let count = rebuilt.body[0].len();
                for (index, child) in rebuilt.body[0].iter_mut().enumerate() {
                    if let Some((next, equality)) = self.embed_recorded_function_expansion(
                        child,
                        application,
                        replacement,
                        continued,
                        beta,
                        position,
                    )? {
                        **child = next;
                        let proof = if count == 1 {
                            format!("(congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) {function} _x) {equality})")
                        } else {
                            let mut context_values = values.clone();
                            context_values[index] = "_x".into();
                            format!("(congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) {function} (Litex.FiniteFunction.tupleValue (M := M) ![{}])) {equality})", context_values.join(", "))
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

fn normalization_operation_children(
    object: &Obj,
) -> Result<(&'static str, Vec<&Obj>), LeanCompileError> {
    match object {
        Obj::ArithmeticOperator(p) => normalization_arithmetic_children(p),
        Obj::IntegerOperator(IntegerOperator::Factorial(p)) => Ok(("factorialValue", vec![&p.arg])),
        Obj::IntegerOperator(IntegerOperator::Gcd(p)) => Ok(("gcdValue", vec![&p.left, &p.right])),
        Obj::IntegerOperator(IntegerOperator::Lcm(p)) => Ok(("lcmValue", vec![&p.left, &p.right])),
        Obj::IntegerOperator(IntegerOperator::Mod(p)) => Ok(("modValue", vec![&p.left, &p.right])),
        Obj::IntegerOperator(IntegerOperator::Quot(p)) => {
            Ok(("quotValue", vec![&p.left, &p.right]))
        }
        _ => Err(LeanCompileError::unsupported(
            "FunctionDefinition/Operation",
        )),
    }
}

fn normalization_operation_children_mut(
    object: &mut Obj,
) -> Result<Vec<&mut Box<Obj>>, LeanCompileError> {
    match object {
        Obj::ArithmeticOperator(p) => normalization_arithmetic_children_mut(p),
        Obj::IntegerOperator(IntegerOperator::Factorial(p)) => Ok(vec![&mut p.arg]),
        Obj::IntegerOperator(IntegerOperator::Gcd(p)) => Ok(vec![&mut p.left, &mut p.right]),
        Obj::IntegerOperator(IntegerOperator::Lcm(p)) => Ok(vec![&mut p.left, &mut p.right]),
        Obj::IntegerOperator(IntegerOperator::Mod(p)) => Ok(vec![&mut p.left, &mut p.right]),
        Obj::IntegerOperator(IntegerOperator::Quot(p)) => Ok(vec![&mut p.left, &mut p.right]),
        _ => Err(LeanCompileError::unsupported(
            "FunctionDefinition/Operation",
        )),
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
        ArithmeticOperator::Sign(value) => Ok(("signValue", vec![&value.arg])),
        ArithmeticOperator::Floor(value) => Ok(("floorValue", vec![&value.arg])),
        ArithmeticOperator::Ceil(value) => Ok(("ceilValue", vec![&value.arg])),
        ArithmeticOperator::Min(value) => Ok(("minValue", vec![&value.left, &value.right])),
        ArithmeticOperator::Max(value) => Ok(("maxValue", vec![&value.left, &value.right])),
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
        ArithmeticOperator::Sign(value) => Ok(vec![&mut value.arg]),
        ArithmeticOperator::Floor(value) => Ok(vec![&mut value.arg]),
        ArithmeticOperator::Ceil(value) => Ok(vec![&mut value.arg]),
        ArithmeticOperator::Min(value) => Ok(vec![&mut value.left, &mut value.right]),
        ArithmeticOperator::Max(value) => Ok(vec![&mut value.left, &mut value.right]),
    }
}
