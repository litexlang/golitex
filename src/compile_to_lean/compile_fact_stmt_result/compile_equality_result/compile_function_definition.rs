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

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_definition(
        &self,
        fact: &EqualFact,
        proof: &EqualitySearchProofByObjectDefinition,
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
                    EqualitySearchProofByFnApplicationObjectDefinition::HaveFnByInduc(_) => Err(
                        LeanCompileError::unsupported("FunctionDefinition/Induction"),
                    ),
                    EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(_) => {
                        Err(LeanCompileError::unsupported(
                            "FunctionDefinition/ParentCheckedBeta",
                        ))
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
        let domains = self.compile_function_domains(&function.body)?;
        let guard = self.compile_function_guard_template(&function.body, &completed)?;
        let body = self.compile_function_body_template(function, &completed)?;
        let expanded = self.compile_normalization_value(&proof.expanded_body, &completed)?;
        let names = format!("let _litex_original := {actual}\nlet _litex_literal := {selected}");
        if arguments.len() == 1 {
            let return_proof = format!("(by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain {} {guard} _x).mpr ⟨_hx, _hg⟩))", domains.join(" "));
            Ok(format!("(by\n  {}\n  have _litex_call_eq := Litex.callCongr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.argument)\n  have _litex_beta := Litex.callFormula_denote {} {guard} {body} {return_proof} _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2\n  exact _litex_call_eq.trans (_litex_beta.trans (show {body} (Litex.denote _litex_literal.val.argument) = {expanded} from rfl))\n)", names.replace('\n', "\n  "), domains.join(" ")))
        } else {
            let return_proof = format!("(by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FunctionSemantics.pairValue (M := M) _x _y) ((Litex.FunctionSignature.two_domain {} {guard} _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ({body} (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).1 (Litex.FunctionSemantics.unpairValue (M := M) (Litex.FunctionSemantics.pairValue (M := M) _x _y)).2) (M.standard {}) at _h; simpa only [Litex.FunctionSemantics.unpair_pair] using _h)", domains.join(" "), domains.last().expect("checked numeric return"));
            Ok(format!("(by\n  {}\n  have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal {head_equal} (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)\n  have _litex_beta := Litex.callFormula2_denote {} {guard} {body} {return_proof} _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2\n  exact _litex_call_eq.trans (_litex_beta.trans (show {body} (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = {expanded} from rfl))\n)", names.replace('\n', "\n  "), domains.join(" ")))
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
                Ok(format!("(M.{operation} {})", values.join(" ")))
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
                            format!("(congrArg M.{operation} {equality})")
                        } else if index == 0 {
                            format!("(congrArg₂ M.{operation} {equality} rfl)")
                        } else {
                            format!("(congrArg₂ M.{operation} rfl {equality})")
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
        _ => Err(LeanCompileError::unsupported(
            "FunctionDefinition/ArithmeticContext",
        )),
    }
}
