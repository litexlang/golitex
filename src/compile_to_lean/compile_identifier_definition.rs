//! Replay the selected identifier-definition edge and its original residual.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_identifier::EqualitySearchProofByIdentifierObjectDefinition;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_identifier_definition(
        &self,
        fact: &EqualFact,
        proof: &EqualitySearchProofByIdentifierObjectDefinition,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (expanded, residual, typed) = match proof {
            EqualitySearchProofByIdentifierObjectDefinition::LetObj(p) => {
                (&p.expanded_rhs, &p.residual_equal, false)
            }
            EqualitySearchProofByIdentifierObjectDefinition::HaveObjEqual(p) => {
                (&p.expanded_rhs, &p.residual_equal, true)
            }
        };
        let residual_subject = source_subject(residual)?;
        let Fact::AtomicFact(AtomicFact::EqualFact(child)) = &residual_subject else {
            return Err(LeanCompileError::unsupported(
                "IdentifierDefinition/ResidualFamily",
            ));
        };
        if child.left.ir() != expanded.ir() {
            return Err(LeanCompileError::unsupported(
                "IdentifierDefinition/ResidualBody",
            ));
        }
        let (identifier, reversed) =
            if child.right.ir() == fact.right.ir() && child.right.ir() != fact.left.ir() {
                (&fact.left, false)
            } else if child.right.ir() == fact.left.ir() && child.right.ir() != fact.right.ir() {
                (&fact.right, true)
            } else {
                return Err(LeanCompileError::unsupported(
                    "IdentifierDefinition/ResidualEndpoint",
                ));
            };
        if !matches!(identifier, Obj::Identifier(_)) {
            return Err(LeanCompileError::unsupported(
                "IdentifierDefinition/Subject",
            ));
        }
        let edge = position
            .with_visible_alias(
                identifier,
                &self.runtime,
                &mut |bound, value, wd, producer| {
                    ensure_object(value, success_object_wd(wd, value)?)?;
                    if value.ir() != expanded.ir() {
                        return Err(LeanCompileError::unsupported(
                            "IdentifierDefinition/ExpandedSubject",
                        ));
                    }
                    let (id, published) = match producer.owner {
                        SourceOwner::Statement(ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::LetObj(
                                ExecLetObjStmtResult::Success(p),
                            )),
                        )) if !typed && p.stored_fact_ids.len() == 1 => (p.stored_fact_ids[0], 1),
                        SourceOwner::Statement(ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::DefineObj(
                                ExecDefineObjStmtResult::HaveObjEqual(
                                    ExecHaveObjEqualStmtResult::Success(p),
                                ),
                            ),
                        )) if typed => {
                            let parameters = p
                                .statement
                                .param_def
                                .groups
                                .iter()
                                .flat_map(|group| &group.params)
                                .collect::<Vec<_>>();
                            let index = parameters
                                .iter()
                                .position(|parameter| *parameter == bound)
                                .ok_or_else(|| {
                                    LeanCompileError::unsupported("IdentifierDefinition/Binding")
                                })?;
                            let count = parameters.len();
                            if p.store_and_infer_result.store_and_infer_results.len() != 2 * count {
                                return Err(LeanCompileError::unsupported(
                                    "IdentifierDefinition/Stores",
                                ));
                            }
                            (
                                p.store_and_infer_result.store_and_infer_results[count + index]
                                    .primary_fact_id(),
                                2 * count + index + 1,
                            )
                        }
                        _ => {
                            return Err(LeanCompileError::unsupported(
                                "IdentifierDefinition/ProducerFamily",
                            ))
                        }
                    };
                    let completed = SourcePosition {
                        before: published,
                        ..*producer
                    };
                    // The selected definition rule authorizes this exact declaration
                    // equality; it does not make unrelated foreign FactIds visible.
                    let (original, _) = completed.visible_fact(id, &self.runtime)?;
                    alias_equality_subject(original, bound, value, &completed, &self.runtime)?;
                    position.declaration_reference(&format!("h_{}", id.value()), producer)
                },
            )?
            .ok_or_else(|| LeanCompileError::unsupported("IdentifierDefinition/Producer"))?;
        let checked = self.compile_verify(residual, position)?;
        let composed = format!("(({edge}).trans ({}))", checked.1);
        Ok(if reversed {
            format!("({composed}).symm")
        } else {
            composed
        })
    }
}
