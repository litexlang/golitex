//! Access and recursive traversal for successful statement results.

use crate::prelude::*;
use std::fmt;

impl fmt::Debug for SuccessStmtResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Self::Fact(result) = self {
            return f.debug_tuple("Fact").field(result).finish();
        }
        f.debug_struct("SuccessStmtResult")
            .field("statement", &self.statement())
            .field("common", &self.common())
            .finish()
    }
}

impl SuccessStmtResult {
    /// Visits the immediate successful composition children retained by this
    /// statement result. During the statement-family migration, legacy
    /// families still expose their ordered children through `common`; migrated
    /// families expose named recursive fields here.
    pub fn visit_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        if let Self::ProofBlock(proof_block) = self {
            proof_block.visit_named_child_results(visitor);
        }
        if let Self::Definition(definition) = self {
            definition.visit_named_child_results(visitor);
        }
        if let Self::Witness(witness) = self {
            witness.visit_named_child_results(visitor);
        }
        if let Self::By(by) = self {
            by.visit_named_child_results(visitor);
        }
        if let Self::ReleaseThmStmt(result) = self {
            result.visit_named_child_results(visitor);
        }
    }

    pub fn try_visit_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        if let Self::ProofBlock(proof_block) = self {
            proof_block.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::Definition(definition) = self {
            definition.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::Witness(witness) = self {
            witness.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::By(by) = self {
            by.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::ReleaseThmStmt(result) = self {
            result.try_visit_named_child_results_mut(visitor)?;
        }
        Ok(())
    }

    pub fn visit_success_child_results(&self, visitor: &mut impl FnMut(&SuccessStmtResult)) {
        if let Self::Definition(SuccessDefinitionStmtResult::DefTemplateStmt(result)) = self {
            visitor(&result.body_statement_result);
        }
    }

    pub fn try_visit_success_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut SuccessStmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        if let Self::Definition(SuccessDefinitionStmtResult::DefTemplateStmt(result)) = self {
            visitor(&mut result.body_statement_result)?;
        }
        Ok(())
    }

    pub fn statement(&self) -> Stmt {
        match self {
            Self::Fact(statement) => statement.fact().into(),
            Self::UnsafeStmt(statement) => statement.statement(),
            Self::Definition(statement) => statement.statement(),
            Self::ReleaseThmStmt(statement) => statement.statement.clone().into(),
            Self::By(statement) => statement.statement(),
            Self::Witness(statement) => statement.statement(),
            Self::ProofBlock(statement) => statement.statement(),
            Self::Command(statement) => statement.statement(),
        }
    }

    pub fn fact(&self) -> Option<&SuccessFactStmtResult> {
        match self {
            Self::Fact(statement) => Some(statement),
            _ => None,
        }
    }

    pub fn fact_mut(&mut self) -> Option<&mut SuccessFactStmtResult> {
        match self {
            Self::Fact(statement) => Some(statement),
            _ => None,
        }
    }

    pub fn common(&self) -> Option<&SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common()),
            Self::Definition(statement) => statement.common(),
            Self::ReleaseThmStmt(statement) => Some(&statement.common),
            Self::By(statement) => Some(statement.common()),
            Self::Witness(statement) => Some(statement.common()),
            Self::ProofBlock(statement) => Some(statement.common()),
            Self::Command(statement) => Some(statement.common()),
        }
    }

    pub fn common_mut(&mut self) -> Option<&mut SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common_mut()),
            Self::Definition(statement) => statement.common_mut(),
            Self::ReleaseThmStmt(statement) => Some(&mut statement.common),
            Self::By(statement) => Some(statement.common_mut()),
            Self::Witness(statement) => Some(statement.common_mut()),
            Self::ProofBlock(statement) => Some(statement.common_mut()),
            Self::Command(statement) => Some(statement.common_mut()),
        }
    }

    pub fn into_common(self) -> Option<SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.into_common()),
            Self::Definition(statement) => statement.into_common(),
            Self::ReleaseThmStmt(statement) => Some(statement.common),
            Self::By(statement) => Some(statement.into_common()),
            Self::Witness(statement) => Some(statement.into_common()),
            Self::ProofBlock(statement) => Some(statement.into_common()),
            Self::Command(statement) => Some(statement.into_common()),
        }
    }

    pub fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::Fact(_) => Vec::new(),
            Self::ProofBlock(proof_block) => proof_block.into_child_results(),
            Self::Definition(definition) => definition.into_child_results(),
            Self::Witness(witness) => witness.into_child_results(),
            Self::By(by) => by.into_child_results(),
            Self::ReleaseThmStmt(result) => result.into_child_results(),
            _other => Vec::new(),
        }
    }
}

impl SuccessReleaseThmStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        if let Some(verification) = &self.verification {
            match &verification.source {
                SuccessVerifyTheoremApplicationSourceResult::Litex(source) => {
                    if let Some(arguments) = &source.argument_verification {
                        for check in &arguments.checks {
                            visitor(check);
                        }
                    }
                    for check in &source.domain_checks {
                        visitor(check);
                    }
                }
                SuccessVerifyTheoremApplicationSourceResult::Builtin(source) => {
                    for check in &source.requirement_checks {
                        visitor(check);
                    }
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        if let Some(verification) = &mut self.verification {
            match &mut verification.source {
                SuccessVerifyTheoremApplicationSourceResult::Litex(source) => {
                    if let Some(arguments) = &mut source.argument_verification {
                        for check in &mut arguments.checks {
                            visitor(check)?;
                        }
                    }
                    for check in &mut source.domain_checks {
                        visitor(check)?;
                    }
                }
                SuccessVerifyTheoremApplicationSourceResult::Builtin(source) => {
                    for check in &mut source.requirement_checks {
                        visitor(check)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        let mut children = Vec::new();
        if let Some(verification) = self.verification {
            match verification.source {
                SuccessVerifyTheoremApplicationSourceResult::Litex(source) => {
                    if let Some(arguments) = source.argument_verification {
                        children.extend(arguments.checks);
                    }
                    children.extend(source.domain_checks);
                }
                SuccessVerifyTheoremApplicationSourceResult::Builtin(source) => {
                    children.extend(source.requirement_checks);
                }
            }
        }
        children
    }
}

impl SuccessByStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::ByCasesStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.coverage_check);
                    for branch in &verification.branches {
                        for step in &branch.proof_steps {
                            visitor(step);
                        }
                        match &branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                for check in &result.checks {
                                    visitor(check);
                                }
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                visitor(&result.contradiction.impossible_check);
                                visitor(&result.contradiction.negated_impossible_check);
                            }
                        }
                    }
                }
            }
            Self::ByContraStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    visitor(&verification.contradiction.impossible_check);
                    visitor(&verification.contradiction.negated_impossible_check);
                }
            }
            Self::ByEnumerateFiniteSetStmt(result) => {
                if let Some(verification) = &result.verification {
                    for assignment in &verification.assignments {
                        visit_assignment_children(assignment, visitor);
                    }
                }
            }
            Self::ByFiniteSetInducStmt(result) => {
                visit_induc_children(result.verification.as_ref(), visitor)
            }
            Self::ByInducStmt(result) => {
                visit_induc_children(result.verification.as_ref(), visitor)
            }
            Self::ByForStmt(result) => {
                if let Some(verification) = &result.verification {
                    for assignment in verification.assignments() {
                        visit_assignment_children(assignment, visitor);
                    }
                }
            }
            Self::ByEnumerateRangeStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.membership_check);
                    for check in &verification.endpoint_checks {
                        visitor(&check.verification);
                    }
                }
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.membership_check);
                    for check in &verification.endpoint_checks {
                        visitor(&check.verification);
                    }
                }
            }
            Self::ByExtensionStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    visitor(&verification.left_to_right_check);
                    visitor(&verification.right_to_left_check);
                }
            }
            Self::ByTransitivePropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::BySymmetricPropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::ByReflexivePropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::ByAntisymmetricPropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::ByZornLemmaStmt(result) => {
                visit_choice_children(result.verification.as_ref(), visitor)
            }
            Self::ByAxiomOfChoiceStmt(result) => {
                visit_choice_children(result.verification.as_ref(), visitor)
            }
            Self::ByRegularityAxiomStmt(result) => {
                visit_choice_children(result.verification.as_ref(), visitor)
            }
            Self::ByDefStmt(result) => {
                if let Some(verification) = &result.verification {
                    if let Some(arguments) = &verification.argument_verification {
                        for check in &arguments.checks {
                            visitor(check);
                        }
                    }
                    for check in &verification.clause_checks {
                        visitor(check);
                    }
                }
            }
            Self::ByStructDefStmt(result) => {
                if let Some(check) = &result.membership_check {
                    visitor(check);
                }
            }
            Self::ByThmStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.temporary_application);
                    visitor(&verification.selected_fact_check);
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::ByCasesStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.coverage_check)?;
                    for branch in &mut verification.branches {
                        for step in &mut branch.proof_steps {
                            visitor(step)?;
                        }
                        match &mut branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                for check in &mut result.checks {
                                    visitor(check)?;
                                }
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                visitor(&mut result.contradiction.impossible_check)?;
                                visitor(&mut result.contradiction.negated_impossible_check)?;
                            }
                        }
                    }
                }
            }
            Self::ByContraStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    visitor(&mut verification.contradiction.impossible_check)?;
                    visitor(&mut verification.contradiction.negated_impossible_check)?;
                }
            }
            Self::ByEnumerateFiniteSetStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for assignment in &mut verification.assignments {
                        try_visit_assignment_children_mut(assignment, visitor)?;
                    }
                }
            }
            Self::ByFiniteSetInducStmt(result) => {
                try_visit_induc_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByInducStmt(result) => {
                try_visit_induc_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByForStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for assignment in verification.assignments_mut() {
                        try_visit_assignment_children_mut(assignment, visitor)?;
                    }
                }
            }
            Self::ByEnumerateRangeStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.membership_check)?;
                    for check in &mut verification.endpoint_checks {
                        visitor(&mut check.verification)?;
                    }
                }
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.membership_check)?;
                    for check in &mut verification.endpoint_checks {
                        visitor(&mut check.verification)?;
                    }
                }
            }
            Self::ByExtensionStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    visitor(&mut verification.left_to_right_check)?;
                    visitor(&mut verification.right_to_left_check)?;
                }
            }
            Self::ByTransitivePropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::BySymmetricPropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByReflexivePropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByAntisymmetricPropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByZornLemmaStmt(result) => {
                try_visit_choice_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByAxiomOfChoiceStmt(result) => {
                try_visit_choice_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByRegularityAxiomStmt(result) => {
                try_visit_choice_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByDefStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    if let Some(arguments) = &mut verification.argument_verification {
                        for check in &mut arguments.checks {
                            visitor(check)?;
                        }
                    }
                    for check in &mut verification.clause_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::ByStructDefStmt(result) => {
                if let Some(check) = &mut result.membership_check {
                    visitor(check)?;
                }
            }
            Self::ByThmStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.temporary_application)?;
                    visitor(&mut verification.selected_fact_check)?;
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::ByCasesStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.coverage_check);
                    for branch in verification.branches {
                        children.extend(branch.proof_steps);
                        match branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                children.extend(result.checks);
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                children.push(*result.contradiction.impossible_check);
                                children.push(*result.contradiction.negated_impossible_check);
                            }
                        }
                    }
                }
                children
            }
            Self::ByContraStmt(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.push(*verification.contradiction.impossible_check);
                    children.push(*verification.contradiction.negated_impossible_check);
                    children
                })
                .unwrap_or_default(),
            Self::ByEnumerateFiniteSetStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    for assignment in verification.assignments {
                        children.extend(into_assignment_children(assignment));
                    }
                }
                children
            }
            Self::ByFiniteSetInducStmt(result) => {
                into_induc_children(result.common, result.verification)
            }
            Self::ByInducStmt(result) => into_induc_children(result.common, result.verification),
            Self::ByForStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    for assignment in verification.into_assignments() {
                        children.extend(into_assignment_children(assignment));
                    }
                }
                children
            }
            Self::ByEnumerateRangeStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.membership_check);
                    children.extend(
                        verification
                            .endpoint_checks
                            .into_iter()
                            .map(|check| *check.verification),
                    );
                }
                children
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.membership_check);
                    children.extend(
                        verification
                            .endpoint_checks
                            .into_iter()
                            .map(|check| *check.verification),
                    );
                }
                children
            }
            Self::ByExtensionStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(verification.proof_steps);
                    children.push(*verification.left_to_right_check);
                    children.push(*verification.right_to_left_check);
                }
                children
            }
            Self::ByTransitivePropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::BySymmetricPropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::ByReflexivePropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::ByAntisymmetricPropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::ByZornLemmaStmt(result) => {
                into_choice_children(result.common, result.verification)
            }
            Self::ByAxiomOfChoiceStmt(result) => {
                into_choice_children(result.common, result.verification)
            }
            Self::ByRegularityAxiomStmt(result) => {
                into_choice_children(result.common, result.verification)
            }
            Self::ByDefStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    if let Some(arguments) = verification.argument_verification {
                        children.extend(arguments.checks);
                    }
                    children.extend(verification.clause_checks);
                }
                children
            }
            Self::ByStructDefStmt(result) => result
                .membership_check
                .into_iter()
                .map(|check| *check)
                .collect(),
            Self::ByThmStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.temporary_application);
                    children.push(*verification.selected_fact_check);
                }
                children
            }
        }
    }
}

fn visit_assignment_children(
    assignment: &SuccessVerifyByAssignmentResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for domain in &assignment.domain_checks {
        visitor(&domain.check);
        if let Some(check) = &domain.negated_check {
            visitor(check);
        }
    }
    for step in &assignment.proof_steps {
        visitor(step);
    }
    for check in &assignment.conclusion_checks {
        visitor(check);
    }
}

fn try_visit_assignment_children_mut<E>(
    assignment: &mut SuccessVerifyByAssignmentResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for domain in &mut assignment.domain_checks {
        visitor(&mut domain.check)?;
        if let Some(check) = &mut domain.negated_check {
            visitor(check)?;
        }
    }
    for step in &mut assignment.proof_steps {
        visitor(step)?;
    }
    for check in &mut assignment.conclusion_checks {
        visitor(check)?;
    }
    Ok(())
}

fn into_assignment_children(assignment: SuccessVerifyByAssignmentResult) -> Vec<StmtResult> {
    let mut children = Vec::new();
    for domain in assignment.domain_checks {
        children.push(*domain.check);
        if let Some(check) = domain.negated_check {
            children.push(*check);
        }
    }
    children.extend(assignment.proof_steps);
    children.extend(assignment.conclusion_checks);
    children
}

fn visit_prop_registration_children(
    verification: Option<&SuccessVerifyByPropRegistrationResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        for step in &verification.proof_steps {
            visitor(step);
        }
        visitor(&verification.forall_check);
    }
}

fn try_visit_prop_registration_children_mut<E>(
    verification: Option<&mut SuccessVerifyByPropRegistrationResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for step in &mut verification.proof_steps {
            visitor(step)?;
        }
        visitor(&mut verification.forall_check)?;
    }
    Ok(())
}

fn into_prop_registration_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByPropRegistrationResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.extend(verification.proof_steps);
        children.push(*verification.forall_check);
    }
    children
}

fn visit_choice_children(
    verification: Option<&SuccessVerifyByChoiceResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        for step in &verification.proof_steps {
            visitor(step);
        }
        for obligation in &verification.obligations {
            if let Some(check) = &obligation.check {
                visitor(check);
            }
        }
    }
}

fn try_visit_choice_children_mut<E>(
    verification: Option<&mut SuccessVerifyByChoiceResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for step in &mut verification.proof_steps {
            visitor(step)?;
        }
        for obligation in &mut verification.obligations {
            if let Some(check) = &mut obligation.check {
                visitor(check)?;
            }
        }
    }
    Ok(())
}

fn into_choice_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByChoiceResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.extend(verification.proof_steps);
        children.extend(
            verification
                .obligations
                .into_iter()
                .filter_map(|obligation| obligation.check.map(|check| *check)),
        );
    }
    children
}

fn visit_induc_children(
    verification: Option<&SuccessVerifyByInducResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    let Some(verification) = verification else {
        return;
    };
    match &verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            for step in &proof.proof_steps {
                visitor(step);
            }
            for goal in &proof.goals {
                visitor(&goal.base_check);
                visitor(&goal.start_in_z_check);
                visitor(&goal.step_check);
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            visitor(&proof.start_in_z_check);
            visit_structured_integer_induc_case_children(&proof.base, visitor);
            visit_structured_integer_induc_case_children(&proof.step, visitor);
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            visit_induc_case_children(&proof.base, visitor);
            visit_induc_case_children(&proof.step, visitor);
        }
    }
}

fn visit_structured_integer_induc_case_children(
    result: &SuccessVerifyByStructuredIntegerInducCaseResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for step in &result.proof_steps {
        visitor(step);
    }
    for conclusion in &result.conclusions {
        visitor(&conclusion.check);
    }
}

fn visit_induc_case_children(
    result: &SuccessVerifyByInducCaseResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for step in &result.proof_steps {
        visitor(step);
    }
    for conclusion in &result.conclusions {
        visitor(&conclusion.check);
    }
}

fn try_visit_induc_children_mut<E>(
    verification: Option<&mut SuccessVerifyByInducResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    let Some(verification) = verification else {
        return Ok(());
    };
    match &mut verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            for step in &mut proof.proof_steps {
                visitor(step)?;
            }
            for goal in &mut proof.goals {
                visitor(&mut goal.base_check)?;
                visitor(&mut goal.start_in_z_check)?;
                visitor(&mut goal.step_check)?;
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            visitor(&mut proof.start_in_z_check)?;
            try_visit_structured_integer_induc_case_children_mut(&mut proof.base, visitor)?;
            try_visit_structured_integer_induc_case_children_mut(&mut proof.step, visitor)?;
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            try_visit_induc_case_children_mut(&mut proof.base, visitor)?;
            try_visit_induc_case_children_mut(&mut proof.step, visitor)?;
        }
    }
    Ok(())
}

fn try_visit_structured_integer_induc_case_children_mut<E>(
    result: &mut SuccessVerifyByStructuredIntegerInducCaseResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for step in &mut result.proof_steps {
        visitor(step)?;
    }
    for conclusion in &mut result.conclusions {
        visitor(&mut conclusion.check)?;
    }
    Ok(())
}

fn try_visit_induc_case_children_mut<E>(
    result: &mut SuccessVerifyByInducCaseResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for step in &mut result.proof_steps {
        visitor(step)?;
    }
    for conclusion in &mut result.conclusions {
        visitor(&mut conclusion.check)?;
    }
    Ok(())
}

fn into_induc_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByInducResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    let Some(verification) = verification else {
        return children;
    };
    match verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            children.extend(proof.proof_steps);
            for goal in proof.goals {
                children.push(*goal.base_check);
                children.push(*goal.start_in_z_check);
                children.push(*goal.step_check);
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            children.push(*proof.start_in_z_check);
            children.extend(into_structured_integer_induc_case_children(proof.base));
            children.extend(into_structured_integer_induc_case_children(proof.step));
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            children.extend(into_induc_case_children(proof.base));
            children.extend(into_induc_case_children(proof.step));
        }
    }
    children
}

fn into_structured_integer_induc_case_children(
    result: SuccessVerifyByStructuredIntegerInducCaseResult,
) -> Vec<StmtResult> {
    let mut children = result.proof_steps;
    children.extend(
        result
            .conclusions
            .into_iter()
            .map(|conclusion| *conclusion.check),
    );
    children
}

fn into_induc_case_children(result: SuccessVerifyByInducCaseResult) -> Vec<StmtResult> {
    let mut children = result.proof_steps;
    children.extend(
        result
            .conclusions
            .into_iter()
            .map(|conclusion| *conclusion.check),
    );
    children
}

impl SuccessWitnessStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::WitnessExistFact(result) => {
                if let Some(verification) = &result.verification {
                    visit_witness_exist_children(verification, visitor);
                }
            }
            Self::WitnessAtomicFact(result) => {
                if let Some(verification) = &result.verification {
                    for check in &verification.definition_parameter_verification.checks {
                        visitor(check);
                    }
                    visit_witness_exist_children(&verification.witness_verification, visitor);
                }
            }
            Self::WitnessNonemptySet(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    visitor(&verification.nonempty_check);
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::WitnessExistFact(result) => {
                if let Some(verification) = &mut result.verification {
                    try_visit_witness_exist_children_mut(verification, visitor)?;
                }
            }
            Self::WitnessAtomicFact(result) => {
                if let Some(verification) = &mut result.verification {
                    for check in &mut verification.definition_parameter_verification.checks {
                        visitor(check)?;
                    }
                    try_visit_witness_exist_children_mut(
                        &mut verification.witness_verification,
                        visitor,
                    )?;
                }
            }
            Self::WitnessNonemptySet(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    visitor(&mut verification.nonempty_check)?;
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::WitnessExistFact(result) => result
                .verification
                .map(into_witness_exist_children)
                .unwrap_or_default(),
            Self::WitnessAtomicFact(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.definition_parameter_verification.checks;
                    children.extend(into_witness_exist_children(
                        verification.witness_verification,
                    ));
                    children
                })
                .unwrap_or_default(),
            Self::WitnessNonemptySet(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.push(*verification.nonempty_check);
                    children
                })
                .unwrap_or_default(),
        }
    }
}

fn visit_witness_exist_children(
    verification: &SuccessVerifyWitnessExistResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for check in verification.parameter_checks.iter().flatten() {
        visitor(check);
    }
    for step in &verification.proof_steps {
        visitor(step);
    }
    for check in &verification.body_checks {
        visitor(check);
    }
    if let Some(check) = &verification.uniqueness_check {
        visitor(check);
    }
}

fn try_visit_witness_exist_children_mut<E>(
    verification: &mut SuccessVerifyWitnessExistResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for check in verification.parameter_checks.iter_mut().flatten() {
        visitor(check)?;
    }
    for step in &mut verification.proof_steps {
        visitor(step)?;
    }
    for check in &mut verification.body_checks {
        visitor(check)?;
    }
    if let Some(check) = &mut verification.uniqueness_check {
        visitor(check)?;
    }
    Ok(())
}

fn into_witness_exist_children(verification: SuccessVerifyWitnessExistResult) -> Vec<StmtResult> {
    let mut children = verification
        .parameter_checks
        .into_iter()
        .flatten()
        .map(|check| *check)
        .collect::<Vec<_>>();
    children.extend(verification.proof_steps);
    children.extend(verification.body_checks);
    if let Some(check) = verification.uniqueness_check {
        children.push(*check);
    }
    children
}

impl SuccessProofBlockStmtResult {
    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::ClaimStmt(result) => claim_child_results(result.verification),
            Self::ExampleStmt(result) => claim_child_results(result.verification),
            Self::SketchStmt(result) => result
                .proof
                .map(|proof| proof.proof_steps)
                .unwrap_or_default(),
            Self::TryStmt(result) => result
                .proof
                .map(|proof| proof.proof_steps)
                .unwrap_or_default(),
        }
    }

    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::ClaimStmt(result) => {
                if let Some(verification) = &result.verification {
                    verification.visit_child_results(visitor);
                }
            }
            Self::ExampleStmt(result) => {
                if let Some(verification) = &result.verification {
                    verification.visit_child_results(visitor);
                }
            }
            Self::SketchStmt(result) => {
                if let Some(proof) = &result.proof {
                    for step in &proof.proof_steps {
                        visitor(step);
                    }
                }
            }
            Self::TryStmt(result) => {
                if let Some(proof) = &result.proof {
                    for step in &proof.proof_steps {
                        visitor(step);
                    }
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::ClaimStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    verification.try_visit_child_results_mut(visitor)?;
                }
            }
            Self::ExampleStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    verification.try_visit_child_results_mut(visitor)?;
                }
            }
            Self::SketchStmt(result) => {
                if let Some(proof) = &mut result.proof {
                    for step in &mut proof.proof_steps {
                        visitor(step)?;
                    }
                }
            }
            Self::TryStmt(result) => {
                if let Some(proof) = &mut result.proof {
                    for step in &mut proof.proof_steps {
                        visitor(step)?;
                    }
                }
            }
        }
        Ok(())
    }
}

fn claim_child_results(verification: Option<SuccessVerifyClaimResult>) -> Vec<StmtResult> {
    match verification {
        Some(SuccessVerifyClaimResult::Forall(result)) => {
            let mut children = result.proof_steps;
            children.extend(result.conclusion_checks);
            children
        }
        Some(SuccessVerifyClaimResult::Fact(result)) => {
            let mut children = result.proof_steps;
            children.push(*result.conclusion_check);
            children
        }
        None => Vec::new(),
    }
}

impl SuccessVerifyClaimResult {
    fn visit_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::Forall(result) => {
                for step in &result.proof_steps {
                    visitor(step);
                }
                for check in &result.conclusion_checks {
                    visitor(check);
                }
            }
            Self::Fact(result) => {
                for step in &result.proof_steps {
                    visitor(step);
                }
                visitor(&result.conclusion_check);
            }
        }
    }

    fn try_visit_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::Forall(result) => {
                for step in &mut result.proof_steps {
                    visitor(step)?;
                }
                for check in &mut result.conclusion_checks {
                    visitor(check)?;
                }
            }
            Self::Fact(result) => {
                for step in &mut result.proof_steps {
                    visitor(step)?;
                }
                visitor(&mut result.conclusion_check)?;
            }
        }
        Ok(())
    }
}

impl SuccessDefinitionStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::ObtainObjFromExistFact(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::ObtainObjFromAtomicFact(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::ObtainObjFromThm(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                if let Some(verification) = &result.verification {
                    for group in &verification.groups {
                        if let Some(check) = &group.nonempty_check {
                            visitor(check);
                        }
                    }
                }
            }
            Self::HaveObjEqualStmt(result) => {
                if let Some(verification) = &result.verification {
                    for check in &verification.type_checks {
                        visitor(check);
                    }
                }
            }
            Self::HaveByPreimageStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_membership_check);
                }
            }
            Self::HaveFnEqualStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.return_check);
                }
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.coverage_check);
                    for check in &verification.return_checks {
                        visitor(check);
                    }
                }
            }
            Self::HaveFnByInducStmt(result) => {
                if let Some(verification) = &result.verification {
                    visit_have_fn_by_induc_children(verification, visitor);
                }
            }
            Self::HaveFnByForallExistUniqueStmt(result) => {
                if let Some(verification) = &result.verification {
                    if let Some(check) = &verification.source_forall_check {
                        visitor(check);
                    }
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor(check);
                    }
                }
            }
            Self::HaveTupleStmt(result) => {
                visit_tuple_or_cart_children(result.verification.as_ref(), visitor)
            }
            Self::HaveCartStmt(result) => {
                visit_tuple_or_cart_children(result.verification.as_ref(), visitor)
            }
            Self::HaveSeqStmt(result) => {
                visit_indexed_function_children(result.verification.as_ref(), visitor)
            }
            Self::HaveFiniteSeqStmt(result) => {
                visit_indexed_function_children(result.verification.as_ref(), visitor)
            }
            Self::HaveMatrixStmt(result) => {
                visit_indexed_function_children(result.verification.as_ref(), visitor)
            }
            Self::DefThmStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor(check);
                    }
                }
            }
            Self::DefStrategyStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor(check);
                    }
                }
            }
            Self::DefAlgoStmt(result) => {
                if let Some(verification) = &result.run_in_local_env {
                    for case in &verification.cases {
                        visitor(&case.verification);
                    }
                    if let Some(default_return) = &verification.default_return {
                        visitor(&default_return.verification);
                    }
                    if let Some(coverage) = &verification.coverage {
                        visitor(&coverage.verification);
                    }
                }
            }
            _ => {}
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromExistFact(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromAtomicFact(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromThm(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for group in &mut verification.groups {
                        if let Some(check) = &mut group.nonempty_check {
                            visitor(check)?;
                        }
                    }
                }
            }
            Self::HaveObjEqualStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for check in &mut verification.type_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::HaveByPreimageStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_membership_check)?;
                }
            }
            Self::HaveFnEqualStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.return_check)?;
                }
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.coverage_check)?;
                    for check in &mut verification.return_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::HaveFnByInducStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    try_visit_have_fn_by_induc_children_mut(verification, visitor)?;
                }
            }
            Self::HaveFnByForallExistUniqueStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    if let Some(check) = &mut verification.source_forall_check {
                        visitor(check)?;
                    }
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::HaveTupleStmt(result) => {
                try_visit_tuple_or_cart_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveCartStmt(result) => {
                try_visit_tuple_or_cart_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveSeqStmt(result) => {
                try_visit_indexed_function_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveFiniteSeqStmt(result) => {
                try_visit_indexed_function_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveMatrixStmt(result) => {
                try_visit_indexed_function_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::DefThmStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::DefStrategyStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::DefAlgoStmt(result) => {
                if let Some(verification) = &mut result.run_in_local_env {
                    for case in &mut verification.cases {
                        visitor(&mut case.verification)?;
                    }
                    if let Some(default_return) = &mut verification.default_return {
                        visitor(&mut default_return.verification)?;
                    }
                    if let Some(coverage) = &mut verification.coverage {
                        visitor(&mut coverage.verification)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::HaveObjByExistFactsStmt(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::ObtainObjFromExistFact(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::ObtainObjFromAtomicFact(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::ObtainObjFromThm(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::HaveObjInNonemptySetStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(
                        verification
                            .groups
                            .into_iter()
                            .filter_map(|group| group.nonempty_check.map(|check| *check)),
                    );
                }
                children
            }
            Self::HaveObjEqualStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(verification.type_checks);
                }
                children
            }
            Self::HaveByPreimageStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.source_membership_check);
                }
                children
            }
            Self::HaveFnEqualStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.return_check);
                }
                children
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.coverage_check);
                    children.extend(verification.return_checks);
                }
                children
            }
            Self::HaveFnByInducStmt(result) => result
                .verification
                .map(into_have_fn_by_induc_children)
                .unwrap_or_default(),
            Self::HaveFnByForallExistUniqueStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    if let Some(check) = verification.source_forall_check {
                        children.push(*check);
                    }
                    children.extend(verification.proof_steps);
                    children.extend(verification.conclusion_checks);
                }
                children
            }
            Self::HaveTupleStmt(result) => {
                into_tuple_or_cart_children(result.common, result.verification)
            }
            Self::HaveCartStmt(result) => {
                into_tuple_or_cart_children(result.common, result.verification)
            }
            Self::HaveSeqStmt(result) => {
                into_indexed_function_children(result.common, result.verification)
            }
            Self::HaveFiniteSeqStmt(result) => {
                into_indexed_function_children(result.common, result.verification)
            }
            Self::HaveMatrixStmt(result) => {
                into_indexed_function_children(result.common, result.verification)
            }
            Self::DefTemplateStmt(result) => vec![(*result.body_statement_result).into()],
            Self::DefThmStmt(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.extend(verification.conclusion_checks);
                    children
                })
                .unwrap_or_default(),
            Self::DefStrategyStmt(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.extend(verification.conclusion_checks);
                    children
                })
                .unwrap_or_default(),
            Self::DefAlgoStmt(result) => result
                .run_in_local_env
                .map(|verification| {
                    let mut children = verification
                        .cases
                        .into_iter()
                        .map(|case| *case.verification)
                        .collect::<Vec<_>>();
                    if let Some(default_return) = verification.default_return {
                        children.push(*default_return.verification);
                    }
                    if let Some(coverage) = verification.coverage {
                        children.push(*coverage.verification);
                    }
                    children
                })
                .unwrap_or_default(),
            _other => Vec::new(),
        }
    }
}

fn visit_have_fn_by_induc_children(
    verification: &SuccessVerifyHaveFnByInducResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    visitor(
        &verification
            .verification_run_in_local_env
            .measure
            .measure_integer_check,
    );
    visitor(
        &verification
            .verification_run_in_local_env
            .measure
            .lower_bound_integer_check,
    );
    visitor(
        &verification
            .verification_run_in_local_env
            .measure
            .lower_bound_check,
    );
    visit_have_fn_by_induc_case_list_children(
        &verification.verification_run_in_local_env.cases,
        visitor,
    );
}

fn visit_have_fn_by_induc_case_list_children(
    cases: &SuccessVerifyHaveFnByInducCaseListResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    visitor(&cases.coverage_check);
    for disjointness in &cases.mutual_exclusions {
        visitor(&disjointness.negated_atom_check);
    }
    for case in &cases.cases {
        match &case.body {
            SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                visitor(&body.return_membership_check)
            }
            SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                visit_have_fn_by_induc_case_list_children(nested, visitor)
            }
        }
    }
}

fn try_visit_have_fn_by_induc_children_mut<E>(
    verification: &mut SuccessVerifyHaveFnByInducResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    visitor(
        &mut verification
            .verification_run_in_local_env
            .measure
            .measure_integer_check,
    )?;
    visitor(
        &mut verification
            .verification_run_in_local_env
            .measure
            .lower_bound_integer_check,
    )?;
    visitor(
        &mut verification
            .verification_run_in_local_env
            .measure
            .lower_bound_check,
    )?;
    try_visit_have_fn_by_induc_case_list_children_mut(
        &mut verification.verification_run_in_local_env.cases,
        visitor,
    )
}

fn try_visit_have_fn_by_induc_case_list_children_mut<E>(
    cases: &mut SuccessVerifyHaveFnByInducCaseListResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    visitor(&mut cases.coverage_check)?;
    for disjointness in &mut cases.mutual_exclusions {
        visitor(&mut disjointness.negated_atom_check)?;
    }
    for case in &mut cases.cases {
        match &mut case.body {
            SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                visitor(&mut body.return_membership_check)?
            }
            SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                try_visit_have_fn_by_induc_case_list_children_mut(nested, visitor)?
            }
        }
    }
    Ok(())
}

fn into_have_fn_by_induc_children(
    verification: SuccessVerifyHaveFnByInducResult,
) -> Vec<StmtResult> {
    let local = verification.verification_run_in_local_env;
    let mut children = vec![
        *local.measure.measure_integer_check,
        *local.measure.lower_bound_integer_check,
        *local.measure.lower_bound_check,
    ];
    into_have_fn_by_induc_case_list_children(local.cases, &mut children);
    children
}

fn into_have_fn_by_induc_case_list_children(
    cases: SuccessVerifyHaveFnByInducCaseListResult,
    children: &mut Vec<StmtResult>,
) {
    children.push(*cases.coverage_check);
    children.extend(
        cases
            .mutual_exclusions
            .into_iter()
            .map(|proof| *proof.negated_atom_check),
    );
    for case in cases.cases {
        match case.body {
            SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                children.push(*body.return_membership_check)
            }
            SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                into_have_fn_by_induc_case_list_children(*nested, children)
            }
        }
    }
}

fn visit_tuple_or_cart_children(
    verification: Option<&SuccessVerifyTupleOrCartDefinitionResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        visitor(&verification.dimension.positive_check);
        visitor(&verification.dimension.at_least_two_check);
    }
}

fn try_visit_tuple_or_cart_children_mut<E>(
    verification: Option<&mut SuccessVerifyTupleOrCartDefinitionResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        visitor(&mut verification.dimension.positive_check)?;
        visitor(&mut verification.dimension.at_least_two_check)?;
    }
    Ok(())
}

fn into_tuple_or_cart_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyTupleOrCartDefinitionResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.push(*verification.dimension.positive_check);
        children.push(*verification.dimension.at_least_two_check);
    }
    children
}

fn visit_indexed_function_children(
    verification: Option<&SuccessVerifyIndexedFunctionDefinitionResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        for check in &verification.bound_checks {
            visitor(check);
        }
        visitor(&verification.return_check);
    }
}

fn try_visit_indexed_function_children_mut<E>(
    verification: Option<&mut SuccessVerifyIndexedFunctionDefinitionResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for check in &mut verification.bound_checks {
            visitor(check)?;
        }
        visitor(&mut verification.return_check)?;
    }
    Ok(())
}

fn into_indexed_function_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.extend(verification.bound_checks);
        children.push(*verification.return_check);
    }
    children
}

impl SuccessUnsafeStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::TrustStmt(result) => result.common,
            Self::TrustHaveStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::TrustStmt(result) => result.statement.clone().into(),
            Self::TrustHaveStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::TrustStmt(result) => &result.common,
            Self::TrustHaveStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::TrustStmt(result) => &mut result.common,
            Self::TrustHaveStmt(result) => &mut result.common,
        }
    }
}

impl SuccessDefinitionStmtResult {
    fn into_common(self) -> Option<SuccessStmtCommonResult> {
        match self {
            Self::LetObjStmt(result) => Some(result.common),
            Self::HaveObjInNonemptySetStmt(result) => Some(result.common),
            Self::HaveObjEqualStmt(result) => Some(result.common),
            Self::HaveObjByExistFactsStmt(result) => Some(result.common),
            Self::ObtainObjFromExistFact(result) => Some(result.common),
            Self::ObtainObjFromAtomicFact(result) => Some(result.common),
            Self::ObtainObjFromThm(result) => Some(result.common),
            Self::HaveByPreimageStmt(result) => Some(result.common),
            Self::HaveFnEqualStmt(result) => Some(result.common),
            Self::HaveFnEqualCaseByCaseStmt(result) => Some(result.common),
            Self::HaveFnByInducStmt(result) => Some(result.common),
            Self::HaveFnByForallExistUniqueStmt(result) => Some(result.common),
            Self::HaveTupleStmt(result) => Some(result.common),
            Self::HaveCartStmt(result) => Some(result.common),
            Self::HaveSeqStmt(result) => Some(result.common),
            Self::HaveFiniteSeqStmt(result) => Some(result.common),
            Self::HaveMatrixStmt(result) => Some(result.common),
            Self::DefPropStmt(result) => Some(result.common),
            Self::DefAbstractPropStmt(result) => Some(result.common),
            Self::DefSettingStmt(result) => Some(result.common),
            Self::DefTemplateStmt(_) => None,
            Self::DefStructStmt(result) => Some(result.common),
            Self::DefAlgoStmt(result) => Some(result.common),
            Self::DefThmStmt(result) => Some(result.common),
            Self::AxiomStmt(result) => Some(result.common),
            Self::DefStrategyStmt(result) => Some(result.common),
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::LetObjStmt(result) => result.statement.clone().into(),
            Self::HaveObjInNonemptySetStmt(result) => result.statement.clone().into(),
            Self::HaveObjEqualStmt(result) => result.statement.clone().into(),
            Self::HaveObjByExistFactsStmt(result) => result.statement.clone().into(),
            Self::ObtainObjFromExistFact(result) => result.statement.clone().into(),
            Self::ObtainObjFromAtomicFact(result) => result.statement.clone().into(),
            Self::ObtainObjFromThm(result) => result.statement.clone().into(),
            Self::HaveByPreimageStmt(result) => result.statement.clone().into(),
            Self::HaveFnEqualStmt(result) => result.statement.clone().into(),
            Self::HaveFnEqualCaseByCaseStmt(result) => result.statement.clone().into(),
            Self::HaveFnByInducStmt(result) => result.statement.clone().into(),
            Self::HaveFnByForallExistUniqueStmt(result) => result.statement.clone().into(),
            Self::HaveTupleStmt(result) => result.statement.clone().into(),
            Self::HaveCartStmt(result) => result.statement.clone().into(),
            Self::HaveSeqStmt(result) => result.statement.clone().into(),
            Self::HaveFiniteSeqStmt(result) => result.statement.clone().into(),
            Self::HaveMatrixStmt(result) => result.statement.clone().into(),
            Self::DefPropStmt(result) => result.statement.clone().into(),
            Self::DefAbstractPropStmt(result) => result.statement.clone().into(),
            Self::DefSettingStmt(result) => result.statement.clone().into(),
            Self::DefTemplateStmt(result) => result.statement.clone().into(),
            Self::DefStructStmt(result) => result.statement.clone().into(),
            Self::DefAlgoStmt(result) => result.statement.clone().into(),
            Self::DefThmStmt(result) => result.statement.clone().into(),
            Self::AxiomStmt(result) => result.statement.clone().into(),
            Self::DefStrategyStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> Option<&SuccessStmtCommonResult> {
        match self {
            Self::LetObjStmt(result) => Some(&result.common),
            Self::HaveObjInNonemptySetStmt(result) => Some(&result.common),
            Self::HaveObjEqualStmt(result) => Some(&result.common),
            Self::HaveObjByExistFactsStmt(result) => Some(&result.common),
            Self::ObtainObjFromExistFact(result) => Some(&result.common),
            Self::ObtainObjFromAtomicFact(result) => Some(&result.common),
            Self::ObtainObjFromThm(result) => Some(&result.common),
            Self::HaveByPreimageStmt(result) => Some(&result.common),
            Self::HaveFnEqualStmt(result) => Some(&result.common),
            Self::HaveFnEqualCaseByCaseStmt(result) => Some(&result.common),
            Self::HaveFnByInducStmt(result) => Some(&result.common),
            Self::HaveFnByForallExistUniqueStmt(result) => Some(&result.common),
            Self::HaveTupleStmt(result) => Some(&result.common),
            Self::HaveCartStmt(result) => Some(&result.common),
            Self::HaveSeqStmt(result) => Some(&result.common),
            Self::HaveFiniteSeqStmt(result) => Some(&result.common),
            Self::HaveMatrixStmt(result) => Some(&result.common),
            Self::DefPropStmt(result) => Some(&result.common),
            Self::DefAbstractPropStmt(result) => Some(&result.common),
            Self::DefSettingStmt(result) => Some(&result.common),
            Self::DefTemplateStmt(_) => None,
            Self::DefStructStmt(result) => Some(&result.common),
            Self::DefAlgoStmt(result) => Some(&result.common),
            Self::DefThmStmt(result) => Some(&result.common),
            Self::AxiomStmt(result) => Some(&result.common),
            Self::DefStrategyStmt(result) => Some(&result.common),
        }
    }

    fn common_mut(&mut self) -> Option<&mut SuccessStmtCommonResult> {
        match self {
            Self::LetObjStmt(result) => Some(&mut result.common),
            Self::HaveObjInNonemptySetStmt(result) => Some(&mut result.common),
            Self::HaveObjEqualStmt(result) => Some(&mut result.common),
            Self::HaveObjByExistFactsStmt(result) => Some(&mut result.common),
            Self::ObtainObjFromExistFact(result) => Some(&mut result.common),
            Self::ObtainObjFromAtomicFact(result) => Some(&mut result.common),
            Self::ObtainObjFromThm(result) => Some(&mut result.common),
            Self::HaveByPreimageStmt(result) => Some(&mut result.common),
            Self::HaveFnEqualStmt(result) => Some(&mut result.common),
            Self::HaveFnEqualCaseByCaseStmt(result) => Some(&mut result.common),
            Self::HaveFnByInducStmt(result) => Some(&mut result.common),
            Self::HaveFnByForallExistUniqueStmt(result) => Some(&mut result.common),
            Self::HaveTupleStmt(result) => Some(&mut result.common),
            Self::HaveCartStmt(result) => Some(&mut result.common),
            Self::HaveSeqStmt(result) => Some(&mut result.common),
            Self::HaveFiniteSeqStmt(result) => Some(&mut result.common),
            Self::HaveMatrixStmt(result) => Some(&mut result.common),
            Self::DefPropStmt(result) => Some(&mut result.common),
            Self::DefAbstractPropStmt(result) => Some(&mut result.common),
            Self::DefSettingStmt(result) => Some(&mut result.common),
            Self::DefTemplateStmt(_) => None,
            Self::DefStructStmt(result) => Some(&mut result.common),
            Self::DefAlgoStmt(result) => Some(&mut result.common),
            Self::DefThmStmt(result) => Some(&mut result.common),
            Self::AxiomStmt(result) => Some(&mut result.common),
            Self::DefStrategyStmt(result) => Some(&mut result.common),
        }
    }
}

impl SuccessByStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::ByCasesStmt(result) => result.common,
            Self::ByContraStmt(result) => result.common,
            Self::ByEnumerateFiniteSetStmt(result) => result.common,
            Self::ByFiniteSetInducStmt(result) => result.common,
            Self::ByInducStmt(result) => result.common,
            Self::ByForStmt(result) => result.common,
            Self::ByExtensionStmt(result) => result.common,
            Self::ByEnumerateRangeStmt(result) => result.common,
            Self::ByClosedRangeAsCasesStmt(result) => result.common,
            Self::ByTransitivePropStmt(result) => result.common,
            Self::BySymmetricPropStmt(result) => result.common,
            Self::ByReflexivePropStmt(result) => result.common,
            Self::ByAntisymmetricPropStmt(result) => result.common,
            Self::ByZornLemmaStmt(result) => result.common,
            Self::ByAxiomOfChoiceStmt(result) => result.common,
            Self::ByRegularityAxiomStmt(result) => result.common,
            Self::ByDefStmt(result) => result.common,
            Self::ByStructDefStmt(result) => result.common,
            Self::ByThmStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ByCasesStmt(result) => result.statement.clone().into(),
            Self::ByContraStmt(result) => result.statement.clone().into(),
            Self::ByEnumerateFiniteSetStmt(result) => result.statement.clone().into(),
            Self::ByFiniteSetInducStmt(result) => result.statement.clone().into(),
            Self::ByInducStmt(result) => result.statement.clone().into(),
            Self::ByForStmt(result) => result.statement.clone().into(),
            Self::ByExtensionStmt(result) => result.statement.clone().into(),
            Self::ByEnumerateRangeStmt(result) => result.statement.clone().into(),
            Self::ByClosedRangeAsCasesStmt(result) => result.statement.clone().into(),
            Self::ByTransitivePropStmt(result) => result.statement.clone().into(),
            Self::BySymmetricPropStmt(result) => result.statement.clone().into(),
            Self::ByReflexivePropStmt(result) => result.statement.clone().into(),
            Self::ByAntisymmetricPropStmt(result) => result.statement.clone().into(),
            Self::ByZornLemmaStmt(result) => result.statement.clone().into(),
            Self::ByAxiomOfChoiceStmt(result) => result.statement.clone().into(),
            Self::ByRegularityAxiomStmt(result) => result.statement.clone().into(),
            Self::ByDefStmt(result) => result.statement.clone().into(),
            Self::ByStructDefStmt(result) => result.statement.clone().into(),
            Self::ByThmStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::ByCasesStmt(result) => &result.common,
            Self::ByContraStmt(result) => &result.common,
            Self::ByEnumerateFiniteSetStmt(result) => &result.common,
            Self::ByFiniteSetInducStmt(result) => &result.common,
            Self::ByInducStmt(result) => &result.common,
            Self::ByForStmt(result) => &result.common,
            Self::ByExtensionStmt(result) => &result.common,
            Self::ByEnumerateRangeStmt(result) => &result.common,
            Self::ByClosedRangeAsCasesStmt(result) => &result.common,
            Self::ByTransitivePropStmt(result) => &result.common,
            Self::BySymmetricPropStmt(result) => &result.common,
            Self::ByReflexivePropStmt(result) => &result.common,
            Self::ByAntisymmetricPropStmt(result) => &result.common,
            Self::ByZornLemmaStmt(result) => &result.common,
            Self::ByAxiomOfChoiceStmt(result) => &result.common,
            Self::ByRegularityAxiomStmt(result) => &result.common,
            Self::ByDefStmt(result) => &result.common,
            Self::ByStructDefStmt(result) => &result.common,
            Self::ByThmStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::ByCasesStmt(result) => &mut result.common,
            Self::ByContraStmt(result) => &mut result.common,
            Self::ByEnumerateFiniteSetStmt(result) => &mut result.common,
            Self::ByFiniteSetInducStmt(result) => &mut result.common,
            Self::ByInducStmt(result) => &mut result.common,
            Self::ByForStmt(result) => &mut result.common,
            Self::ByExtensionStmt(result) => &mut result.common,
            Self::ByEnumerateRangeStmt(result) => &mut result.common,
            Self::ByClosedRangeAsCasesStmt(result) => &mut result.common,
            Self::ByTransitivePropStmt(result) => &mut result.common,
            Self::BySymmetricPropStmt(result) => &mut result.common,
            Self::ByReflexivePropStmt(result) => &mut result.common,
            Self::ByAntisymmetricPropStmt(result) => &mut result.common,
            Self::ByZornLemmaStmt(result) => &mut result.common,
            Self::ByAxiomOfChoiceStmt(result) => &mut result.common,
            Self::ByRegularityAxiomStmt(result) => &mut result.common,
            Self::ByDefStmt(result) => &mut result.common,
            Self::ByStructDefStmt(result) => &mut result.common,
            Self::ByThmStmt(result) => &mut result.common,
        }
    }
}

impl SuccessWitnessStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::WitnessExistFact(result) => result.common,
            Self::WitnessAtomicFact(result) => result.common,
            Self::WitnessNonemptySet(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::WitnessExistFact(result) => result.statement.clone().into(),
            Self::WitnessAtomicFact(result) => result.statement.clone().into(),
            Self::WitnessNonemptySet(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::WitnessExistFact(result) => &result.common,
            Self::WitnessAtomicFact(result) => &result.common,
            Self::WitnessNonemptySet(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::WitnessExistFact(result) => &mut result.common,
            Self::WitnessAtomicFact(result) => &mut result.common,
            Self::WitnessNonemptySet(result) => &mut result.common,
        }
    }
}

impl SuccessProofBlockStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::ClaimStmt(result) => result.common,
            Self::ExampleStmt(result) => result.common,
            Self::SketchStmt(result) => result.common,
            Self::TryStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ClaimStmt(result) => result.statement.clone().into(),
            Self::ExampleStmt(result) => result.statement.clone().into(),
            Self::SketchStmt(result) => result.statement.clone().into(),
            Self::TryStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::ClaimStmt(result) => &result.common,
            Self::ExampleStmt(result) => &result.common,
            Self::SketchStmt(result) => &result.common,
            Self::TryStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::ClaimStmt(result) => &mut result.common,
            Self::ExampleStmt(result) => &mut result.common,
            Self::SketchStmt(result) => &mut result.common,
            Self::TryStmt(result) => &mut result.common,
        }
    }
}

impl SuccessCommandStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::EvalStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::EvalStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::EvalStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::EvalStmt(result) => &mut result.common,
        }
    }
}
