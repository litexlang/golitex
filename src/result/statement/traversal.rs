//! Access and recursive traversal for successful statement results.

use crate::prelude::*;
use std::fmt;

trait ResultTraversalChild {
    fn visit_with(&self, visitor: &mut ResultChildVisitor<'_>);
}

impl ResultTraversalChild for StmtResult {
    fn visit_with(&self, visitor: &mut ResultChildVisitor<'_>) {
        (visitor.statement)(self);
    }
}

impl ResultTraversalChild for VerifyFactResult {
    fn visit_with(&self, visitor: &mut ResultChildVisitor<'_>) {
        (visitor.verification)(self);
    }
}

impl ResultTraversalChild for ExistentialEliminationSourceResult {
    fn visit_with(&self, visitor: &mut ResultChildVisitor<'_>) {
        match self {
            Self::Fact(result) => visitor.visit(result),
            Self::TheoremApplication(result) => visitor.visit(result),
        }
    }
}

impl<T: ResultTraversalChild + ?Sized> ResultTraversalChild for Box<T> {
    fn visit_with(&self, visitor: &mut ResultChildVisitor<'_>) {
        self.as_ref().visit_with(visitor);
    }
}

struct ResultChildVisitor<'a> {
    statement: &'a mut dyn FnMut(&StmtResult),
    verification: &'a mut dyn FnMut(&VerifyFactResult),
}

impl ResultChildVisitor<'_> {
    fn visit<T: ResultTraversalChild + ?Sized>(&mut self, child: &T) {
        child.visit_with(self);
    }
}

trait ResultTraversalChildMut {
    fn try_visit_with<E>(&mut self, visitor: &mut ResultChildMutVisitor<'_, E>) -> Result<(), E>;
}

impl ResultTraversalChildMut for StmtResult {
    fn try_visit_with<E>(&mut self, visitor: &mut ResultChildMutVisitor<'_, E>) -> Result<(), E> {
        (visitor.statement)(self)
    }
}

impl ResultTraversalChildMut for VerifyFactResult {
    fn try_visit_with<E>(&mut self, visitor: &mut ResultChildMutVisitor<'_, E>) -> Result<(), E> {
        (visitor.verification)(self)
    }
}

impl ResultTraversalChildMut for ExistentialEliminationSourceResult {
    fn try_visit_with<E>(&mut self, visitor: &mut ResultChildMutVisitor<'_, E>) -> Result<(), E> {
        match self {
            Self::Fact(result) => visitor.visit(result),
            Self::TheoremApplication(result) => visitor.visit(result),
        }
    }
}

impl<T: ResultTraversalChildMut + ?Sized> ResultTraversalChildMut for Box<T> {
    fn try_visit_with<E>(&mut self, visitor: &mut ResultChildMutVisitor<'_, E>) -> Result<(), E> {
        self.as_mut().try_visit_with(visitor)
    }
}

struct ResultChildMutVisitor<'a, E> {
    statement: &'a mut dyn FnMut(&mut StmtResult) -> Result<(), E>,
    verification: &'a mut dyn FnMut(&mut VerifyFactResult) -> Result<(), E>,
}

impl<E> ResultChildMutVisitor<'_, E> {
    fn visit<T: ResultTraversalChildMut + ?Sized>(&mut self, child: &mut T) -> Result<(), E> {
        child.try_visit_with(self)
    }
}

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
        let mut ignore_verification = |_: &VerifyFactResult| {};
        let mut visitor = ResultChildVisitor {
            statement: visitor,
            verification: &mut ignore_verification,
        };
        if let Self::ProofBlock(proof_block) = self {
            proof_block.visit_named_child_results(&mut visitor);
        }
        if let Self::Definition(definition) = self {
            definition.visit_named_child_results(&mut visitor);
        }
        if let Self::Witness(witness) = self {
            witness.visit_named_child_results(&mut visitor);
        }
        if let Self::By(by) = self {
            by.visit_named_child_results(&mut visitor);
        }
        if let Self::ReleaseThmStmt(result) = self {
            result.visit_named_child_results(&mut visitor);
        }
        if let Self::ReleaseStructDefStmt(result) = self {
            result.visit_named_child_results(&mut visitor);
        }
    }

    /// Visits verifier-generated fact-process children without treating them
    /// as executed statements.
    pub fn visit_fact_verification_children(&self, visitor: &mut impl FnMut(&VerifyFactResult)) {
        let mut ignore_statement = |_: &StmtResult| {};
        let mut visitor = ResultChildVisitor {
            statement: &mut ignore_statement,
            verification: visitor,
        };
        if let Self::ProofBlock(proof_block) = self {
            proof_block.visit_named_child_results(&mut visitor);
        }
        if let Self::Definition(definition) = self {
            definition.visit_named_child_results(&mut visitor);
        }
        if let Self::Witness(witness) = self {
            witness.visit_named_child_results(&mut visitor);
        }
        if let Self::By(by) = self {
            by.visit_named_child_results(&mut visitor);
        }
        if let Self::ReleaseThmStmt(result) = self {
            result.visit_named_child_results(&mut visitor);
        }
        if let Self::ReleaseStructDefStmt(result) = self {
            result.visit_named_child_results(&mut visitor);
        }
    }

    pub fn try_visit_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut ignore_verification = |_: &mut VerifyFactResult| Ok(());
        let mut visitor = ResultChildMutVisitor {
            statement: visitor,
            verification: &mut ignore_verification,
        };
        if let Self::ProofBlock(proof_block) = self {
            proof_block.try_visit_named_child_results_mut(&mut visitor)?;
        }
        if let Self::Definition(definition) = self {
            definition.try_visit_named_child_results_mut(&mut visitor)?;
        }
        if let Self::Witness(witness) = self {
            witness.try_visit_named_child_results_mut(&mut visitor)?;
        }
        if let Self::By(by) = self {
            by.try_visit_named_child_results_mut(&mut visitor)?;
        }
        if let Self::ReleaseThmStmt(result) = self {
            result.try_visit_named_child_results_mut(&mut visitor)?;
        }
        if let Self::ReleaseStructDefStmt(result) = self {
            result.try_visit_named_child_results_mut(&mut visitor)?;
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
            Self::ReleaseStructDefStmt(statement) => statement.statement.clone().into(),
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
            Self::ReleaseStructDefStmt(statement) => Some(&statement.common),
            Self::By(statement) => Some(statement.common()),
            Self::Witness(statement) => Some(statement.common()),
            Self::ProofBlock(statement) => statement.common(),
            Self::Command(statement) => Some(statement.common()),
        }
    }

    /// Environment mutations produced by this statement, independent of the
    /// concrete Result layout used by that statement kind.
    pub fn environment_effects(&self) -> Option<&SuccessInferResult> {
        match self {
            Self::Fact(statement) => Some(&statement.infers),
            Self::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(statement)) => {
                Some(&statement.environment_effects)
            }
            _ => self.common().map(|common| &common.infers),
        }
    }

    pub fn common_mut(&mut self) -> Option<&mut SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common_mut()),
            Self::Definition(statement) => statement.common_mut(),
            Self::ReleaseThmStmt(statement) => Some(&mut statement.common),
            Self::ReleaseStructDefStmt(statement) => Some(&mut statement.common),
            Self::By(statement) => Some(statement.common_mut()),
            Self::Witness(statement) => Some(statement.common_mut()),
            Self::ProofBlock(statement) => statement.common_mut(),
            Self::Command(statement) => Some(statement.common_mut()),
        }
    }

    pub fn into_common(self) -> Option<SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.into_common()),
            Self::Definition(statement) => statement.into_common(),
            Self::ReleaseThmStmt(statement) => Some(statement.common),
            Self::ReleaseStructDefStmt(statement) => Some(statement.common),
            Self::By(statement) => Some(statement.into_common()),
            Self::Witness(statement) => Some(statement.into_common()),
            Self::ProofBlock(statement) => statement.into_common(),
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
            Self::ReleaseStructDefStmt(result) => result.into_child_results(),
            _other => Vec::new(),
        }
    }
}

impl SuccessReleaseThmStmtResult {
    fn visit_named_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        if let Some(verification) = &self.verification {
            match &verification.source {
                SuccessVerifyTheoremApplicationSourceResult::Litex(source) => {
                    if let SuccessVerifyLitexTheoremApplicationMode::ForallInstantiation {
                        argument_verification,
                        domain_checks,
                        ..
                    } = &source.mode
                    {
                        if let Some(arguments) = argument_verification {
                            for check in &arguments.checks {
                                visitor.visit(check);
                            }
                        }
                        for check in domain_checks {
                            visitor.visit(check);
                        }
                    }
                }
                SuccessVerifyTheoremApplicationSourceResult::Builtin(source) => {
                    for check in &source.requirement_checks {
                        visitor.visit(check);
                    }
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
    ) -> Result<(), E> {
        if let Some(verification) = &mut self.verification {
            match &mut verification.source {
                SuccessVerifyTheoremApplicationSourceResult::Litex(source) => {
                    if let SuccessVerifyLitexTheoremApplicationMode::ForallInstantiation {
                        argument_verification,
                        domain_checks,
                        ..
                    } = &mut source.mode
                    {
                        if let Some(arguments) = argument_verification {
                            for check in &mut arguments.checks {
                                visitor.visit(check)?;
                            }
                        }
                        for check in domain_checks {
                            visitor.visit(check)?;
                        }
                    }
                }
                SuccessVerifyTheoremApplicationSourceResult::Builtin(source) => {
                    for check in &mut source.requirement_checks {
                        visitor.visit(check)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        Vec::new()
    }
}

impl SuccessReleaseStructDefStmtResult {
    fn visit_named_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        if let Some(check) = &self.membership_check {
            visitor.visit(check);
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
    ) -> Result<(), E> {
        if let Some(check) = &mut self.membership_check {
            visitor.visit(check)?;
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        Vec::new()
    }
}


impl SuccessByStmtResult {
    fn visit_named_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        match self {
            Self::ByCasesStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.coverage_check);
                    for branch in &verification.branches {
                        for step in &branch.proof_steps {
                            visitor.visit(step);
                        }
                        match &branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                for check in &result.checks {
                                    visitor.visit(check);
                                }
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                visitor.visit(&result.contradiction.impossible_check);
                                visitor.visit(&result.contradiction.negated_impossible_check);
                            }
                        }
                    }
                }
            }
            Self::ByContraStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor.visit(step);
                    }
                    visitor.visit(&verification.contradiction.impossible_check);
                    visitor.visit(&verification.contradiction.negated_impossible_check);
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
                    visitor.visit(&verification.membership_check);
                    for check in &verification.endpoint_checks {
                        visitor.visit(&check.verification);
                    }
                }
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.membership_check);
                    for check in &verification.endpoint_checks {
                        visitor.visit(&check.verification);
                    }
                }
            }
            Self::ByExtensionStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor.visit(step);
                    }
                    visitor.visit(&verification.left_to_right_check);
                    visitor.visit(&verification.right_to_left_check);
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
                            visitor.visit(check);
                        }
                    }
                    for check in &verification.clause_checks {
                        visitor.visit(check);
                    }
                }
            }
            Self::ByThmStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.temporary_application);
                    visitor.visit(&verification.selected_fact_check);
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
    ) -> Result<(), E> {
        match self {
            Self::ByCasesStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.coverage_check)?;
                    for branch in &mut verification.branches {
                        for step in &mut branch.proof_steps {
                            visitor.visit(step)?;
                        }
                        match &mut branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                for check in &mut result.checks {
                                    visitor.visit(check)?;
                                }
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                visitor.visit(&mut result.contradiction.impossible_check)?;
                                visitor
                                    .visit(&mut result.contradiction.negated_impossible_check)?;
                            }
                        }
                    }
                }
            }
            Self::ByContraStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor.visit(step)?;
                    }
                    visitor.visit(&mut verification.contradiction.impossible_check)?;
                    visitor.visit(&mut verification.contradiction.negated_impossible_check)?;
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
                    visitor.visit(&mut verification.membership_check)?;
                    for check in &mut verification.endpoint_checks {
                        visitor.visit(&mut check.verification)?;
                    }
                }
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.membership_check)?;
                    for check in &mut verification.endpoint_checks {
                        visitor.visit(&mut check.verification)?;
                    }
                }
            }
            Self::ByExtensionStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor.visit(step)?;
                    }
                    visitor.visit(&mut verification.left_to_right_check)?;
                    visitor.visit(&mut verification.right_to_left_check)?;
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
                            visitor.visit(check)?;
                        }
                    }
                    for check in &mut verification.clause_checks {
                        visitor.visit(check)?;
                    }
                }
            }
            Self::ByThmStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.temporary_application)?;
                    visitor.visit(&mut verification.selected_fact_check)?;
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::ByCasesStmt(result) => {
                let mut children: Vec<StmtResult> = Vec::new();
                if let Some(verification) = result.verification {
                    for branch in verification.branches {
                        children.extend(branch.proof_steps);
                    }
                }
                children
            }
            Self::ByContraStmt(result) => result
                .verification
                .map(|verification| verification.proof_steps)
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
                let _ = result;
                Vec::new()
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::ByExtensionStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(verification.proof_steps);
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
                let _ = result;
                Vec::new()
            }
            Self::ByThmStmt(result) => {
                let _ = result;
                Vec::new()
            }
        }
    }
}

fn visit_assignment_children(
    assignment: &SuccessVerifyByAssignmentResult,
    visitor: &mut ResultChildVisitor<'_>,
) {
    for domain in &assignment.domain_checks {
        visitor.visit(&domain.check);
        if let Some(check) = &domain.negated_check {
            visitor.visit(check);
        }
    }
    for step in &assignment.proof_steps {
        visitor.visit(step);
    }
    for check in &assignment.conclusion_checks {
        visitor.visit(check);
    }
}

fn try_visit_assignment_children_mut<E>(
    assignment: &mut SuccessVerifyByAssignmentResult,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    for domain in &mut assignment.domain_checks {
        visitor.visit(&mut domain.check)?;
        if let Some(check) = &mut domain.negated_check {
            visitor.visit(check)?;
        }
    }
    for step in &mut assignment.proof_steps {
        visitor.visit(step)?;
    }
    for check in &mut assignment.conclusion_checks {
        visitor.visit(check)?;
    }
    Ok(())
}

fn into_assignment_children(assignment: SuccessVerifyByAssignmentResult) -> Vec<StmtResult> {
    assignment.proof_steps
}

fn visit_prop_registration_children(
    verification: Option<&SuccessVerifyByPropRegistrationResult>,
    visitor: &mut ResultChildVisitor<'_>,
) {
    if let Some(verification) = verification {
        for step in &verification.proof_steps {
            visitor.visit(step);
        }
        visitor.visit(&verification.forall_check);
    }
}

fn try_visit_prop_registration_children_mut<E>(
    verification: Option<&mut SuccessVerifyByPropRegistrationResult>,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for step in &mut verification.proof_steps {
            visitor.visit(step)?;
        }
        visitor.visit(&mut verification.forall_check)?;
    }
    Ok(())
}

fn into_prop_registration_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByPropRegistrationResult>,
) -> Vec<StmtResult> {
    verification
        .map(|verification| verification.proof_steps)
        .unwrap_or_default()
}

fn visit_choice_children(
    verification: Option<&SuccessVerifyByChoiceResult>,
    visitor: &mut ResultChildVisitor<'_>,
) {
    if let Some(verification) = verification {
        for step in &verification.proof_steps {
            visitor.visit(step);
        }
        for obligation in &verification.obligations {
            if let Some(check) = &obligation.check {
                visitor.visit(check);
            }
        }
    }
}

fn try_visit_choice_children_mut<E>(
    verification: Option<&mut SuccessVerifyByChoiceResult>,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for step in &mut verification.proof_steps {
            visitor.visit(step)?;
        }
        for obligation in &mut verification.obligations {
            if let Some(check) = &mut obligation.check {
                visitor.visit(check)?;
            }
        }
    }
    Ok(())
}

fn into_choice_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByChoiceResult>,
) -> Vec<StmtResult> {
    verification
        .map(|verification| verification.proof_steps)
        .unwrap_or_default()
}

fn visit_induc_children(
    verification: Option<&SuccessVerifyByInducResult>,
    visitor: &mut ResultChildVisitor<'_>,
) {
    let Some(verification) = verification else {
        return;
    };
    match &verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            for step in &proof.proof_steps {
                visitor.visit(step);
            }
            for goal in &proof.goals {
                visitor.visit(&goal.base_check);
                visitor.visit(&goal.start_in_z_check);
                visitor.visit(&goal.step_check);
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            visitor.visit(&proof.start_in_z_check);
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
    visitor: &mut ResultChildVisitor<'_>,
) {
    for step in &result.proof_steps {
        visitor.visit(step);
    }
    for conclusion in &result.conclusions {
        visitor.visit(&conclusion.check);
    }
}

fn visit_induc_case_children(
    result: &SuccessVerifyByInducCaseResult,
    visitor: &mut ResultChildVisitor<'_>,
) {
    for step in &result.proof_steps {
        visitor.visit(step);
    }
    for conclusion in &result.conclusions {
        visitor.visit(&conclusion.check);
    }
}

fn try_visit_induc_children_mut<E>(
    verification: Option<&mut SuccessVerifyByInducResult>,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    let Some(verification) = verification else {
        return Ok(());
    };
    match &mut verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            for step in &mut proof.proof_steps {
                visitor.visit(step)?;
            }
            for goal in &mut proof.goals {
                visitor.visit(&mut goal.base_check)?;
                visitor.visit(&mut goal.start_in_z_check)?;
                visitor.visit(&mut goal.step_check)?;
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            visitor.visit(&mut proof.start_in_z_check)?;
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
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    for step in &mut result.proof_steps {
        visitor.visit(step)?;
    }
    for conclusion in &mut result.conclusions {
        visitor.visit(&mut conclusion.check)?;
    }
    Ok(())
}

fn try_visit_induc_case_children_mut<E>(
    result: &mut SuccessVerifyByInducCaseResult,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    for step in &mut result.proof_steps {
        visitor.visit(step)?;
    }
    for conclusion in &mut result.conclusions {
        visitor.visit(&mut conclusion.check)?;
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
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            children.extend(proof.base.proof_steps);
            children.extend(proof.step.proof_steps);
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            children.extend(into_induc_case_children(proof.base));
            children.extend(into_induc_case_children(proof.step));
        }
    }
    children
}

fn into_induc_case_children(result: SuccessVerifyByInducCaseResult) -> Vec<StmtResult> {
    result.proof_steps
}

impl SuccessWitnessStmtResult {
    fn visit_named_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        match self {
            Self::WitnessExistFact(result) => {
                if let Some(verification) = &result.verification {
                    visit_witness_exist_children(verification, visitor);
                }
            }
            Self::WitnessAtomicFact(result) => {
                if let Some(verification) = &result.verification {
                    for check in &verification.definition_parameter_verification.checks {
                        visitor.visit(check);
                    }
                    visit_witness_exist_children(&verification.witness_verification, visitor);
                }
            }
            Self::WitnessNonemptySet(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor.visit(step);
                    }
                    visitor.visit(&verification.nonempty_check);
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
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
                        visitor.visit(check)?;
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
                        visitor.visit(step)?;
                    }
                    visitor.visit(&mut verification.nonempty_check)?;
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
                .map(|verification| into_witness_exist_children(verification.witness_verification))
                .unwrap_or_default(),
            Self::WitnessNonemptySet(result) => result
                .verification
                .map(|verification| verification.proof_steps)
                .unwrap_or_default(),
        }
    }
}

fn visit_witness_exist_children(
    verification: &SuccessVerifyWitnessExistResult,
    visitor: &mut ResultChildVisitor<'_>,
) {
    for check in verification.parameter_checks.iter().flatten() {
        visitor.visit(check);
    }
    for step in &verification.proof_steps {
        visitor.visit(step);
    }
    for check in &verification.body_checks {
        visitor.visit(check);
    }
    if let Some(check) = &verification.uniqueness_check {
        visitor.visit(check);
    }
}

fn try_visit_witness_exist_children_mut<E>(
    verification: &mut SuccessVerifyWitnessExistResult,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    for check in verification.parameter_checks.iter_mut().flatten() {
        visitor.visit(check)?;
    }
    for step in &mut verification.proof_steps {
        visitor.visit(step)?;
    }
    for check in &mut verification.body_checks {
        visitor.visit(check)?;
    }
    if let Some(check) = &mut verification.uniqueness_check {
        visitor.visit(check)?;
    }
    Ok(())
}

fn into_witness_exist_children(verification: SuccessVerifyWitnessExistResult) -> Vec<StmtResult> {
    verification.proof_steps
}

impl SuccessProofBlockStmtResult {
    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::ClaimStmt(result) => result.proof_steps,
            Self::ExampleStmt(result) => claim_child_results(result.verification),
            Self::SketchStmt(result) => result
                .proof
                .map(|proof| proof.proof_steps)
                .unwrap_or_default(),
            Self::TryStmt(result) => match result.execution {
                TryStmtExecutionResult::Committed(proof) => proof.proof_steps,
                TryStmtExecutionResult::RolledBack(_)
                | TryStmtExecutionResult::SkippedByTrustedExecution => vec![],
            },
        }
    }

    fn visit_named_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        match self {
            Self::ClaimStmt(result) => {
                for step in &result.proof_steps {
                    visitor.visit(step);
                }
                for check in &result.conclusion_checks {
                    visitor.visit(check);
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
                        visitor.visit(step);
                    }
                }
            }
            Self::TryStmt(result) => {
                if let TryStmtExecutionResult::Committed(proof) = &result.execution {
                    for step in &proof.proof_steps {
                        visitor.visit(step);
                    }
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
    ) -> Result<(), E> {
        match self {
            Self::ClaimStmt(result) => {
                for step in &mut result.proof_steps {
                    visitor.visit(step)?;
                }
                for check in &mut result.conclusion_checks {
                    visitor.visit(check)?;
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
                        visitor.visit(step)?;
                    }
                }
            }
            Self::TryStmt(result) => {
                if let TryStmtExecutionResult::Committed(proof) = &mut result.execution {
                    for step in &mut proof.proof_steps {
                        visitor.visit(step)?;
                    }
                }
            }
        }
        Ok(())
    }
}

fn claim_child_results(verification: Option<SuccessCheckedGoalBlockResult>) -> Vec<StmtResult> {
    let Some(result) = verification else {
        return Vec::new();
    };
    result.proof_steps
}

impl SuccessCheckedGoalBlockResult {
    fn visit_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        for step in &self.proof_steps {
            visitor.visit(step);
        }
        for check in &self.conclusion_checks {
            visitor.visit(check);
        }
    }

    fn try_visit_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
    ) -> Result<(), E> {
        for step in &mut self.proof_steps {
            visitor.visit(step)?;
        }
        for check in &mut self.conclusion_checks {
            visitor.visit(check)?;
        }
        Ok(())
    }
}

impl SuccessDefinitionStmtResult {
    fn visit_named_child_results(&self, visitor: &mut ResultChildVisitor<'_>) {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.source_result);
                }
            }
            Self::ObtainObjFromExistFact(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.source_result);
                }
            }
            Self::ObtainObjFromAtomicFact(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.source_result);
                }
            }
            Self::ObtainObjFromThm(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.source_result);
                }
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                if let Some(verification) = &result.verification {
                    for group in &verification.groups {
                        if let Some(check) = &group.nonempty_check {
                            visitor.visit(check);
                        }
                    }
                }
            }
            Self::HaveObjEqualStmt(result) => {
                if let Some(verification) = &result.verification {
                    for check in &verification.type_checks {
                        visitor.visit(check);
                    }
                }
            }
            Self::HaveByPreimageStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.source_membership_check);
                }
            }
            Self::HaveFnEqualStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.return_check);
                }
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor.visit(&verification.coverage_check);
                    for check in &verification.return_checks {
                        visitor.visit(check);
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
                        visitor.visit(check);
                    }
                    for step in &verification.proof_steps {
                        visitor.visit(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor.visit(check);
                    }
                }
            }
            Self::DefThmStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor.visit(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor.visit(check);
                    }
                }
            }
            Self::DefStrategyStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor.visit(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor.visit(check);
                    }
                }
            }
            Self::DefAlgoStmt(result) => {
                if let Some(verification) = &result.run_in_local_env {
                    for case in &verification.cases {
                        visitor.visit(&case.verification);
                    }
                    if let Some(default_return) = &verification.default_return {
                        visitor.visit(&default_return.verification);
                    }
                    if let Some(coverage) = &verification.coverage {
                        visitor.visit(&coverage.verification);
                    }
                }
            }
            _ => {}
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut ResultChildMutVisitor<'_, E>,
    ) -> Result<(), E> {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromExistFact(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromAtomicFact(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromThm(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.source_result)?;
                }
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for group in &mut verification.groups {
                        if let Some(check) = &mut group.nonempty_check {
                            visitor.visit(check)?;
                        }
                    }
                }
            }
            Self::HaveObjEqualStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for check in &mut verification.type_checks {
                        visitor.visit(check)?;
                    }
                }
            }
            Self::HaveByPreimageStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.source_membership_check)?;
                }
            }
            Self::HaveFnEqualStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.return_check)?;
                }
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor.visit(&mut verification.coverage_check)?;
                    for check in &mut verification.return_checks {
                        visitor.visit(check)?;
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
                        visitor.visit(check)?;
                    }
                    for step in &mut verification.proof_steps {
                        visitor.visit(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor.visit(check)?;
                    }
                }
            }
            Self::DefThmStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor.visit(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor.visit(check)?;
                    }
                }
            }
            Self::DefStrategyStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor.visit(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor.visit(check)?;
                    }
                }
            }
            Self::DefAlgoStmt(result) => {
                if let Some(verification) = &mut result.run_in_local_env {
                    for case in &mut verification.cases {
                        visitor.visit(&mut case.verification)?;
                    }
                    if let Some(default_return) = &mut verification.default_return {
                        visitor.visit(&mut default_return.verification)?;
                    }
                    if let Some(coverage) = &mut verification.coverage {
                        visitor.visit(&mut coverage.verification)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::ObtainObjFromExistFact(result) => {
                let _ = result;
                Vec::new()
            }
            Self::ObtainObjFromAtomicFact(result) => {
                let _ = result;
                Vec::new()
            }
            Self::ObtainObjFromThm(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveObjEqualStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveByPreimageStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveFnEqualStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveFnByInducStmt(result) => {
                let _ = result;
                Vec::new()
            }
            Self::HaveFnByForallExistUniqueStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    if let Some(check) = verification.source_forall_check {
                        let _ = check;
                    }
                    children.extend(verification.proof_steps);
                }
                children
            }
            Self::DefTemplateStmt(result) => vec![(*result.body_statement_result).into()],
            Self::DefThmStmt(result) => result
                .verification
                .map(|verification| verification.proof_steps)
                .unwrap_or_default(),
            Self::DefStrategyStmt(result) => result
                .verification
                .map(|verification| verification.proof_steps)
                .unwrap_or_default(),
            Self::DefAlgoStmt(result) => {
                let _ = result;
                Vec::new()
            }
            _other => Vec::new(),
        }
    }
}

fn visit_have_fn_by_induc_children(
    verification: &SuccessVerifyHaveFnByInducResult,
    visitor: &mut ResultChildVisitor<'_>,
) {
    visitor.visit(
        &verification
            .verification_run_in_local_env
            .measure
            .measure_integer_check,
    );
    visitor.visit(
        &verification
            .verification_run_in_local_env
            .measure
            .lower_bound_integer_check,
    );
    visitor.visit(
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
    visitor: &mut ResultChildVisitor<'_>,
) {
    visitor.visit(&cases.coverage_check);
    for disjointness in &cases.mutual_exclusions {
        visitor.visit(&disjointness.negated_atom_check);
    }
    for case in &cases.cases {
        match &case.body {
            SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                visitor.visit(&body.return_membership_check)
            }
            SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                visit_have_fn_by_induc_case_list_children(nested, visitor)
            }
        }
    }
}

fn try_visit_have_fn_by_induc_children_mut<E>(
    verification: &mut SuccessVerifyHaveFnByInducResult,
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    visitor.visit(
        &mut verification
            .verification_run_in_local_env
            .measure
            .measure_integer_check,
    )?;
    visitor.visit(
        &mut verification
            .verification_run_in_local_env
            .measure
            .lower_bound_integer_check,
    )?;
    visitor.visit(
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
    visitor: &mut ResultChildMutVisitor<'_, E>,
) -> Result<(), E> {
    visitor.visit(&mut cases.coverage_check)?;
    for disjointness in &mut cases.mutual_exclusions {
        visitor.visit(&mut disjointness.negated_atom_check)?;
    }
    for case in &mut cases.cases {
        match &mut case.body {
            SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                visitor.visit(&mut body.return_membership_check)?
            }
            SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                try_visit_have_fn_by_induc_case_list_children_mut(nested, visitor)?
            }
        }
    }
    Ok(())
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
            Self::ByZornLemmaStmt(result) => result.common,
            Self::ByAxiomOfChoiceStmt(result) => result.common,
            Self::ByRegularityAxiomStmt(result) => result.common,
            Self::ByDefStmt(result) => result.common,
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
            Self::ByZornLemmaStmt(result) => result.statement.clone().into(),
            Self::ByAxiomOfChoiceStmt(result) => result.statement.clone().into(),
            Self::ByRegularityAxiomStmt(result) => result.statement.clone().into(),
            Self::ByDefStmt(result) => result.statement.clone().into(),
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
            Self::ByZornLemmaStmt(result) => &result.common,
            Self::ByAxiomOfChoiceStmt(result) => &result.common,
            Self::ByRegularityAxiomStmt(result) => &result.common,
            Self::ByDefStmt(result) => &result.common,
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
            Self::ByZornLemmaStmt(result) => &mut result.common,
            Self::ByAxiomOfChoiceStmt(result) => &mut result.common,
            Self::ByRegularityAxiomStmt(result) => &mut result.common,
            Self::ByDefStmt(result) => &mut result.common,
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
    fn into_common(self) -> Option<SuccessStmtCommonResult> {
        match self {
            Self::ClaimStmt(_) => None,
            Self::ExampleStmt(result) => Some(result.common),
            Self::SketchStmt(result) => Some(result.common),
            Self::TryStmt(result) => Some(result.common),
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

    fn common(&self) -> Option<&SuccessStmtCommonResult> {
        match self {
            Self::ClaimStmt(_) => None,
            Self::ExampleStmt(result) => Some(&result.common),
            Self::SketchStmt(result) => Some(&result.common),
            Self::TryStmt(result) => Some(&result.common),
        }
    }

    fn common_mut(&mut self) -> Option<&mut SuccessStmtCommonResult> {
        match self {
            Self::ClaimStmt(_) => None,
            Self::ExampleStmt(result) => Some(&mut result.common),
            Self::SketchStmt(result) => Some(&mut result.common),
            Self::TryStmt(result) => Some(&mut result.common),
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
