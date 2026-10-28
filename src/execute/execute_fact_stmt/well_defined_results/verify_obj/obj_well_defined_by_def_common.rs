use super::entry::ObjWellDefinedProof;
use super::fail_to_verify_obj_well_defined::FailToVerifyObjWellDefinedByDefCommon;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

/// Reduced stages collect failures only. Detailed stages retain checked children.
/// Children precede requirements when choosing the failure in every mode.
pub enum ObjWellDefinedByDefCommonStages {
    Compact(CompactObjWellDefinedByDefCommonStages),
    Normal(NormalObjWellDefinedByDefCommonStages),
    Detailed(DetailedObjWellDefinedByDefCommonStages),
}
pub struct CompactObjWellDefinedByDefCommonStages {
    pub child_failure: Option<(usize, Box<FailToVerifyObjWellDefinedByDefCommon>)>,
    pub child_count: usize,
    pub requirement_failure: Option<(usize, Box<VerifyFactResult>)>,
    pub requirement_count: usize,
}
pub struct NormalObjWellDefinedByDefCommonStages {
    pub child_failure: Option<(usize, Box<FailToVerifyObjWellDefinedByDefCommon>)>,
    pub child_count: usize,
    pub requirement_failure: Option<(usize, Box<VerifyFactResult>)>,
    pub requirement_count: usize,
}
pub struct DetailedObjWellDefinedByDefCommonStages {
    pub child_obj_well_defined: Vec<VerifyObjWellDefinedResult>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl ObjWellDefinedByDefCommonStages {
    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }
    pub(crate) fn require_mode(&self, detail: OutputDetail) -> RuntimeResult<()> {
        detail.require(self.detail(), "object WD stages")
    }
    pub fn leaf(detail: OutputDetail) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactObjWellDefinedByDefCommonStages {
                child_failure: None,
                child_count: 0,
                requirement_failure: None,
                requirement_count: 0,
            }),
            OutputDetail::Normal => Self::Normal(NormalObjWellDefinedByDefCommonStages {
                child_failure: None,
                child_count: 0,
                requirement_failure: None,
                requirement_count: 0,
            }),
            OutputDetail::Detailed => Self::Detailed(DetailedObjWellDefinedByDefCommonStages {
                child_obj_well_defined: Vec::new(),
                requirement_fact_verified: Vec::new(),
            }),
        }
    }
    pub fn from_children(
        detail: OutputDetail,
        children: Vec<VerifyObjWellDefinedResult>,
    ) -> RuntimeResult<Self> {
        let mut stages = Self::leaf(detail);
        for child in children {
            stages.push_child(child)?;
        }
        Ok(stages)
    }
    pub fn push_child(&mut self, child: VerifyObjWellDefinedResult) -> RuntimeResult<()> {
        if let VerifyObjWellDefinedResult::Success(proof) = &child {
            self.detail().require(proof.detail(), "object WD child")?;
        }
        match self {
            Self::Compact(stages) => {
                capture_failed_child(&mut stages.child_failure, stages.child_count, child);
                stages.child_count += 1;
            }
            Self::Normal(stages) => {
                capture_failed_child(&mut stages.child_failure, stages.child_count, child);
                stages.child_count += 1;
            }
            Self::Detailed(stages) => stages.child_obj_well_defined.push(child),
        }
        Ok(())
    }
    pub fn prepend_child(&mut self, child: VerifyObjWellDefinedResult) -> RuntimeResult<()> {
        if let VerifyObjWellDefinedResult::Success(proof) = &child {
            self.detail().require(proof.detail(), "object WD head")?;
        }
        match self {
            Self::Compact(stages) => {
                if let Some((index, _)) = &mut stages.child_failure {
                    *index += 1;
                }
                prepend_failed_child(&mut stages.child_failure, 0, child);
                stages.child_count += 1;
            }
            Self::Normal(stages) => {
                if let Some((index, _)) = &mut stages.child_failure {
                    *index += 1;
                }
                prepend_failed_child(&mut stages.child_failure, 0, child);
                stages.child_count += 1;
            }
            Self::Detailed(stages) => stages.child_obj_well_defined.insert(0, child),
        }
        Ok(())
    }
    pub fn push_requirement(&mut self, requirement: VerifyFactResult) {
        match self {
            Self::Compact(stages) => {
                capture_failed_requirement(
                    &mut stages.requirement_failure,
                    stages.requirement_count,
                    requirement,
                );
                stages.requirement_count += 1;
            }
            Self::Normal(stages) => {
                capture_failed_requirement(
                    &mut stages.requirement_failure,
                    stages.requirement_count,
                    requirement,
                );
                stages.requirement_count += 1;
            }
            Self::Detailed(stages) => stages.requirement_fact_verified.push(requirement),
        }
    }
    pub fn with_requirements(mut self, requirements: Vec<VerifyFactResult>) -> Self {
        for requirement in requirements {
            self.push_requirement(requirement);
        }
        self
    }
    /// Only retained Detailed formed-child records consume this index.
    pub fn captured_child_count(&self) -> usize {
        match self {
            Self::Detailed(stages) => stages.child_obj_well_defined.len(),
            Self::Compact(stages) => stages.child_count,
            Self::Normal(stages) => stages.child_count,
        }
    }
    pub fn append(&mut self, other: Self) -> RuntimeResult<()> {
        self.detail()
            .require(other.detail(), "object WD appended stages")?;
        match (self, other) {
            (Self::Compact(left), Self::Compact(right)) => {
                if left.child_failure.is_none() {
                    left.child_failure = right
                        .child_failure
                        .map(|(index, failure)| (left.child_count + index, failure));
                }
                if left.requirement_failure.is_none() {
                    left.requirement_failure = right
                        .requirement_failure
                        .map(|(index, failure)| (left.requirement_count + index, failure));
                }
                left.child_count += right.child_count;
                left.requirement_count += right.requirement_count;
            }
            (Self::Normal(left), Self::Normal(right)) => {
                if left.child_failure.is_none() {
                    left.child_failure = right
                        .child_failure
                        .map(|(index, failure)| (left.child_count + index, failure));
                }
                if left.requirement_failure.is_none() {
                    left.requirement_failure = right
                        .requirement_failure
                        .map(|(index, failure)| (left.requirement_count + index, failure));
                }
                left.child_count += right.child_count;
                left.requirement_count += right.requirement_count;
            }
            (Self::Detailed(left), Self::Detailed(right)) => {
                left.child_obj_well_defined
                    .extend(right.child_obj_well_defined);
                left.requirement_fact_verified
                    .extend(right.requirement_fact_verified);
            }
            _ => unreachable!("mode checked before appending"),
        }
        Ok(())
    }
    pub fn failed_child(
        &self,
    ) -> Option<(
        usize,
        &Obj,
        &super::fail_to_verify_obj_well_defined::FailToVerifyObjWellDefinedResult,
    )> {
        let failure = match self {
            Self::Compact(stages) => stages.child_failure.as_ref(),
            Self::Normal(stages) => stages.child_failure.as_ref(),
            Self::Detailed(stages) => {
                return stages.child_obj_well_defined.iter().enumerate().find_map(
                    |(index, child)| match child {
                        VerifyObjWellDefinedResult::Failed { obj, reason } => {
                            Some((index, obj, reason))
                        }
                        VerifyObjWellDefinedResult::Success(_) => None,
                    },
                )
            }
        }?;
        let (index, failure) = failure;
        let FailToVerifyObjWellDefinedByDefCommon::Child { obj, child } = failure.as_ref() else {
            unreachable!("captured child failure")
        };
        Some((*index, obj, child))
    }
    pub fn failed_requirement(&self) -> Option<(usize, &VerifyFactResult)> {
        let failure = match self {
            Self::Compact(stages) => stages.requirement_failure.as_ref(),
            Self::Normal(stages) => stages.requirement_failure.as_ref(),
            Self::Detailed(stages) => {
                return stages
                    .requirement_fact_verified
                    .iter()
                    .enumerate()
                    .find(|(_, requirement)| requirement.is_failed())
            }
        }?;
        Some((failure.0, failure.1.as_ref()))
    }
    pub fn detailed_stages(&self) -> Option<&DetailedObjWellDefinedByDefCommonStages> {
        match self {
            Self::Detailed(stages) => Some(stages),
            Self::Compact(_) | Self::Normal(_) => None,
        }
    }
    pub fn is_fully_known(&self) -> bool {
        match self {
            Self::Compact(stages) => {
                stages.child_failure.is_none() && stages.requirement_failure.is_none()
            }
            Self::Normal(stages) => {
                stages.child_failure.is_none() && stages.requirement_failure.is_none()
            }
            Self::Detailed(stages) => {
                stages
                    .child_obj_well_defined
                    .iter()
                    .all(|child| !child.is_failed())
                    && stages
                        .requirement_fact_verified
                        .iter()
                        .all(|requirement| !requirement.is_failed())
            }
        }
    }
    pub fn into_common_fail(self, root: &Obj) -> FailToVerifyObjWellDefinedByDefCommon {
        match self {
            Self::Compact(stages) => {
                reduced_failure(stages.child_failure, stages.requirement_failure, root)
            }
            Self::Normal(stages) => {
                reduced_failure(stages.child_failure, stages.requirement_failure, root)
            }
            Self::Detailed(stages) => {
                for child in stages.child_obj_well_defined {
                    if let VerifyObjWellDefinedResult::Failed { obj, reason } = child {
                        return FailToVerifyObjWellDefinedByDefCommon::Child {
                            obj,
                            child: Box::new(reason),
                        };
                    }
                }
                for requirement in stages.requirement_fact_verified {
                    if requirement.is_failed() {
                        return FailToVerifyObjWellDefinedByDefCommon::Requirement {
                            obj: root.clone(),
                            result: requirement,
                        };
                    }
                }
                missing_failure()
            }
        }
    }
    pub fn into_success_child_proofs(
        self,
    ) -> (Vec<Box<ObjWellDefinedProof>>, Vec<VerifyFactResult>) {
        OutputDetail::Detailed
            .require(self.detail(), "Detailed object WD packing")
            .unwrap_or_else(|error| panic!("{error}"));
        let Self::Detailed(stages) = self else {
            unreachable!()
        };
        let children = stages
            .child_obj_well_defined
            .into_iter()
            .map(|child| match child {
                VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
                VerifyObjWellDefinedResult::Failed { .. } => {
                    unreachable!("successful stages checked before packing")
                }
            })
            .collect();
        (children, stages.requirement_fact_verified)
    }
}
fn capture_failed_child(
    slot: &mut Option<(usize, Box<FailToVerifyObjWellDefinedByDefCommon>)>,
    index: usize,
    child: VerifyObjWellDefinedResult,
) {
    if slot.is_none() {
        prepend_failed_child(slot, index, child);
    }
}
fn prepend_failed_child(
    slot: &mut Option<(usize, Box<FailToVerifyObjWellDefinedByDefCommon>)>,
    index: usize,
    child: VerifyObjWellDefinedResult,
) {
    if let VerifyObjWellDefinedResult::Failed { obj, reason } = child {
        *slot = Some((
            index,
            Box::new(FailToVerifyObjWellDefinedByDefCommon::Child {
                obj,
                child: Box::new(reason),
            }),
        ));
    }
}
fn capture_failed_requirement(
    slot: &mut Option<(usize, Box<VerifyFactResult>)>,
    index: usize,
    requirement: VerifyFactResult,
) {
    if slot.is_none() && requirement.is_failed() {
        *slot = Some((index, Box::new(requirement)));
    }
}
fn reduced_failure(
    child: Option<(usize, Box<FailToVerifyObjWellDefinedByDefCommon>)>,
    requirement: Option<(usize, Box<VerifyFactResult>)>,
    root: &Obj,
) -> FailToVerifyObjWellDefinedByDefCommon {
    if let Some((_, child)) = child {
        return *child;
    }
    if let Some((_, requirement)) = requirement {
        return FailToVerifyObjWellDefinedByDefCommon::Requirement {
            obj: root.clone(),
            result: *requirement,
        };
    }
    missing_failure()
}
fn missing_failure() -> FailToVerifyObjWellDefinedByDefCommon {
    FailToVerifyObjWellDefinedByDefCommon::Others(
        "object well-definedness failed without child or requirement detail".into(),
    )
}

#[cfg(test)]
mod tests {
    use super::super::fail_to_verify_obj_well_defined::fail_to_verify_obj_well_defined_others;
    use super::super::obj_well_defined_proof_by_def::{
        LiteralObjWellDefinedProofByDef, NumberObjWellDefinedProof, ObjWellDefinedProofByDef,
    };
    use super::*;
    use crate::ast::obj::{Literal, Number};

    fn number(value: &str) -> Obj {
        Obj::Literal(Literal::Number(Number {
            normalized_value: value.into(),
        }))
    }
    fn success(mode: OutputDetail) -> VerifyObjWellDefinedResult {
        VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::by_def(
            mode,
            &number("1"),
            None,
            || {
                ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(
                    NumberObjWellDefinedProof::new(),
                ))
            },
        ))
    }
    fn failure(value: &str) -> VerifyObjWellDefinedResult {
        VerifyObjWellDefinedResult::Failed {
            obj: number(value),
            reason: fail_to_verify_obj_well_defined_others("failure priority control".into()),
        }
    }

    #[test]
    fn reduced_producer_never_runs_the_detailed_constructor() {
        for mode in [
            OutputDetail::Compact,
            OutputDetail::Normal,
            OutputDetail::Detailed,
        ] {
            let built = std::cell::Cell::new(false);
            let proof = ObjWellDefinedProof::by_def(mode, &number("1"), None, || {
                built.set(true);
                ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(
                    NumberObjWellDefinedProof::new(),
                ))
            });
            assert_eq!(proof.detail(), mode);
            assert_eq!(built.get(), mode == OutputDetail::Detailed);
        }
    }

    #[test]
    fn stage_merge_preserves_failure_position_and_prepend_priority() {
        for mode in [
            OutputDetail::Compact,
            OutputDetail::Normal,
            OutputDetail::Detailed,
        ] {
            let mut left = ObjWellDefinedByDefCommonStages::leaf(mode);
            left.push_child(success(mode)).unwrap();
            let mut right = ObjWellDefinedByDefCommonStages::leaf(mode);
            right.push_child(failure("2")).unwrap();
            right.push_child(failure("3")).unwrap();
            left.append(right).unwrap();
            let (index, obj, _) = left.failed_child().unwrap();
            assert_eq!(index, 1);
            assert_eq!(obj, &number("2"));
            assert_eq!(left.captured_child_count(), 3);
            left.prepend_child(failure("4")).unwrap();
            let (index, obj, _) = left.failed_child().unwrap();
            assert_eq!(index, 0);
            assert_eq!(obj, &number("4"));
        }
    }

    #[test]
    fn mixed_mode_children_are_rejected_before_collecting_them() {
        let mut stages = ObjWellDefinedByDefCommonStages::leaf(OutputDetail::Normal);
        assert!(matches!(
            stages.push_child(success(OutputDetail::Compact)),
            Err(crate::runtime::RuntimeError::InternalBug(_))
        ));
        assert_eq!(stages.captured_child_count(), 0);
        assert!(stages.is_fully_known());
    }
}
