use super::helper::source_subject;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecReleaseStructDefStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_release_struct_definition(
        &self,
        result: &ExecReleaseStructDefStmtResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseStructDefStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("StructRelease/Failed"));
        };
        if p.release.obj.ir() != p.statement.obj.ir() || p.release.struct_obj != p.struct_obj {
            return Err(LeanCompileError::unsupported("StructRelease/Subject"));
        }
        let prior = SourcePosition {
            before: 0,
            ..*position
        };
        let fact = source_subject(&p.membership)?;
        if !matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==p.statement.obj.ir()
            && matches!(&m.set, Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(s)) if s==&p.struct_obj))
        {
            return Err(LeanCompileError::unsupported(
                "StructRelease/MembershipSubject",
            ));
        }
        let member = self.compile_verify(&p.membership, &prior)?;
        let completed = SourcePosition { before: 1, ..prior };
        let formed = SourcePosition::new(
            Some(&completed),
            SourceOwner::Verify(&p.membership),
            usize::MAX,
        );
        Ok(self
            .compile_struct_layer(&p.release, &member.1, &formed)?
            .join("\n\n"))
    }
}
