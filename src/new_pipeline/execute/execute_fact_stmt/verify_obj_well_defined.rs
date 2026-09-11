use crate::new_pipeline::runtime::runtime_ids::WellDefinednessId2;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

// How object well-definedness was established.
// ByReuse is checked first (session memo cites a prior wd id). Then either
// ByTrivial, or a constructor-specific ByXxxDef path.
pub enum WellDefinednessProofOfObj2 {
    ByReuse(WellDefinednessId2),
    // Atom (identifier / bound), Number, Pi, EulerNumber, ImaginaryUnit,
    // StandardSet, and similar leaves with no further WD obligations.
    ByTrivial,
    ByAddDef(WellDefinednessProofOfAddObj2),
    // Other constructors with requirements get ByXxxDef variants later.
}

pub struct WellDefinednessProofOfAddObj2 {
    pub well_defined_of_left: Box<WellDefinednessProofOfObj2>,
    pub well_defined_of_right: Box<WellDefinednessProofOfObj2>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_obj_well_definedness2(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState2,
    ) -> Result<WellDefinednessProofOfObj2, RuntimeError> {
        // ByReuse comes first once Runtime allocates WellDefinednessId2 and
        // VerifyState2 memos object -> wd id.
        let _ = &verify_state;

        match obj {
            Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_)
            | Obj::Atom(_) => Ok(WellDefinednessProofOfObj2::ByTrivial),
            Obj::Add(add) => self.verify_add_obj_well_definedness2(add, verify_state),
            _ => todo!("object well-definedness for remaining Obj variants"),
        }
    }

    // Example: a + b is WD when both sides are WD and each side is in C.
    fn verify_add_obj_well_definedness2(
        &mut self,
        add: &Add,
        verify_state: VerifyState2,
    ) -> Result<WellDefinednessProofOfObj2, RuntimeError> {
        let _ = (add, verify_state);
        todo!("ByAddDef: child WD + requirement facts")
    }
}
