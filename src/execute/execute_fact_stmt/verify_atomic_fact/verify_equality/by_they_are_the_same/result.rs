// Identity evidence refers to the enclosing equality's two objects. It never
// cites the environment, unfolds a definition, or hides a mathematical premise.
pub enum TheyAreTheSameProof {
    SameIr(SameIrProof),
    SameFreeParamShape(SameFreeParamShapeProof),
}

pub enum SameFreeParamShapeProof {
    FnSet(FnSetAlphaProof),
    AnonymousFn(AnonymousFnAlphaProof),
    SetBuilder(SetBuilderAlphaProof),
}

pub struct SameIrProof {}
pub struct FnSetAlphaProof {}
pub struct AnonymousFnAlphaProof {}
pub struct SetBuilderAlphaProof {}

impl SameIrProof {
    pub fn new() -> Self {
        Self {}
    }
}

impl FnSetAlphaProof {
    pub fn new() -> Self {
        Self {}
    }
}

impl AnonymousFnAlphaProof {
    pub fn new() -> Self {
        Self {}
    }
}

impl SetBuilderAlphaProof {
    pub fn new() -> Self {
        Self {}
    }
}

impl From<SameIrProof> for TheyAreTheSameProof {
    fn from(proof: SameIrProof) -> Self {
        Self::SameIr(proof)
    }
}

impl From<SameFreeParamShapeProof> for TheyAreTheSameProof {
    fn from(proof: SameFreeParamShapeProof) -> Self {
        Self::SameFreeParamShape(proof)
    }
}

impl From<FnSetAlphaProof> for SameFreeParamShapeProof {
    fn from(proof: FnSetAlphaProof) -> Self {
        Self::FnSet(proof)
    }
}

impl From<AnonymousFnAlphaProof> for SameFreeParamShapeProof {
    fn from(proof: AnonymousFnAlphaProof) -> Self {
        Self::AnonymousFn(proof)
    }
}

impl From<SetBuilderAlphaProof> for SameFreeParamShapeProof {
    fn from(proof: SetBuilderAlphaProof) -> Self {
        Self::SetBuilder(proof)
    }
}
