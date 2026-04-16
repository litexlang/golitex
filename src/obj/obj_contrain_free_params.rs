#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjContainFreeParamsType(u8);

impl ObjContainFreeParamsType {
    pub fn new(
        contain_exist_free_params: bool,
        contain_forall_free_params: bool,
        contain_fn_set_free_params: bool,
        contain_set_builder_free_params: bool,
    ) -> Self {
        let mut bits: u8 = 0;
        if contain_exist_free_params {
            bits |= 1;
        }
        if contain_forall_free_params {
            bits |= 2;
        }
        if contain_fn_set_free_params {
            bits |= 4;
        }
        if contain_set_builder_free_params {
            bits |= 8;
        }
        Self(bits)
    }

    pub fn contain_exist_free_params(&self) -> bool {
        self.0 & 1 != 0
    }

    pub fn contain_forall_free_params(&self) -> bool {
        self.0 & 2 != 0
    }

    pub fn contain_fn_set_free_params(&self) -> bool {
        self.0 & 4 != 0
    }

    pub fn contain_set_builder_free_params(&self) -> bool {
        self.0 & 8 != 0
    }
}
