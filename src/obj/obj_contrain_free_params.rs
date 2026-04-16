pub type ObjContainFreeParamsType = u8;

impl ObjContainFreeParamsType {
    pub fn new(
        contain_exist_free_params: bool,
        contain_forall_free_params: bool,
        contain_fn_set_free_params: bool,
        contain_set_builder_free_params: bool,
    ) -> Self {
        let mut type_value: ObjContainFreeParamsType = 0;
        if contain_exist_free_params {
            type_value |= 1;
        }
        if contain_forall_free_params {
            type_value |= 2;
        }
        if contain_fn_set_free_params {
            type_value |= 4;
        }
        if contain_set_builder_free_params {
            type_value |= 8;
        }
        type_value
    }

    pub fn contain_exist_free_params(&self) -> bool {
        self & 1 == 1
    }

    pub fn contain_forall_free_params(&self) -> bool {
        self & 2 == 2
    }

    pub fn contain_fn_set_free_params(&self) -> bool {
        self & 4 == 4
    }

    pub fn contain_set_builder_free_params(&self) -> bool {
        self & 8 == 8
    }
}
