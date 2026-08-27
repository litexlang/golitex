#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputStyle {
    Compact,
    Normal,
    Detailed,
}

impl OutputStyle {
    pub fn is_detailed(self) -> bool {
        self == OutputStyle::Detailed
    }
}
