#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputDetail {
    Compact,
    Normal,
    Detailed,
}

impl OutputDetail {
    pub fn is_detailed(self) -> bool {
        self == OutputDetail::Detailed
    }
}

#[deprecated(note = "use `OutputDetail`")]
pub type OutputStyle = OutputDetail;
