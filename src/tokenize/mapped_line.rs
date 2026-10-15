/// Transformed line bytes retain their positions in the original input.
pub(super) struct MappedLine {
    pub text: String,
    pub offsets: Vec<usize>,
}

impl MappedLine {
    pub fn new(text: String, offsets: Vec<usize>) -> Self {
        debug_assert_eq!(text.len(), offsets.len());
        Self { text, offsets }
    }
}
