//! Atomic-fact polarity vocabulary contracts.

use crate::common::defaults::default_line_file;
use crate::fact::{AtomicFact, EqualFact, NotEqualFact};
use crate::obj::{Number, Obj};

#[test]
fn positive_polarity_is_distinct_from_verification_success() {
    let one: Obj = Number::new("1".to_string()).into();
    let equality: AtomicFact = EqualFact::new(one.clone(), one.clone(), default_line_file()).into();
    let inequality: AtomicFact = NotEqualFact::new(one.clone(), one, default_line_file()).into();

    assert!(equality.has_positive_polarity());
    assert!(!inequality.has_positive_polarity());
}
