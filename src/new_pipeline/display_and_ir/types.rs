//! Typed wrappers for IR strings.
//!
//! Construct only via `ir()` in this module
//! (`XxxIR(String)` is module-private). Arbitrary
//! `String` values cannot become these types without going through that path.

use std::borrow::Borrow;
use std::fmt;
use std::ops::Deref;

macro_rules! define_ir {
    ($name:ident) => {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $name(pub(super) String);

        impl $name {
            pub fn as_str(&self) -> &str {
                &self.0
            }

            pub fn display_string(&self) -> String {
                self.0.clone()
            }
        }

        impl Deref for $name {
            type Target = str;

            fn deref(&self) -> &str {
                &self.0
            }
        }

        impl AsRef<str> for $name {
            fn as_ref(&self) -> &str {
                &self.0
            }
        }

        impl Borrow<str> for $name {
            fn borrow(&self) -> &str {
                &self.0
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.0)
            }
        }
    };
}

define_ir!(ObjIR);
define_ir!(FactIR);
define_ir!(StmtIR);
define_ir!(ParamIR);
