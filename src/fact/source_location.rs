//! Fact source-location access and replacement.

use crate::prelude::*;

impl Fact {
    pub fn line_file(&self) -> LineFile {
        match self {
            Fact::AtomicFact(a) => a.line_file(),
            Fact::ExistFact(e) => e.line_file(),
            Fact::OrFact(o) => o.line_file.clone(),
            Fact::AndFact(a) => a.line_file(),
            Fact::ChainFact(c) => c.line_file(),
            Fact::ForallFact(f) => f.line_file.clone(),
            Fact::ForallFactWithIff(f) => f.line_file.clone(),
            Fact::NotForall(f) => f.line_file(),
        }
    }

    pub fn with_line_file(self, line_file: LineFile) -> Self {
        match self {
            Fact::AtomicFact(a) => Fact::AtomicFact(a.with_line_file(line_file)),
            Fact::ExistFact(mut e) => {
                match &mut e {
                    ExistFactEnum::ExistFact(b)
                    | ExistFactEnum::ExistUniqueFact(b)
                    | ExistFactEnum::NotExistFact(b) => b.line_file = line_file,
                }
                Fact::ExistFact(e)
            }
            Fact::OrFact(mut o) => {
                o.line_file = line_file;
                Fact::OrFact(o)
            }
            Fact::AndFact(mut a) => {
                a.line_file = line_file;
                Fact::AndFact(a)
            }
            Fact::ChainFact(mut c) => {
                c.line_file = line_file;
                Fact::ChainFact(c)
            }
            Fact::ForallFact(mut f) => {
                f.line_file = line_file;
                Fact::ForallFact(f)
            }
            Fact::ForallFactWithIff(mut f) => {
                f.line_file = line_file;
                Fact::ForallFactWithIff(f)
            }
            Fact::NotForall(mut f) => {
                f.forall_fact.line_file = line_file;
                Fact::NotForall(f)
            }
        }
    }

    pub fn into_stmt(self) -> Stmt {
        self.into()
    }
}
