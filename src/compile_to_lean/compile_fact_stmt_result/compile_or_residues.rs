use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_or_complete_residues(
        &self,
        fact: &OrFact,
        subject: &Obj,
        modulus: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let count = natural_literal(modulus).ok_or_else(|| invalid("LiteralModulus"))?;
        if count < 2 || count != fact.facts.len() {
            return Err(invalid("CoverageCount"));
        }
        let mut seen = vec![false; count];
        let mut branches = Vec::new();
        let mut first_remainder = None;
        for branch in &fact.facts {
            let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)) = branch else {
                return Err(invalid("EqualityBranches"));
            };
            let (remainder, literal, reversed) = residue_branch(equal, subject, modulus)?;
            let residue = natural_literal(literal).ok_or_else(|| invalid("LiteralResidue"))?;
            if residue >= count || seen[residue] {
                return Err(invalid("ResidueCoverage"));
            }
            seen[residue] = true;
            first_remainder.get_or_insert(remainder);
            branches.push((residue, literal, reversed));
        }
        if seen.iter().any(|p| !p) {
            return Err(invalid("ResidueCoverage"));
        }
        // This reference borrows the original Or-branch Mod constructor WD.
        let remainder = self.compile_object_reference(first_remainder.unwrap(), position)?;
        let modulus_numeric = self.compile_numeric_observation(modulus, position)?.1;
        let mut lines = vec![
            format!("let _remainder := {remainder}"),
            format!("have _modulus : Litex.denote _remainder.val.right = M.number (({count} : ℤ) : ℂ) := ({modulus_numeric}).trans (congrArg M.number (by norm_num))"),
            format!("obtain ⟨_residue, _lo, _hi, _value⟩ := Litex.remainderResidueWitness _remainder ({count} : ℤ) (by norm_num) _modulus"),
        ];
        let alternatives = (0..count)
            .map(|k| format!("_residue = ({k} : ℤ)"))
            .collect::<Vec<_>>()
            .join(" ∨ ");
        lines.push(format!("have _cases : {alternatives} := by omega"));
        lines.push(format!(
            "rcases _cases with {}",
            (0..count)
                .map(|k| format!("_case_{k}"))
                .collect::<Vec<_>>()
                .join(" | ")
        ));
        for residue in 0..count {
            let (index, (_, literal, reversed)) = branches
                .iter()
                .enumerate()
                .find(|(_, (k, _, _))| *k == residue)
                .unwrap();
            let observed = self.compile_numeric_observation(literal, position)?.1;
            let literal = self.compile_object_reference(literal, position)?;
            let numeric = format!("(show Litex.denote {literal} = M.number (({residue} : ℤ) : ℂ) from ({observed}).trans (congrArg M.number (by norm_num)))");
            let mut term = format!("(show Litex.Same _remainder {literal} from ((_value.trans (congrArg (fun k : ℤ => M.number (k : ℂ)) _case_{residue})).trans ({numeric}).symm))");
            if *reversed {
                term = format!("({term}).symm");
            }
            if index + 1 != count {
                term = format!("(Or.inl {term})");
            }
            for _ in 0..index {
                term = format!("(Or.inr {term})");
            }
            lines.push(format!("· exact {term}"));
        }
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
fn residue_branch<'a>(
    equal: &'a EqualFact,
    subject: &Obj,
    modulus: &Obj,
) -> Result<(&'a Obj, &'a Obj, bool), LeanCompileError> {
    for (remainder, literal, reversed) in [
        (&equal.left, &equal.right, false),
        (&equal.right, &equal.left, true),
    ] {
        if matches!(remainder,Obj::IntegerOperator(IntegerOperator::Mod(p)) if p.left.ir()==subject.ir() && p.right.ir()==modulus.ir())
            && natural_literal(literal).is_some()
        {
            return Ok((remainder, literal, reversed));
        }
    }
    Err(invalid("OriginalSubjectModulus"))
}
fn natural_literal(obj: &Obj) -> Option<usize> {
    let Obj::Literal(Literal::Number(n)) = obj else {
        return None;
    };
    n.normalized_value.parse().ok()
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ResidueSplit/{part}"))
}
