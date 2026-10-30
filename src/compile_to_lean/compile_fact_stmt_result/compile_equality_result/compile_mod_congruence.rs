use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ModCongruenceStrategySingleStep;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_mod_congruence(
        &self,
        goal: &EqualFact,
        proof: &ModCongruenceStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let invalid = |part| LeanCompileError::unsupported(&format!("ModCongruence/{part}"));
        let (
            Obj::IntegerOperator(IntegerOperator::Mod(left)),
            Obj::IntegerOperator(IntegerOperator::Mod(right)),
        ) = (&goal.left, &goal.right)
        else {
            return Err(invalid("Conclusion"));
        };
        let (Some((operation, a, b)), Some((right_operation, c, d))) =
            (mod_binary(&left.left), mod_binary(&right.left))
        else {
            return Err(invalid("Operation"));
        };
        if operation != right_operation
            || proof.requirement_facts.len() != 3
            || proof.proof_of_requirement_facts.len() != 3
        {
            return Err(invalid("Requirements"));
        }
        let mut equalities = Vec::new();
        let mut lines = Vec::new();
        for (index, (requirement, child)) in proof
            .requirement_facts
            .iter()
            .zip(&proof.proof_of_requirement_facts)
            .enumerate()
        {
            let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = requirement else {
                return Err(invalid("RequirementFamily"));
            };
            let subject = source_subject(child)?;
            if subject.fact_id() != requirement.fact_id() || subject.ir() != requirement.ir() {
                return Err(invalid("RequirementSubject"));
            }
            equalities.push(equal);
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(&proof.proof_of_requirement_facts),
                index,
            );
            let compiled = self.compile_verify(child, &prior)?;
            lines.push(format!(
                "have _mod_requirement_{index} : {} := {}",
                compiled.0, compiled.1
            ));
        }
        if equalities[0].left.ir() != left.right.ir()
            || equalities[0].right.ir() != right.right.ir()
        {
            return Err(invalid("ModulusSubject"));
        }
        let completed = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(&proof.proof_of_requirement_facts),
            3,
        );
        lines.push(format!(
            "let _mod_left := {}",
            self.compile_object_reference(&goal.left, position)?
        ));
        lines.push(format!(
            "let _mod_right := {}",
            self.compile_object_reference(&goal.right, position)?
        ));
        let mut values = Vec::new();
        let mut members = Vec::new();
        for (name, argument, modulus, residue, side) in [
            ("a", a, left.right.as_ref(), &equalities[1].left, "left"),
            ("b", b, left.right.as_ref(), &equalities[2].left, "left"),
            ("c", c, right.right.as_ref(), &equalities[1].right, "right"),
            ("d", d, right.right.as_ref(), &equalities[2].right, "right"),
        ] {
            let elided = mod_residue_elided(argument, modulus, residue)
                .ok_or_else(|| invalid("ResidueSubject"))?;
            let term = format!("_mod_{name}");
            lines.push(format!(
                "let {term} := {}",
                self.compile_object_reference(residue, &completed)?
            ));
            let (value, member, identity) = if elided {
                (
                    format!("(Litex.denote {term})"),
                    format!("(Litex.modInZ {term})"),
                    format!("Litex.integerModValueIdempotent (Litex.denote {term}.val.left) (Litex.denote {term}.val.right) {term}.wd.1 {term}.wd.2.1"),
                )
            } else {
                (
                    format!("(Litex.denote {term}.val.left)"),
                    format!("{term}.wd.1"),
                    "rfl".to_string(),
                )
            };
            lines.push(format!("have {term}_residue : Litex.integerDivisionValue false {value} (Litex.denote _mod_{side}.val.right) = Litex.denote {term} := {identity}"));
            values.push(value);
            members.push(member);
        }
        let native = match operation {
            "Add" => "addValue",
            "Sub" => "subValue",
            "Mul" => "mulValue",
            _ => unreachable!(),
        };
        lines.push(format!("change Litex.integerDivisionValue false (M.{native} {} {}) (Litex.denote _mod_left.val.right) = Litex.integerDivisionValue false (M.{native} {} {}) (Litex.denote _mod_right.val.right)", values[0], values[1], values[2], values[3]));
        lines.push(format!("exact Litex.integerMod{operation}Congr {} {} (Litex.denote _mod_left.val.right) (Litex.denote _mod_right.val.right) {} {} _mod_left.wd.2.1 _mod_requirement_0 (_mod_a_residue.trans (_mod_requirement_1.trans _mod_c_residue.symm)) (_mod_b_residue.trans (_mod_requirement_2.trans _mod_d_residue.symm))", values[..2].join(" "), values[2..].join(" "), members[..2].join(" "), members[2..].join(" ")));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}

fn mod_binary(object: &Obj) -> Option<(&'static str, &Obj, &Obj)> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => Some(("Add", &p.left, &p.right)),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => Some(("Sub", &p.left, &p.right)),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => Some(("Mul", &p.left, &p.right)),
        _ => None,
    }
}

fn mod_residue_elided(argument: &Obj, modulus: &Obj, residue: &Obj) -> Option<bool> {
    if let Obj::IntegerOperator(IntegerOperator::Mod(inner)) = argument {
        if inner.right.as_ref() == modulus {
            return (residue.ir() == argument.ir()).then_some(true);
        }
    }
    match residue {
        Obj::IntegerOperator(IntegerOperator::Mod(p))
            if p.left.ir() == argument.ir() && p.right.ir() == modulus.ir() =>
        {
            Some(false)
        }
        _ => None,
    }
}
