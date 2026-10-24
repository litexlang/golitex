use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn min_max_arguments(
    obj: &Obj,
    maximum: bool,
) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Min(p)) if !maximum => {
            Some((&p.left, &p.right))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Max(p)) if maximum => Some((&p.left, &p.right)),
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_min_max_selection(
        &self,
        goal: &EqualFact,
        maximum: bool,
        select_left: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let matches = |object: &Obj, selected: &Obj| {
            min_max_arguments(object, maximum)
                .is_some_and(|(a, b)| selected.ir() == if select_left { a.ir() } else { b.ir() })
        };
        let (object, reversed) = if matches(&goal.left, &goal.right) {
            (&goal.left, false)
        } else if matches(&goal.right, &goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::unsupported("MinMax/SelectionSubject"));
        };
        let [requirement] = requirements else {
            return Err(LeanCompileError::unsupported("MinMax/SelectionRequirement"));
        };
        let Fact::AtomicFact(subject) = source_subject(requirement)? else {
            return Err(LeanCompileError::unsupported("MinMax/SelectionOrder"));
        };
        let (a, b) = min_max_arguments(object, maximum).unwrap();
        let (low, high) = if maximum == select_left {
            (b, a)
        } else {
            (a, b)
        };
        let (actual_low, actual_high, strict) = source_order_oriented(&subject)?;
        if strict || actual_low.ir() != low.ir() || actual_high.ir() != high.ir() {
            return Err(LeanCompileError::unsupported("MinMax/SelectionOrder"));
        }
        // The sole search child follows the parent's completed endpoint WD.
        let order = self.compile_verify(requirement, position)?.1;
        let term = self.compile_object_reference(object, position)?;
        let law = match (maximum, select_left) {
            (false, true) => "minOfLeOperands",
            (false, false) => "minOfGeOperands",
            (true, true) => "maxOfGeOperands",
            (true, false) => "maxOfLeOperands",
        };
        let symmetric = if reversed { ".symm" } else { "" };
        Ok(format!("(Litex.{law} {term} {order}){symmetric}"))
    }

    pub(in crate::compile_to_lean) fn numeric_min_max_wd(
        &self,
        wd: &ObjWellDefinedProof,
        children: &[Box<ObjWellDefinedProof>],
        maximum: bool,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        let Some((left, right)) = min_max_arguments(wd.obj(), maximum) else {
            return Err(LeanCompileError::unsupported(
                "MinMax/ObservationConstructor",
            ));
        };
        if children.len() != 2 {
            return Err(LeanCompileError::unsupported("WD/MinMaxStages"));
        }
        ensure_object(left, &children[0])?;
        ensure_object(right, &children[1])?;
        // Constructor replay first validates the exact children and both real domains.
        let term = self.compile_wd(wd, position)?;
        let setup = format!(
            "let _extremum := {term};\nlet _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);\n"
        );
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let mut native = Vec::new();
            let mut equations = Vec::new();
            for (index, child) in children.iter().enumerate() {
                let observation = self.numeric_wd(
                    child,
                    &SourcePosition {
                        before: index,
                        ..*position
                    },
                )?;
                let exact = observation
                    .3
                    .as_ref()
                    .ok_or_else(|| LeanCompileError::unsupported("MinMax/ClosedOperand"))?;
                let real = exact_rational_literal(exact, "ℝ")?;
                equations.push(format!(
                    "(({}).trans (congrArg M.number (by norm_num : {} = (({real} : ℝ) : ℂ))))",
                    observation.1, observation.0
                ));
                native.push(real);
            }
            let operation = if maximum { "Max.max" } else { "Min.min" };
            let scalar = format!("(({operation} {} {} : ℝ) : ℂ)", native[0], native[1]);
            let proof = format!(
                "({setup}Litex.minMaxDenoteReal _extremum {} {} {} {})",
                native[0], native[1], equations[0], equations[1]
            );
            return Ok((scalar, proof, format!("({setup}_member)"), Some(value)));
        }
        Ok((
            format!("({setup}Litex.NativeBridge.asComplex _extremum _member)"),
            format!("({setup}Litex.NativeBridge.asComplex_spec _extremum _member)"),
            format!("({setup}_member)"),
            None,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_min_max_wd(
        &self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        maximum: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 2 || requirements.len() != 2 {
            return Err(LeanCompileError::unsupported("WD/MinMaxStages"));
        }
        let mut terms = Vec::new();
        for (index, obj) in [left, right].iter().enumerate() {
            ensure_object(obj, &children[index])?;
            terms.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, obj) in [left, right].iter().enumerate() {
            if membership_subject(&source_subject(&requirements[index])?, obj)? != StandardSet::R {
                return Err(LeanCompileError::unsupported("WD/MinMaxRealDomain"));
            }
            terms.push(self.compile_wd_requirement(
                &requirements[index],
                &SourcePosition {
                    before: 2 + index,
                    ..*position
                },
            )?);
        }
        let operation = if maximum { "max" } else { "min" };
        Ok(format!("(Litex.{operation} {})", terms.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_min_max_identity(
        &self,
        fact: &EqualFact,
        maximum: bool,
        commutative: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if commutative {
            let (Some((a, b)), Some((c, d))) = (
                min_max_arguments(&fact.left, maximum),
                min_max_arguments(&fact.right, maximum),
            ) else {
                return Err(LeanCompileError::unsupported(
                    "MinMax/CommutativeConstructor",
                ));
            };
            if a.ir() != d.ir() || b.ir() != c.ir() {
                return Err(LeanCompileError::unsupported("MinMax/CommutativeSubject"));
            }
            return Ok(format!(
                "(Litex.minMaxCommutative {} {} (Eq.refl _) (Eq.refl _))",
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?
            ));
        }
        for (obj, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if let Some((a, b)) = min_max_arguments(obj, maximum) {
                if a.ir() == b.ir() && a.ir() == other.ir() {
                    let proof = format!(
                        "(Litex.minMaxIdempotent {} (Eq.refl _))",
                        self.compile_object_reference(obj, position)?
                    );
                    return Ok(if reversed {
                        format!("({proof}).symm")
                    } else {
                        proof
                    });
                }
            }
        }
        Err(LeanCompileError::unsupported("MinMax/IdempotentSubject"))
    }
}
