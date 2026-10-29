use super::searched::project_known_premise;
use super::structural_membership::project_structural_membership;
use crate::json_output::helper::{object_for, string};
use crate::prelude::*;

pub(super) fn project_sign(proof: &StructuralRealSignProof, rt: &Runtime) -> JsonValue {
    use StructuralRealSignReason::*;
    let mut fields = vec![
        ("type", string("by_structural_real_sign")),
        ("element", string(proof.element.readable_string())),
        ("sign", string(format!("{:?}", proof.sign))),
    ];
    let kind = match &proof.reason {
        Known { real, source } => {
            fields.push(("real", project_structural_membership(real, rt)));
            fields.push(("source", project_known_premise(source, rt)));
            "known"
        }
        WeakAndNonzero {
            real,
            weak,
            nonzero,
        } => {
            fields.push(("real", project_structural_membership(real, rt)));
            fields.push(("weak", project_known_premise(weak, rt)));
            fields.push(("nonzero", project_known_premise(nonzero, rt)));
            "weak_and_nonzero"
        }
        WeakSignAndNonzero { weak, nonzero } => {
            fields.push(("weak", project_sign(weak, rt)));
            fields.push(("nonzero", project_sign(nonzero, rt)));
            "weak_sign_and_nonzero"
        }
        Membership(p) => {
            fields.push(("membership", project_structural_membership(p, rt)));
            "membership"
        }
        Closed(p) => {
            fields.push((
                "calculation",
                super::closed_calculation::project_atomic_calculation(p, rt),
            ));
            "closed"
        }
        ZeroLiteral => "zero_literal",
        Neg { argument } | PositiveAbs { argument } | PositiveSqrt { argument } => {
            fields.push(("argument", project_sign(argument, rt)));
            match &proof.reason {
                Neg { .. } => "neg",
                PositiveAbs { .. } => "positive_abs",
                _ => "positive_sqrt",
            }
        }
        Add { left, right }
        | Sub { left, right }
        | Mul { left, right }
        | Div { left, right }
        | MinBoth { left, right }
        | MaxBoth { left, right } => {
            fields.push(("left", project_sign(left, rt)));
            fields.push(("right", project_sign(right, rt)));
            match &proof.reason {
                Add { .. } => "add",
                Sub { .. } => "sub",
                Mul { .. } => "mul",
                Div { .. } => "div",
                MinBoth { .. } => "min_both",
                _ => "max_both",
            }
        }
        MinLeft {
            selected,
            other_real,
        }
        | MinRight {
            selected,
            other_real,
        }
        | MaxLeft {
            selected,
            other_real,
        }
        | MaxRight {
            selected,
            other_real,
        } => {
            fields.push(("selected", project_sign(selected, rt)));
            fields.push(("other_real", project_structural_membership(other_real, rt)));
            match &proof.reason {
                MinLeft { .. } => "min_left",
                MinRight { .. } => "min_right",
                MaxLeft { .. } => "max_left",
                _ => "max_right",
            }
        }
        PositivePower {
            base,
            exponent_real,
        } => {
            fields.push(("base", project_sign(base, rt)));
            fields.push((
                "exponent_real",
                project_structural_membership(exponent_real, rt),
            ));
            "positive_power"
        }
        PositiveEvenPower { base, exponent } => {
            fields.push(("base", project_sign(base, rt)));
            fields.push(("exponent", string(exponent.readable_string())));
            "positive_even_power"
        }
        NonnegativeEvenPower {
            base_real,
            exponent,
        } => {
            fields.push(("base_real", project_structural_membership(base_real, rt)));
            fields.push(("exponent", string(exponent.readable_string())));
            "nonnegative_even_power"
        }
        NonnegativeAbs { argument_real } | NonnegativeSqrt { argument_real } => {
            fields.push((
                "argument_real",
                project_structural_membership(argument_real, rt),
            ));
            if matches!(&proof.reason, NonnegativeAbs { .. }) {
                "nonnegative_abs"
            } else {
                "nonnegative_sqrt"
            }
        }
    };
    fields.push(("kind", string(kind)));
    fields.push(("domain_evidence", string("enclosing_object_wd")));
    object_for(rt, fields)
}

pub(super) fn project_membership(proof: &SignedNumericMembershipProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("builtin_rule")),
            ("rule", string("SignedNumericMembership")),
            (
                "base_membership",
                project_structural_membership(&proof.base_membership, rt),
            ),
            ("sign", project_sign(&proof.sign, rt)),
        ],
    )
}
