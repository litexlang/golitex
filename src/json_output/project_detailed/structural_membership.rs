use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_structural_membership(
    proof: &StructuralMembershipProof,
    rt: &Runtime,
) -> JsonValue {
    use StructuralMembershipReason::*;
    let mut fields = vec![
        ("type", string("by_structural_membership")),
        ("element", string(proof.element.readable_string())),
        (
            "set",
            string(Obj::StandardSet(proof.set.clone()).readable_string()),
        ),
    ];
    let kind = match &proof.reason {
        Known(p) => {
            fields.push(("cite", super::searched::project_known_atomic(p, rt)));
            "known"
        }
        KnownSubset(p) => {
            fields.push(("member_proof", super::searched::project_known_premise(&p.member_proof, rt)));
            fields.push(("subset_proof", super::searched::project_known_premise(&p.subset_proof, rt)));
            "known_subset"
        }
        Closed(p) => {
            fields.push((
                "calculation",
                super::closed_calculation::project_membership("in", p, rt),
            ));
            "closed"
        }
        StandardSuperset(p) => {
            fields.push(("source", project_structural_membership(p, rt)));
            "standard_superset"
        }
        Add { left, right } | Sub { left, right } | Mul { left, right } | Div { left, right } => {
            fields.push(("left", project_structural_membership(left, rt)));
            fields.push(("right", project_structural_membership(right, rt)));
            match &proof.reason {
                Add { .. } => "add",
                Sub { .. } => "sub",
                Mul { .. } => "mul",
                Div { .. } => {
                    fields.push(("domain_evidence", string("enclosing_object_wd")));
                    "div"
                }
                _ => unreachable!(),
            }
        }
        Neg { argument } | Abs { argument } => {
            fields.push(("argument", project_structural_membership(argument, rt)));
            if matches!(&proof.reason, Neg { .. }) {
                "neg"
            } else {
                "abs"
            }
        }
        Pow { base, exponent } => {
            fields.push(("base", project_structural_membership(base, rt)));
            fields.push(("exponent", project_structural_membership(exponent, rt)));
            fields.push(("domain_evidence", string("enclosing_object_wd")));
            "pow"
        }
        Intrinsic(rule) => {
            fields.push(("rule", string(intrinsic_name(rule))));
            fields.push(("domain_evidence", string("enclosing_object_wd")));
            "intrinsic_codomain"
        }
    };
    fields.push(("kind", string(kind)));
    object_for(rt, fields)
}

fn intrinsic_name(rule: &IntrinsicCodomain) -> &'static str {
    use IntrinsicCodomain::*;
    match rule {
        Floor => "floor",
        Ceil => "ceil",
        Sign => "sign",
        Min => "min",
        Max => "max",
        Mod => "mod",
        Quot => "quot",
        Gcd => "gcd",
        Lcm => "lcm",
        Factorial => "factorial",
        Exp => "exp",
        Abs => "abs",
        Sqrt => "sqrt",
        Log => "log",
        Ln => "ln",
        Sin => "sin",
        Cos => "cos",
        Tan => "tan",
        Cot => "cot",
        Arcsin => "arcsin",
        Arccos => "arccos",
        Arctan => "arctan",
        Arccot => "arccot",
        RealPart => "re",
        ImaginaryPart => "img",
        ComplexAbs => "C_abs",


        FiniteSetSize => "finite_set_size",
        FiniteSetMax => "finite_set_max",
        FiniteSetMin => "finite_set_min",
        EulerNumber => "e",
        Pi => "pi",
        ImaginaryUnit => "i",
    }
}
