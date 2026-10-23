/// Construct the one/two-binder result of the checked real-line certificate.
pub(super) fn real_comparison_witness(
    base: &str,
    membership: &str,
    relation: &str,
    witness_left: bool,
    two_parameters: bool,
) -> String {
    let mut steps = vec![
        format!("let _real_base := {base}"),
        format!("have _real_base_member : Litex.In _real_base Litex.R := {membership}"),
    ];
    let (witness, member, proof) = if relation == "eq" {
        ("_real_base", "_real_base_member", "(by rfl)".to_string())
    } else {
        let lemma = if witness_left {
            "existsRealBelow"
        } else {
            "existsRealAbove"
        };
        steps.push(format!("obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.{lemma} _real_base _real_base_member"));
        let arguments = if witness_left {
            "_real_witness _real_base"
        } else {
            "_real_base _real_witness"
        };
        let proof = match relation {
            "ne" => format!("(Litex.ltNotSame {arguments} _real_order)"),
            "le" => format!("(Litex.ltToLe {arguments} _real_order)"),
            _ => "_real_order".to_string(),
        };
        ("_real_witness", "_real_member", proof)
    };
    let prefix = if two_parameters {
        "_real_base, _real_base_member, "
    } else {
        ""
    };
    steps.push(format!("exact ⟨{prefix}{witness}, {member}, {proof}⟩"));
    format!("(by\n  {})", steps.join("\n  "))
}
