//! Checked, backend-facing evidence produced only by `Runtime::to_lean_mode`.
//!
//! This IR records the verifier route that succeeded. Lean emission consumes
//! these values and must not re-run Litex proof search or guess a proof from a
//! raw source statement.

use crate::common::fact_id::FactId;
use crate::fact::Fact;
use crate::obj::Obj;
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
use std::fmt;

#[derive(Clone, Debug)]
pub enum StmtToLeanIR {
    AbstractProp(AbstractPropToLeanIR),
    Prop(PropToLeanIR),
    Trust(TrustToLeanIR),
    Fact(FactStmtToLeanIR),
}

#[derive(Clone, Debug)]
pub struct AbstractPropToLeanIR {
    pub name: String,
    pub params: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct PropToLeanIR {
    pub name: String,
    pub params: Vec<ParamGroupToLeanIR>,
    pub iff_facts: Vec<Fact>,
}

#[derive(Clone, Debug)]
pub struct ParamGroupToLeanIR {
    pub names: Vec<String>,
    pub param_type: ParamTypeToLeanIR,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamTypeToLeanIR {
    Real,
    Rational,
    Integer,
    Natural,
    LitexSet,
    LitexNonemptySet,
    Unsupported(String),
}

#[derive(Clone, Debug)]
pub struct TrustToLeanIR {
    pub facts: Vec<FactToLeanIR>,
    pub inferred_facts: Vec<FactToLeanIR>,
}

#[derive(Clone, Debug)]
pub struct FactStmtToLeanIR {
    pub fact: FactToLeanIR,
    pub inferred_facts: Vec<FactToLeanIR>,
}

#[derive(Clone, Debug)]
pub struct FactToLeanIR {
    /// `Some` exactly when this proof node corresponds to an environment-stored
    /// fact. Pure verification subgoals may be anonymous (`None`).
    pub fact_id: Option<FactId>,
    pub proposition: Fact,
    pub proof: FactProofToLeanIR,
}

#[derive(Clone, Debug)]
pub enum FactProofToLeanIR {
    Trusted,
    /// A temporary hypothesis introduced inside a proof. It is rendered as a
    /// local Lean binder, never as an axiom.
    Assumption,
    KnownFact {
        source_fact_id: FactId,
    },
    KnownForall {
        source_fact_id: FactId,
        arguments: Vec<KnownForallArgumentToLeanIR>,
        parameter_requirements: Vec<FactToLeanIR>,
        requirements: Vec<FactToLeanIR>,
    },
    Builtin {
        kind: BuiltinProofKindToLeanIR,
        rule: BuiltinRuleToLeanIR,
        subgoals: Vec<FactToLeanIR>,
    },
    Definition {
        name: String,
    },
    UserStrategy {
        name: String,
    },
    Composite {
        steps: Vec<FactToLeanIR>,
    },
    ForallIntroduction {
        /// Temporary parameter-typing facts. Lean's typed binders discharge
        /// these, but the IR retains their Litex identities and provenance.
        parameter_assumptions: Vec<FactToLeanIR>,
        assumptions: Vec<FactToLeanIR>,
        conclusions: Vec<FactToLeanIR>,
    },
    Inference {
        source_fact_id: Option<FactId>,
        reason: String,
    },
    Memo {
        proof: Box<FactProofToLeanIR>,
    },
    Unsupported {
        reason: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinProofKindToLeanIR {
    Rule,
    Strategy,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuiltinRuleToLeanIR {
    RationalExpressionSimplification,
    Other(String),
}

#[derive(Clone)]
pub struct KnownForallArgumentToLeanIR {
    pub param: String,
    pub argument: Obj,
}

impl fmt::Debug for KnownForallArgumentToLeanIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KnownForallArgumentToLeanIR")
            .field("param", &self.param)
            .field("argument", &self.argument.to_string())
            .finish()
    }
}

impl BuiltinRuleToLeanIR {
    pub fn from_verified_label(label: &str, goal: &Fact) -> Self {
        match label {
            "calculation and rational expression simplification" => {
                BuiltinRuleToLeanIR::RationalExpressionSimplification
            }
            "bounded symbolic normalization"
                if matches!(
                    goal,
                    Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality))
                        if objs_equal_by_rational_expression_evaluation(
                            &equality.left,
                            &equality.right,
                        )
                ) =>
            {
                BuiltinRuleToLeanIR::RationalExpressionSimplification
            }
            other => BuiltinRuleToLeanIR::Other(other.to_string()),
        }
    }
}
