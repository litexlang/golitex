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
pub struct LocalPremiseToLeanIR {
    pub fact_id: FactId,
    pub fact: Fact,
}

impl LocalPremiseToLeanIR {
    pub fn new(fact_id: FactId, fact: Fact) -> Self {
        LocalPremiseToLeanIR { fact_id, fact }
    }
}

#[derive(Clone, Debug)]
pub enum FactProofToLeanIR {
    Trusted,
    KnownFactCitation {
        source_fact_id: FactId,
    },
    /// A goal derived by applying one explicit proof rule to recursively
    /// checked premise nodes. This is the extensible compiler-facing proof
    /// shape; adding a transport rule does not require another tree variant.
    RuleApplication {
        rule: ProofRuleToLeanIR,
        /// Verifier-side typing checks retained as evidence. Lean usually
        /// discharges these through elaboration rather than proof arguments.
        parameter_requirements: Vec<FactToLeanIR>,
        premises: Vec<FactToLeanIR>,
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
        parameter_premises: Vec<LocalPremiseToLeanIR>,
        premises: Vec<LocalPremiseToLeanIR>,
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

#[derive(Clone)]
pub enum ProofRuleToLeanIR {
    EqualityRewrite(EqualityRewriteToLeanIR),
    IffRewrite {
        direction: IffDirectionToLeanIR,
    },
    DefinitionReduction {
        definition: String,
    },
    Normalization {
        kind: NormalizationKindToLeanIR,
    },
    KnownForallInstantiation {
        source_fact_id: FactId,
        arguments: Vec<KnownForallArgumentToLeanIR>,
    },
    ModusPonens,
    AndIntroduction,
    ExistIntroduction {
        witnesses: Vec<Obj>,
    },
    CaseSplit,
    OtherUnsupported {
        name: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormalizationKindToLeanIR {
    RationalExpressionSimplification,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IffDirectionToLeanIR {
    Forward,
    Backward,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqualityRewriteDirectionToLeanIR {
    Forward,
    Backward,
}

/// Equality rewrite metadata. In its enclosing `RuleApplication`, premise 0
/// is the fact being transported and premise `n + 1` proves `steps[n]`.
#[derive(Clone, Debug)]
pub struct EqualityRewriteToLeanIR {
    pub steps: Vec<EqualityRewriteStepToLeanIR>,
}

#[derive(Clone)]
pub struct EqualityRewriteStepToLeanIR {
    pub from: Obj,
    pub to: Obj,
    pub direction: EqualityRewriteDirectionToLeanIR,
}

impl fmt::Debug for EqualityRewriteStepToLeanIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EqualityRewriteStepToLeanIR")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("direction", &self.direction)
            .finish()
    }
}

impl fmt::Debug for ProofRuleToLeanIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofRuleToLeanIR::EqualityRewrite(rewrite) => {
                f.debug_tuple("EqualityRewrite").field(rewrite).finish()
            }
            ProofRuleToLeanIR::IffRewrite { direction } => f
                .debug_struct("IffRewrite")
                .field("direction", direction)
                .finish(),
            ProofRuleToLeanIR::DefinitionReduction { definition } => f
                .debug_struct("DefinitionReduction")
                .field("definition", definition)
                .finish(),
            ProofRuleToLeanIR::Normalization { kind } => {
                f.debug_struct("Normalization").field("kind", kind).finish()
            }
            ProofRuleToLeanIR::KnownForallInstantiation {
                source_fact_id,
                arguments,
            } => f
                .debug_struct("KnownForallInstantiation")
                .field("source_fact_id", source_fact_id)
                .field("arguments", arguments)
                .finish(),
            ProofRuleToLeanIR::ModusPonens => f.write_str("ModusPonens"),
            ProofRuleToLeanIR::AndIntroduction => f.write_str("AndIntroduction"),
            ProofRuleToLeanIR::ExistIntroduction { witnesses } => f
                .debug_struct("ExistIntroduction")
                .field(
                    "witnesses",
                    &witnesses
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .finish(),
            ProofRuleToLeanIR::CaseSplit => f.write_str("CaseSplit"),
            ProofRuleToLeanIR::OtherUnsupported { name } => f
                .debug_struct("OtherUnsupported")
                .field("name", name)
                .finish(),
        }
    }
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

impl ProofRuleToLeanIR {
    pub fn from_verified_builtin_label(label: &str, goal: &Fact) -> Self {
        match label {
            "calculation and rational expression simplification" => {
                ProofRuleToLeanIR::Normalization {
                    kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                }
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
                ProofRuleToLeanIR::Normalization {
                    kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                }
            }
            other => ProofRuleToLeanIR::OtherUnsupported {
                name: other.to_string(),
            },
        }
    }
}
