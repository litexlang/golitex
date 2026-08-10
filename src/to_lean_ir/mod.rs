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

mod builtin_rule;
mod carrier;
mod obj;

pub use builtin_rule::{
    ArithmeticBuiltinRuleToLeanIR, BuiltinRuleToLeanIR, DivNotEqualZeroToLeanIR,
    NonzeroExpressionOrientationToLeanIR,
};
pub use carrier::LeanCarrierToLeanIR;
pub use obj::{
    BuiltinObjOperatorToLeanIR, CollectionObjToLeanIR, ConstantObjToLeanIR, ObjToLeanIR,
    StandardSetToLeanIR,
};

#[derive(Clone, Debug)]
pub enum StmtToLeanIR {
    AbstractProp(AbstractPropToLeanIR),
    Prop(PropToLeanIR),
    HaveObjChoice(HaveObjChoiceToLeanIR),
    HaveObjEqual(HaveObjEqualToLeanIR),
    HaveExistentialWitness(HaveExistentialWitnessToLeanIR),
    Proof(ProofStmtToLeanIR),
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
pub struct HaveObjEqualToLeanIR {
    pub definitions: Vec<ObjectDefinitionToLeanIR>,
    pub facts: Vec<FactToLeanIR>,
}

#[derive(Clone, Debug)]
pub struct HaveObjChoiceToLeanIR {
    pub choices: Vec<ObjectChoiceToLeanIR>,
}

#[derive(Clone, Debug)]
pub struct HaveExistentialWitnessToLeanIR {
    /// Checked proof of the exact positive existential being eliminated.
    pub source: FactToLeanIR,
    /// Fresh names introduced in existential-parameter order.
    pub witnesses: Vec<ExistentialWitnessToLeanIR>,
    /// Exact type and direct-body facts exported to the Litex environment.
    pub projections: Vec<FactToLeanIR>,
}

#[derive(Clone, Debug)]
pub struct ExistentialWitnessToLeanIR {
    pub symbol_id: crate::symbol::SymbolId,
    pub name: String,
    /// Instantiated type after substituting any earlier witnesses.
    pub param_type: ParamTypeToLeanIR,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExistentialProjectionRoleToLeanIR {
    ParameterType { witness_index: usize },
    BodyFact { body_index: usize },
}

#[derive(Clone, Debug)]
pub struct ObjectChoiceToLeanIR {
    pub symbol_id: crate::symbol::SymbolId,
    pub name: String,
    pub carrier: ObjToLeanIR,
    /// Checked proof of `litexIsNonemptySet carrier`; this proposition is the
    /// target ABI's existential witness package.
    pub nonempty_proof: FactToLeanIR,
    /// Exact environment-stored `name ∈ carrier` fact and its stable identity.
    pub membership: FactToLeanIR,
}

#[derive(Clone, Debug)]
pub struct ObjectDefinitionToLeanIR {
    pub symbol_id: crate::symbol::SymbolId,
    pub name: String,
    pub param_type: ParamTypeToLeanIR,
    pub value: ObjToLeanIR,
}

#[derive(Clone, Debug)]
pub struct ProofStmtToLeanIR {
    pub facts: Vec<FactToLeanIR>,
    pub inferred_facts: Vec<FactToLeanIR>,
}

#[derive(Clone, Debug)]
pub struct ParamGroupToLeanIR {
    pub symbol_ids: Vec<crate::symbol::SymbolId>,
    pub names: Vec<String>,
    pub param_type: ParamTypeToLeanIR,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamTypeToLeanIR {
    /// A native Lean set whose element carrier is retained explicitly.
    Set {
        element_carrier: LeanCarrierToLeanIR,
    },
    /// A binder plus the source membership proposition that constrains it.
    MemberOf {
        set: ObjToLeanIR,
        element_carrier: LeanCarrierToLeanIR,
    },
    NonemptySet {
        element_carrier: LeanCarrierToLeanIR,
    },
    FiniteSet {
        element_carrier: LeanCarrierToLeanIR,
    },
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
    /// Citation of a positive existential whose binders were alpha-renamed by
    /// parsing or witness extraction.  Runtime lowering admits this node only
    /// after the verifier's canonical existential comparison succeeds.
    ExistentialAlphaRenameCitation {
        source_fact_id: FactId,
        source_proposition: Fact,
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
        /// Typed consequences derived while installing parameters and domain
        /// premises. These must be reconstructed inside the same proof scope.
        inferred_premises: Vec<FactToLeanIR>,
        conclusions: Vec<FactToLeanIR>,
    },
    /// A fact released by `have x T = value`. The declaration itself is a
    /// sibling statement-IR node. Membership/type facts replay the verifier's
    /// check for `value`; the defining equality reduces by reflexivity.
    ObjectDefinition {
        definition: String,
        value: ObjToLeanIR,
        value_check: Option<Box<FactToLeanIR>>,
    },
    /// Membership released by a sibling `ObjectChoiceToLeanIR`. The sibling
    /// carries the nonemptiness proof used by both `Exists.choose` and
    /// `Exists.choose_spec` during emission.
    ObjectChoice {
        definition: String,
        carrier: ObjToLeanIR,
    },
    /// A type or body fact projected by a sibling existential-elimination
    /// statement.  The copied expected proposition makes malformed IR fail
    /// before a projection term is emitted.
    ExistentialElimination {
        source_proposition: Fact,
        role: ExistentialProjectionRoleToLeanIR,
        expected_proposition: Fact,
    },
    CaseSplit {
        coverage: Box<FactToLeanIR>,
        branches: Vec<CaseBranchToLeanIR>,
    },
    ByContradiction {
        reverse_assumption: LocalPremiseToLeanIR,
        steps: Vec<StmtToLeanIR>,
        contradiction: ContradictionToLeanIR,
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

#[derive(Clone, Debug)]
pub struct CaseBranchToLeanIR {
    pub assumption: LocalPremiseToLeanIR,
    pub steps: Vec<StmtToLeanIR>,
    pub exit: CaseBranchExitToLeanIR,
}

#[derive(Clone, Debug)]
pub enum CaseBranchExitToLeanIR {
    Conclusion(FactToLeanIR),
    Contradiction(ContradictionToLeanIR),
}

#[derive(Clone, Debug)]
pub struct ContradictionToLeanIR {
    pub fact: Box<FactToLeanIR>,
    pub negated_fact: Box<FactToLeanIR>,
}

#[derive(Clone)]
pub enum ProofRuleToLeanIR {
    Builtin(BuiltinRuleToLeanIR),
    ObjectReflexivity,
    ClosedRealMembership,
    RealSetNonempty,
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
        /// User proof statements executed in the temporary witness scope.
        /// Body verification may cite their retained FactIds.
        steps: Vec<StmtToLeanIR>,
        /// Exact propositions associated with the two generic premise lists.
        /// Keeping these copies in the rule metadata makes malformed evidence
        /// fail before Lean source is emitted.
        expected_parameter_requirements: Vec<Fact>,
        expected_body_facts: Vec<Fact>,
    },
    ClassicalExcludedMiddle,
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
            ProofRuleToLeanIR::Builtin(rule) => f.debug_tuple("Builtin").field(rule).finish(),
            ProofRuleToLeanIR::ObjectReflexivity => f.write_str("ObjectReflexivity"),
            ProofRuleToLeanIR::ClosedRealMembership => f.write_str("ClosedRealMembership"),
            ProofRuleToLeanIR::RealSetNonempty => f.write_str("RealSetNonempty"),
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
            ProofRuleToLeanIR::ExistIntroduction {
                witnesses,
                steps,
                expected_parameter_requirements,
                expected_body_facts,
            } => f
                .debug_struct("ExistIntroduction")
                .field(
                    "witnesses",
                    &witnesses
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .field("steps", steps)
                .field(
                    "expected_parameter_requirements",
                    &expected_parameter_requirements
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .field(
                    "expected_body_facts",
                    &expected_body_facts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                )
                .finish(),
            ProofRuleToLeanIR::ClassicalExcludedMiddle => f.write_str("ClassicalExcludedMiddle"),
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
    /// Records both the native Lean binder carrier and any separate membership
    /// or set-property requirement retained from Litex.
    pub param_type: ParamTypeToLeanIR,
}

impl fmt::Debug for KnownForallArgumentToLeanIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KnownForallArgumentToLeanIR")
            .field("param", &self.param)
            .field("argument", &self.argument.to_string())
            .field("param_type", &self.param_type)
            .finish()
    }
}

impl ProofRuleToLeanIR {
    pub fn from_verified_builtin_label(label: &str, goal: &Fact) -> Self {
        match label {
            "they are the same" | "known-only equality: they are the same"
                if matches!(
                    goal,
                    Fact::AtomicFact(crate::fact::AtomicFact::EqualFact(equality))
                        if crate::obj::obj_equality_key(&equality.left)
                            == crate::obj::obj_equality_key(&equality.right)
                ) =>
            {
                ProofRuleToLeanIR::ObjectReflexivity
            }
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
            "or: complementary atomic facts" if is_binary_complementary_or(goal) => {
                ProofRuleToLeanIR::ClassicalExcludedMiddle
            }
            "standard_nonempty_set" if is_real_set_nonempty(goal) => {
                ProofRuleToLeanIR::RealSetNonempty
            }
            _ if is_closed_real_membership(goal) => ProofRuleToLeanIR::ClosedRealMembership,
            other => ProofRuleToLeanIR::OtherUnsupported {
                name: other.to_string(),
            },
        }
    }
}

fn is_real_set_nonempty(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(crate::fact::AtomicFact::IsNonemptySetFact(fact))
            if matches!(fact.set, Obj::StandardSet(crate::obj::StandardSet::R))
    )
}

fn is_binary_complementary_or(goal: &Fact) -> bool {
    let Fact::OrFact(or_fact) = goal else {
        return false;
    };
    if or_fact.facts.len() != 2 {
        return false;
    }
    let (
        crate::fact::AndChainAtomicFact::AtomicFact(first),
        crate::fact::AndChainAtomicFact::AtomicFact(second),
    ) = (&or_fact.facts[0], &or_fact.facts[1])
    else {
        return false;
    };
    first
        .logical_negation()
        .is_ok_and(|negated| negated.to_string() == second.to_string())
}

pub(crate) fn is_closed_real_membership(goal: &Fact) -> bool {
    matches!(
        goal,
        Fact::AtomicFact(crate::fact::AtomicFact::InFact(membership))
            if matches!(membership.set, Obj::StandardSet(crate::obj::StandardSet::R))
                && is_closed_rational_obj(&membership.element)
    )
}

fn is_closed_rational_obj(obj: &Obj) -> bool {
    match obj {
        Obj::Number(_) => true,
        Obj::Add(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        Obj::Sub(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        Obj::Mul(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        Obj::Div(value) => {
            is_closed_rational_obj(value.left.as_ref())
                && is_closed_rational_obj(value.right.as_ref())
        }
        _ => false,
    }
}
