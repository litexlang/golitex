//! Leaf explain for atomic family group `in_fact`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{
    AddInNaturalBuiltinRuleProof,
    CartMembershipBuiltinRuleProof,
    ClosedNumericMembershipBuiltinRuleProof,
    ComplexArithmeticClosureBuiltinRuleProof,
    ComplexCoordinateInComplexBuiltinRuleProof,
    ComplexCoordinateInRealBuiltinRuleProof,
    FamilyUnionMembershipFromMemberBuiltinRuleProof,
    FiniteSetSubsetMembershipBuiltinRuleProof,
    AnonymousFnApplicationInFnRangeBuiltinRuleProof,
    InFactSearchProofByBuiltinRule,
    IndexUnionMembershipFromIndexBuiltinRuleProof,
    IntersectMembershipBuiltinRuleProof,
    IntervalMembershipBuiltinRuleProof,
    ListSetElementMembershipBuiltinRuleProof,
    MulInNaturalBuiltinRuleProof,
    NativeConstantMembershipBuiltinRuleProof,
    NativeScalarCodomainBuiltinRuleProof,
    FiniteSetMaxMemberBuiltinRuleProof,
    FiniteSetMinMemberBuiltinRuleProof,
    PositiveIntegerInNPosBuiltinRuleProof,
            AnonymousFnInDeclaredFnSetBuiltinRuleProof,
    OneSideInfinityIntervalMembershipBuiltinRuleProof,
    PowerSetMembershipBuiltinRuleProof,
    PredecessorInNaturalBuiltinRuleProof,
    PredecessorFromPositiveNaturalBuiltinRuleProof,
    PredecessorFromNaturalAboveZeroBuiltinRuleProof,
    RealArithmeticClosureBuiltinRuleProof,
    RealTrigClosureBuiltinRuleProof,
    RealTrigInComplexBuiltinRuleProof,
    SetBuilderMembershipBuiltinRuleProof,
    SetMinusMembershipBuiltinRuleProof,
    StandardSetSubsetMembershipBuiltinRuleProof,
    StructObjMembershipBuiltinRuleProof,
    UnionMembershipFromLeftBuiltinRuleProof,
    UnionMembershipFromRightBuiltinRuleProof,
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl InFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("Positive minimum", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_en(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_en(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_en(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_en(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_en(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_en(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_en(),
            Self::RealArithmeticConstructorClosure(_) => text("Real arithmetic constructor closure", "Checked real leaves compose under field operations and integer powers; domain guards remain in the enclosing WD proof"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("Natural/integer arithmetic constructor closure", "Checked natural/integer leaves compose under their closed arithmetic constructors; domain guards remain in the enclosing WD proof"),
            Self::RealOperandArithmeticClosure(_) => text("Real arithmetic from checked operands", "Checked real operands remain real under field arithmetic; division also has its checked WD domain"),
            Self::RealPower(_) => text("Real power", "The base is checked real and the enclosing power WD certificate proves a supported real power domain"),
            Self::ClosedExactScalarMembership(_) => text("Exact scalar membership", "Exact real and imaginary coordinates satisfy the target scalar carrier"),
            Self::IntegerArithmeticClosure(_) => text("Integer arithmetic closure", "Checked integer operands remain integers under negation, absolute value, addition, subtraction, multiplication and natural powers"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_en(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_en(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_en(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_en(),
            Self::FoldScalarCodomain(_) => text("Fold carrier", "The checked homogeneous operation and seed preserve the fold carrier"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("Finite aggregate scalar carrier", "Checked summands or factors close the declared scalar carrier; empty sums include zero");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_en(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("Anonymous function return carrier", "A checked direct application inhabits its declared static scalar codomain"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_en(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_en(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_en(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_en(),
            Self::CartMembership(p) => p.rule_name_and_message_en(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_en(),
            Self::StructObjMembership(p) => p.rule_name_and_message_en(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_en(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_en(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_en(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_en(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_en(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_en(),
            Self::IntersectMembership(p) => p.rule_name_and_message_en(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_en(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_en(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_en(),
            Self::IntervalMembership(p) => p.rule_name_and_message_en(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_en(),
            Self::AddInNatural(p) => p.rule_name_and_message_en(),
            Self::MulInNatural(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => {
                text("正实数的最小值", "a,b $in R+ => min(a,b) $in R+")
            }
            Self::PositiveRealProduct(_) => {
                text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+")
            }
            Self::PositiveRealQuotient(_) => {
                text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+")
            }
            Self::NonzeroRationalProduct(_) => {
                text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*")
            }
            Self::NonzeroRationalQuotient(_) => {
                text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*")
            }
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_zh(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_zh(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_zh(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_zh(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_zh(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_zh(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_zh(),
            Self::RealArithmeticConstructorClosure(_) => text(
                "实数运算结构封闭",
                "已验证的实数叶子经四则运算和整数幂仍为实数；定义域条件保留在外层WD证明中",
            ),
            Self::DiscreteArithmeticConstructorClosure(_) => text(
                "自然数/整数运算结构封闭",
                "已验证的自然数/整数叶子经对应的封闭运算保持类型；定义域条件保留在外层WD证明中",
            ),
            Self::RealOperandArithmeticClosure(_) => text(
                "由实数操作数得实数运算结果",
                "已验证的实数操作数经四则运算仍为实数；除法另有已验证的定义域条件",
            ),
            Self::RealPower(_) => text(
                "实数幂",
                "底数已验证为实数；外层幂的定义良好证据验证受支持的实数幂定义域",
            ),
            Self::ClosedExactScalarMembership(_) => {
                text("精确数值载体", "精确的实部和虚部满足目标数值集合的条件")
            }
            Self::IntegerArithmeticClosure(_) => text(
                "整数运算封闭",
                "已验证的整数操作数经取负、绝对值、加减乘及自然数幂仍为整数",
            ),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_zh(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_zh(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_zh(),
            Self::FoldScalarCodomain(_) => {
                text("Fold 的载体", "已验证的齐次运算与初值保持 fold 的载体")
            }
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = (
                    "有限聚合的数值载体",
                    "合法求和项或因子在声明的数值载体内封闭；空求和须包含零",
                );
                BuiltinRuleText {
                    rule_name: name.into(),
                    message: message.into(),
                }
            }
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_zh(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text(
                "匿名函数的返回载体",
                "已验证的直接调用属于其声明的静态数值返回载体",
            ),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_zh(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_zh(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_zh(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_zh(),
            Self::CartMembership(p) => p.rule_name_and_message_zh(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_zh(),
            Self::StructObjMembership(p) => p.rule_name_and_message_zh(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_zh(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_zh(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_zh(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_zh(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_zh(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_zh(),
            Self::IntersectMembership(p) => p.rule_name_and_message_zh(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_zh(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_zh(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_zh(),
            Self::IntervalMembership(p) => p.rule_name_and_message_zh(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_zh(),
            Self::AddInNatural(p) => p.rule_name_and_message_zh(),
            Self::MulInNatural(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => {
                text("正實數的最小值", "a,b $in R+ => min(a,b) $in R+")
            }
            Self::PositiveRealProduct(_) => {
                text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+")
            }
            Self::PositiveRealQuotient(_) => {
                text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+")
            }
            Self::NonzeroRationalProduct(_) => {
                text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*")
            }
            Self::NonzeroRationalQuotient(_) => {
                text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*")
            }
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_zh_hant(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_zh_hant(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_zh_hant(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_zh_hant(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_zh_hant(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_zh_hant(),
            Self::RealArithmeticConstructorClosure(_) => text(
                "實數運算結構封閉",
                "已驗證的實數葉子經四則運算和整數冪仍為實數；定義域條件保留在外層WD證明中",
            ),
            Self::DiscreteArithmeticConstructorClosure(_) => text(
                "自然數/整數運算結構封閉",
                "已驗證的自然數/整數葉子經對應的封閉運算保持類型；定義域條件保留在外層WD證明中",
            ),
            Self::RealOperandArithmeticClosure(_) => text(
                "由已檢查運算元得實數運算",
                "經檢查的實數在體運算下仍為實數；除法亦有已檢查的良定域",
            ),
            Self::RealPower(_) => text(
                "實數冪",
                "底數已驗證為實數；外層冪的良定證據驗證受支援的實數冪定義域",
            ),
            Self::ClosedExactScalarMembership(_) => {
                text("精確純量成員關係", "精確實部與虛部符合目標純量載體")
            }
            Self::IntegerArithmeticClosure(_) => text(
                "整數運算封閉",
                "經檢查的整數在取負、絕對值、加減乘及自然數次方下仍為整數",
            ),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_zh_hant(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_zh_hant(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_zh_hant(),
            Self::FoldScalarCodomain(_) => text("折疊載體", "已檢查的同質運算與初值保持折疊載體"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = (
                    "有限聚合純量載體",
                    "已檢查的加數或因子保持宣告的純量載體封閉；空和包含零",
                );
                BuiltinRuleText {
                    rule_name: name.into(),
                    message: message.into(),
                }
            }
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_zh_hant(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text(
                "匿名函數返回載體",
                "經檢查的直接函數套用屬於宣告的靜態純量陪域",
            ),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::CartMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::StructObjMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_zh_hant(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_zh_hant(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_zh_hant(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_zh_hant(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_zh_hant(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_zh_hant(),
            Self::IntersectMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_zh_hant(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_zh_hant(),
            Self::IntervalMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_zh_hant(),
            Self::AddInNatural(p) => p.rule_name_and_message_zh_hant(),
            Self::MulInNatural(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("Minimum positif", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_fr(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_fr(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_fr(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_fr(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_fr(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_fr(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_fr(),
            Self::RealArithmeticConstructorClosure(_) => text("Clôture des constructeurs arithmétiques réels", "Les feuilles réelles vérifiées restent réelles par les opérations de corps et les puissances entières ; les conditions de domaine restent dans la preuve de bonne définition"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("Clôture arithmétique de N/Z", "Les feuilles de N/Z restent dans leur ensemble sous les opérations autorisées ; les domaines restent dans la preuve externe"),
            Self::RealOperandArithmeticClosure(_) => text("Arithmétique réelle depuis les opérandes vérifiés", "Les opérandes réels vérifiés restent réels sous les opérations de corps ; la division a aussi son domaine vérifié"),
            Self::RealPower(_) => text("Puissance réelle", "La base est vérifiée réelle et le certificat de bonne définition établit un domaine de puissance réelle pris en charge"),
            Self::ClosedExactScalarMembership(_) => text("Appartenance scalaire exacte", "Les coordonnées réelles et imaginaires exactes satisfont l'ensemble porteur scalaire cible"),
            Self::IntegerArithmeticClosure(_) => text("Clôture arithmétique entière", "Les opérandes entiers vérifiés restent entiers sous opposé, valeur absolue, addition, soustraction, multiplication et puissances naturelles"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_fr(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_fr(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_fr(),
            Self::FoldScalarCodomain(_) => text("Ensemble porteur du pli", "L'opération homogène et la valeur initiale vérifiées préservent l'ensemble porteur du pli"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("Ensemble porteur scalaire d'agrégat fini", "Les termes ou facteurs vérifiés ferment l'ensemble porteur scalaire déclaré ; les sommes vides incluent zéro");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_fr(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("Ensemble porteur du retour de fonction anonyme", "Une application directe vérifiée appartient à son codomaine scalaire statique déclaré"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_fr(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_fr(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_fr(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_fr(),
            Self::CartMembership(p) => p.rule_name_and_message_fr(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_fr(),
            Self::StructObjMembership(p) => p.rule_name_and_message_fr(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_fr(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_fr(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_fr(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_fr(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_fr(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_fr(),
            Self::IntersectMembership(p) => p.rule_name_and_message_fr(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_fr(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_fr(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_fr(),
            Self::IntervalMembership(p) => p.rule_name_and_message_fr(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_fr(),
            Self::AddInNatural(p) => p.rule_name_and_message_fr(),
            Self::MulInNatural(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("Положительный минимум", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_ru(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_ru(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_ru(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_ru(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_ru(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_ru(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_ru(),
            Self::RealArithmeticConstructorClosure(_) => text("Замкнутость вещественных арифметических конструкторов", "Проверенные вещественные листья остаются вещественными при операциях поля и целых степенях; условия области сохраняются в доказательстве корректности"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("Арифметическая замкнутость N/Z", "Проверенные листья N/Z сохраняют тип при разрешённых операциях; области остаются во внешнем доказательстве"),
            Self::RealOperandArithmeticClosure(_) => text("Вещественная арифметика из проверенных операндов", "Проверенные вещественные остаются вещественными при операциях поля; область корректности деления также проверена"),
            Self::RealPower(_) => text("Вещественная степень", "Основание проверено как вещественное, а сертификат корректности устанавливает допустимую область вещественной степени"),
            Self::ClosedExactScalarMembership(_) => text("Точная скалярная принадлежность", "Точные действительные и мнимые координаты удовлетворяют целевому скалярному носителю"),
            Self::IntegerArithmeticClosure(_) => text("Замкнутость целочисленной арифметики", "Проверенные целые остаются целыми при отрицании, модуле, сложении, вычитании, умножении и натуральных степенях"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_ru(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_ru(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_ru(),
            Self::FoldScalarCodomain(_) => text("Носитель свёртки", "Проверенная однородная операция и начальное значение сохраняют носитель свёртки"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("Скалярный носитель конечного агрегата", "Проверенные слагаемые или множители сохраняют объявленный скалярный носитель; пустые суммы включают ноль");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_ru(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("Носитель возврата анонимной функции", "Проверенное прямое применение принадлежит объявленной статической скалярной области значений"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_ru(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_ru(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_ru(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_ru(),
            Self::CartMembership(p) => p.rule_name_and_message_ru(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_ru(),
            Self::StructObjMembership(p) => p.rule_name_and_message_ru(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_ru(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_ru(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_ru(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_ru(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_ru(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_ru(),
            Self::IntersectMembership(p) => p.rule_name_and_message_ru(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_ru(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_ru(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_ru(),
            Self::IntervalMembership(p) => p.rule_name_and_message_ru(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_ru(),
            Self::AddInNatural(p) => p.rule_name_and_message_ru(),
            Self::MulInNatural(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("Mínimo positivo", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_es(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_es(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_es(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_es(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_es(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_es(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_es(),
            Self::RealArithmeticConstructorClosure(_) => text("Cierre de constructores aritméticos reales", "Las hojas reales comprobadas siguen siendo reales con operaciones de cuerpo y potencias enteras; las condiciones de dominio quedan en la prueba de buena definición"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("Cierre aritmético de N/Z", "Las hojas N/Z conservan su tipo con las operaciones permitidas; los dominios permanecen en la prueba externa"),
            Self::RealOperandArithmeticClosure(_) => text("Aritmética real desde operandos comprobados", "Los reales comprobados siguen siendo reales bajo operaciones de cuerpo; la división tiene también su dominio comprobado"),
            Self::RealPower(_) => text("Potencia real", "La base está comprobada real y el certificado de buena definición demuestra un dominio admitido de potencia real"),
            Self::ClosedExactScalarMembership(_) => text("Pertenencia escalar exacta", "Las coordenadas reales e imaginarias exactas satisfacen el portador escalar objetivo"),
            Self::IntegerArithmeticClosure(_) => text("Clausura aritmética entera", "Los enteros comprobados siguen siendo enteros bajo negación, valor absoluto, suma, resta, multiplicación y potencias naturales"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_es(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_es(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_es(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_es(),
            Self::FoldScalarCodomain(_) => text("Portador del pliegue", "La operación homogénea y semilla comprobadas conservan el portador del pliegue"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("Portador escalar de agregado finito", "Los sumandos o factores comprobados mantienen cerrado el portador escalar declarado; las sumas vacías incluyen cero");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_es(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("Portador de retorno de función anónima", "Una aplicación directa comprobada pertenece a su codominio escalar estático declarado"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_es(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_es(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_es(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_es(),
            Self::CartMembership(p) => p.rule_name_and_message_es(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_es(),
            Self::StructObjMembership(p) => p.rule_name_and_message_es(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_es(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_es(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_es(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_es(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_es(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_es(),
            Self::IntersectMembership(p) => p.rule_name_and_message_es(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_es(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_es(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_es(),
            Self::IntervalMembership(p) => p.rule_name_and_message_es(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_es(),
            Self::AddInNatural(p) => p.rule_name_and_message_es(),
            Self::MulInNatural(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("القيمة الصغرى موجبة", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_ar(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_ar(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_ar(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_ar(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_ar(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_ar(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_ar(),
            Self::RealArithmeticConstructorClosure(_) => text("انغلاق البنى الحسابية الحقيقية", "تبقى الأوراق الحقيقية المتحقق منها حقيقية تحت عمليات الحقل والقوى الصحيحة؛ وتبقى شروط المجال في برهان حسن التعريف"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("الانغلاق الحسابي لـ N/Z", "تحافظ الأوراق N/Z على نوعها بالعمليات المسموحة؛ تبقى المجالات في البرهان الخارجي"),
            Self::RealOperandArithmeticClosure(_) => text("حساب حقيقي من معاملات متحقق منها", "المعاملات الحقيقية المتحقق منها تبقى حقيقية تحت عمليات الحقل؛ وللقسمة مجال حسن تعريف متحقق منه"),
            Self::RealPower(_) => text("قوة حقيقية", "تم التحقق من أن الأساس حقيقي وشهادة حسن التعريف تثبت مجال قوة حقيقية مدعوما"),
            Self::ClosedExactScalarMembership(_) => text("انتماء قياسي دقيق", "الإحداثيان الحقيقي والتخيلي الدقيقان يحققان المجموعة الحاملة القياسية الهدف"),
            Self::IntegerArithmeticClosure(_) => text("انغلاق الحساب الصحيح", "المعاملات الصحيحة المتحقق منها تبقى صحيحة تحت السالب والقيمة المطلقة والجمع والطرح والضرب والقوى الطبيعية"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_ar(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_ar(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_ar(),
            Self::FoldScalarCodomain(_) => text("مجموعة حاملة للطي", "العملية المتجانسة والقيمة الابتدائية المتحقق منهما تحفظان المجموعة الحاملة للطي"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("مجموعة حاملة قياسية لتجميع منتهٍ", "الحدود أو العوامل المتحقق منها تحفظ المجموعة الحاملة القياسية المعلنة؛ والمجاميع الخالية تتضمن صفرًا");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_ar(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("مجموعة حاملة لإرجاع دالة مجهولة", "تطبيق مباشر متحقق منه ينتمي إلى مجاله المقابل القياسي الساكن المعلن"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_ar(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_ar(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_ar(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_ar(),
            Self::CartMembership(p) => p.rule_name_and_message_ar(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_ar(),
            Self::StructObjMembership(p) => p.rule_name_and_message_ar(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_ar(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_ar(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_ar(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_ar(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_ar(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_ar(),
            Self::IntersectMembership(p) => p.rule_name_and_message_ar(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_ar(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_ar(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_ar(),
            Self::IntervalMembership(p) => p.rule_name_and_message_ar(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_ar(),
            Self::AddInNatural(p) => p.rule_name_and_message_ar(),
            Self::MulInNatural(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("正の実数の最小値", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_ja(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_ja(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_ja(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_ja(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_ja(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_ja(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_ja(),
            Self::RealArithmeticConstructorClosure(_) => text("実数算術構造の閉性", "検証済みの実数の葉は体演算と整数べきで実数を保ち、定義域条件は外側の定義可能性証明に保持される"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("自然数・整数の算術閉性", "許可された演算は自然数・整数の型を保持し、定義域の証明は外側に残る"),
            Self::RealOperandArithmeticClosure(_) => text(
                "検査済みの被演算子から実数演算",
                "検査済みの実数は体演算でも実数であり、除算の定義域も検査済みです",
            ),
            Self::RealPower(_) => text("実数のべき", "底は実数と検査済みで、外側の定義証明が対応する実数べきの定義域を確立します"),
            Self::ClosedExactScalarMembership(_) => text(
                "正確なスカラー所属",
                "正確な実部と虚部は対象スカラー台集合を満たします",
            ),
            Self::IntegerArithmeticClosure(_) => text(
                "整数演算の閉性",
                "検査済みの整数は符号反転、絶対値、加減乗算、自然数乗でも整数です",
            ),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_ja(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_ja(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_ja(),
            Self::FoldScalarCodomain(_) => text(
                "畳み込みの台集合",
                "検査済みの同型演算と初期値は畳み込みの台集合を保ちます",
            ),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("有限集約のスカラー台集合", "検査済みの加数または因子は宣言されたスカラー台集合を保ち、空和はゼロを含みます");
                BuiltinRuleText {
                    rule_name: name.into(),
                    message: message.into(),
                }
            }
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_ja(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text(
                "無名関数の戻り値の台集合",
                "検査済みの直接適用は宣言された静的スカラー終域に属します",
            ),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_ja(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_ja(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_ja(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_ja(),
            Self::CartMembership(p) => p.rule_name_and_message_ja(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_ja(),
            Self::StructObjMembership(p) => p.rule_name_and_message_ja(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_ja(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_ja(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_ja(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_ja(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_ja(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_ja(),
            Self::IntersectMembership(p) => p.rule_name_and_message_ja(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_ja(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_ja(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_ja(),
            Self::IntervalMembership(p) => p.rule_name_and_message_ja(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_ja(),
            Self::AddInNatural(p) => p.rule_name_and_message_ja(),
            Self::MulInNatural(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("양의 실수의 최솟값", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_ko(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_ko(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_ko(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_ko(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_ko(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_ko(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_ko(),
            Self::RealArithmeticConstructorClosure(_) => text("실수 산술 구조의 닫힘", "검사된 실수 잎은 체 연산과 정수 거듭제곱으로 실수를 유지하며 정의역 조건은 바깥 정의 가능성 증명에 남습니다"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("자연수/정수 산술의 닫힘", "허용된 연산은 자연수/정수 유형을 보존하며 정의역 증명은 바깥에 남습니다"),
            Self::RealOperandArithmeticClosure(_) => text("검사된 피연산자로 실수 산술", "검사된 실수는 체 연산에서 실수로 유지되며 나눗셈의 정의 영역도 검사됩니다"),
            Self::RealPower(_) => text("실수 거듭제곱", "밑은 실수로 검사되었으며 바깥 정의 인증서가 지원되는 실수 거듭제곱 정의역을 증명합니다"),
            Self::ClosedExactScalarMembership(_) => text("정확한 스칼라 소속", "정확한 실수부와 허수부 좌표는 대상 스칼라 바탕 집합을 만족합니다"),
            Self::IntegerArithmeticClosure(_) => text("정수 산술 닫힘", "검사된 정수는 부호 반전, 절댓값, 덧셈, 뺄셈, 곱셈 및 자연수 거듭제곱에서 정수로 유지됩니다"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_ko(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_ko(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_ko(),
            Self::FoldScalarCodomain(_) => text("접기 바탕 집합", "검사된 동종 연산과 초깃값은 접기의 바탕 집합을 보존합니다"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("유한 집계 스칼라 바탕 집합", "검사된 항 또는 인자는 선언된 스칼라 바탕 집합을 유지하며 빈 합은 0을 포함합니다");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_ko(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("익명 함수 반환 바탕 집합", "검사된 직접 적용은 선언된 정적 스칼라 공역에 속합니다"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_ko(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_ko(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_ko(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_ko(),
            Self::CartMembership(p) => p.rule_name_and_message_ko(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_ko(),
            Self::StructObjMembership(p) => p.rule_name_and_message_ko(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_ko(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_ko(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_ko(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_ko(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_ko(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_ko(),
            Self::IntersectMembership(p) => p.rule_name_and_message_ko(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_ko(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_ko(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_ko(),
            Self::IntervalMembership(p) => p.rule_name_and_message_ko(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_ko(),
            Self::AddInNatural(p) => p.rule_name_and_message_ko(),
            Self::MulInNatural(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::MinPreservesPositiveCarrier(_) => text("Giá trị nhỏ nhất dương", "a,b $in R+ => min(a,b) $in R+"),
            Self::PositiveRealProduct(_) => text("a,b $in R+ => a*b $in R+", "a,b $in R+ => a*b $in R+"),
            Self::PositiveRealQuotient(_) => text("a,b $in R+ => a/b $in R+", "a,b $in R+ => a/b $in R+"),
            Self::NonzeroRationalProduct(_) => text("a,b $in Q* => a*b $in Q*", "a,b $in Q* => a*b $in Q*"),
            Self::NonzeroRationalQuotient(_) => text("a,b $in Q* => a/b $in Q*", "a,b $in Q* => a/b $in Q*"),
            Self::ClosedNumericMembership(p) => p.rule_name_and_message_vi(),
            Self::ComplexArithmeticClosure(p) => p.rule_name_and_message_vi(),
            Self::RealTrigClosure(p) => p.rule_name_and_message_vi(),
            Self::RealTrigInComplex(p) => p.rule_name_and_message_vi(),
            Self::ComplexCoordinateInReal(p) => p.rule_name_and_message_vi(),
            Self::ComplexCoordinateInComplex(p) => p.rule_name_and_message_vi(),
            Self::RealArithmeticClosure(p) => p.rule_name_and_message_vi(),
            Self::RealArithmeticConstructorClosure(_) => text("Tính đóng của cấu trúc số học thực", "Các lá thực đã kiểm tra vẫn là số thực qua phép toán trường và lũy thừa nguyên; điều kiện miền được giữ trong chứng minh xác định tốt"),
            Self::DiscreteArithmeticConstructorClosure(_) => text("Tính đóng số học của N/Z", "Các phép toán cho phép giữ kiểu N/Z; chứng minh miền nằm ở ngoài"),
            Self::RealOperandArithmeticClosure(_) => text("Số học thực từ toán hạng đã kiểm tra", "Các toán hạng thực đã kiểm tra vẫn thực qua phép toán trường; phép chia cũng có miền xác định tốt đã kiểm tra"),
            Self::RealPower(_) => text("Lũy thừa thực", "Cơ số được kiểm tra là thực và chứng nhận xác định tốt chứng minh miền lũy thừa thực được hỗ trợ"),
            Self::ClosedExactScalarMembership(_) => text("Thuộc về vô hướng chính xác", "Tọa độ thực và ảo chính xác thỏa tập nền vô hướng mục tiêu"),
            Self::IntegerArithmeticClosure(_) => text("Đóng của số học nguyên", "Các toán hạng nguyên đã kiểm tra vẫn nguyên qua đổi dấu, trị tuyệt đối, cộng, trừ, nhân và lũy thừa tự nhiên"),
            Self::FiniteSetMaxMember(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetMinMember(p) => p.rule_name_and_message_vi(),
            Self::NativeScalarCodomain(p) => p.rule_name_and_message_vi(),
            Self::PositiveIntegerInNPos(p) => p.rule_name_and_message_vi(),
            Self::FoldScalarCodomain(_) => text("Tập nền phép gấp", "Phép toán đồng nhất và giá trị khởi tạo đã kiểm tra bảo toàn tập nền của phép gấp"),
            Self::AggregateScalarCodomain(_) => {
                let (name, message) = ("Tập nền vô hướng tổng hợp hữu hạn", "Các số hạng hoặc thừa số đã kiểm tra giữ tập nền vô hướng đã khai báo đóng; tổng rỗng gồm không");
                BuiltinRuleText { rule_name:name.into(), message:message.into() }
            },
            Self::AnonymousFnInDeclaredFnSet(p) => p.rule_name_and_message_vi(),
            Self::AnonymousFnApplicationScalarCodomain(_) => text("Tập nền trả về của hàm ẩn danh", "Áp dụng trực tiếp đã kiểm tra thuộc đối miền vô hướng tĩnh đã khai báo"),
            Self::StandardSetSubsetMembership(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSubsetMembership(p) => p.rule_name_and_message_vi(),
            Self::SetBuilderMembership(p) => p.rule_name_and_message_vi(),
            Self::NativeConstantMembership(p) => p.rule_name_and_message_vi(),
            Self::ListSetElementMembership(p) => p.rule_name_and_message_vi(),
            Self::CartMembership(p) => p.rule_name_and_message_vi(),
            Self::PowerSetMembership(p) => p.rule_name_and_message_vi(),
            Self::StructObjMembership(p) => p.rule_name_and_message_vi(),
            Self::PredecessorInNatural(p) => p.rule_name_and_message_vi(),
            Self::PredecessorFromPositiveNatural(p) => p.rule_name_and_message_vi(),
            Self::PredecessorFromNaturalAboveZero(p) => p.rule_name_and_message_vi(),
            Self::AnonymousFnApplicationInFnRange(p) => p.rule_name_and_message_vi(),
            Self::UnionMembershipFromLeft(p) => p.rule_name_and_message_vi(),
            Self::UnionMembershipFromRight(p) => p.rule_name_and_message_vi(),
            Self::IntersectMembership(p) => p.rule_name_and_message_vi(),
            Self::SetMinusMembership(p) => p.rule_name_and_message_vi(),
            Self::FamilyUnionMembershipFromMember(p) => p.rule_name_and_message_vi(),
            Self::IndexUnionMembershipFromIndex(p) => p.rule_name_and_message_vi(),
            Self::IntervalMembership(p) => p.rule_name_and_message_vi(),
            Self::OneSideInfinityIntervalMembership(p) => p.rule_name_and_message_vi(),
            Self::AddInNatural(p) => p.rule_name_and_message_vi(),
            Self::MulInNatural(p) => p.rule_name_and_message_vi(),
        }
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::MinPreservesPositiveCarrier(_) => None,
            Self::PositiveRealProduct(_)
            | Self::PositiveRealQuotient(_)
            | Self::NonzeroRationalProduct(_)
            | Self::NonzeroRationalQuotient(_) => None,
            Self::ClosedNumericMembership(_) => None,
            Self::ComplexArithmeticClosure(_) => None,
            Self::RealTrigClosure(_) => None,
            Self::RealTrigInComplex(_) => None,
            Self::ComplexCoordinateInReal(_) => None,
            Self::ComplexCoordinateInComplex(_) => None,
            Self::RealArithmeticClosure(_) => None,
            Self::RealOperandArithmeticClosure(_) => None,
            Self::RealArithmeticConstructorClosure(_) => None,
            Self::DiscreteArithmeticConstructorClosure(_) => None,
            Self::RealPower(_) => None,
            Self::ClosedExactScalarMembership(_) => None,
            Self::IntegerArithmeticClosure(_) => None,
            Self::FiniteSetMaxMember(_) | Self::FiniteSetMinMember(_) => None,
            Self::NativeScalarCodomain(_) => None,
            Self::PositiveIntegerInNPos(_) => None,
            Self::AggregateScalarCodomain(_) => None,
            Self::FoldScalarCodomain(_) => None,
            Self::AnonymousFnInDeclaredFnSet(_) => None,
            Self::AnonymousFnApplicationScalarCodomain(_) => None,
            Self::StandardSetSubsetMembership(_) => None,
            Self::FiniteSetSubsetMembership(_) => None,
            Self::SetBuilderMembership(_) => None,
            Self::NativeConstantMembership(_) => None,
            Self::ListSetElementMembership(_) => None,
            Self::CartMembership(_) => None,
            Self::PowerSetMembership(_) => None,
            Self::StructObjMembership(_) => None,
            Self::PredecessorInNatural(p) => p.in_natural_proof.cite_fact_id(),
            Self::PredecessorFromPositiveNatural(p) => p.in_natural_proof.cite_fact_id(),
            Self::PredecessorFromNaturalAboveZero(p) => p.in_natural_proof.cite_fact_id(),
            Self::AnonymousFnApplicationInFnRange(_) => None,
            Self::UnionMembershipFromLeft(_) => None,
            Self::UnionMembershipFromRight(_) => None,
            Self::IntersectMembership(_) => None,
            Self::SetMinusMembership(_) => None,
            Self::FamilyUnionMembershipFromMember(p) => Some(p.cite_member_set_in_family_fact_id),
            Self::IndexUnionMembershipFromIndex(p) => Some(p.cite_index_in_index_set_fact_id),
            Self::IntervalMembership(_) => None,
            Self::OneSideInfinityIntervalMembership(_) => None,
            Self::AddInNatural(_) => None,
            Self::MulInNatural(_) => None,
        }
    }
}

impl ClosedNumericMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Membership by evaluating a closed expression",
            "The evaluated value of the closed expression belongs to the target set",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("闭式求值确认成员关系", "闭式的求值结果属于目标集合")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("閉式求值確認成員關係", "閉式的求值結果屬於目標集合")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance par évaluation d’une expression fermée",
            "La valeur évaluée de l’expression fermée appartient à l’ensemble cible",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность по вычислению замкнутого выражения",
            "Вычисленное значение замкнутого выражения принадлежит целевому множеству",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia por evaluación de una expresión cerrada",
            "El valor evaluado de la expresión cerrada pertenece al conjunto objetivo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الانتماء بتقييم تعبير مغلق",
            "القيمة المحسوبة للتعبير المغلق تنتمي إلى المجموعة المستهدفة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "閉じた式の評価による所属",
            "閉じた式の評価値は対象集合に属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "닫힌 식 평가에 따른 소속",
            "닫힌 식의 평가값이 대상 집합에 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quan hệ thuộc bằng tính biểu thức đóng",
            "Giá trị tính được của biểu thức đóng thuộc tập đích",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ComplexArithmeticClosureBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Complex Arithmetic Closure",
            "Well-defined field arithmetic on complex operands returns a complex value",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("复数运算封闭", "良定的复数运算结果属于复数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "複數運算封閉",
            "子物件良定後，C 載體上的 `+ - * / …` 結果仍在 C",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Clôture arithmétique complexe",
            "Après bonne définition des enfants, `+ - * / …` sur les ensembles porteurs C reste dans C",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Замкнутость комплексной арифметики",
            "После корректности дочерних объектов `+ - * / …` на носителях C остаётся в C",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Clausura aritmética compleja",
            "Tras buena definición de los hijos, `+ - * / …` en portadores C permanece en C",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انغلاق الحساب المركب",
            "بعد حسن تعريف العناصر الفرعية تبقى `+ - * / …` على المجموعات الحاملة C في C",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "複素数演算の閉性",
            "子要素の定義の検証後、C 上の `+ - * / …` の結果は C に属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "복소수 산술 닫힘",
            "하위 객체 정의 검증 후 C 바탕 집합의 `+ - * / …` 결과는 C에 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đóng của số học phức",
            "Sau kiểm tra xác định tốt của đối tượng con, `+ - * / …` trên tập nền C vẫn trong C",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl RealTrigClosureBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real Trig Closure",
            "A well-defined real trigonometric function or its principal inverse returns a real value",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实三角运算封闭", "良定的实三角运算结果属于实数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("實三角運算封閉", "子物件良定後，實三角運算結果屬於實數")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Clôture trigonométrique réelle",
            "Après bonne définition des enfants, les résultats trigonométriques réels sont réels",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Замкнутость вещественной тригонометрии",
            "После корректности дочерних объектов результаты вещественной тригонометрии вещественны",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Clausura trigonométrica real",
            "Tras buena definición de los hijos, los resultados trigonométricos reales son reales",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انغلاق المثلثيات الحقيقية",
            "بعد حسن تعريف العناصر الفرعية تكون نتائج المثلثيات الحقيقية حقيقية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "実三角関数の閉性",
            "子要素の定義の検証後、実三角関数の結果は実数です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "실수 삼각함수 닫힘",
            "하위 객체 정의 검증 후 실수 삼각함숫값은 실수입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đóng của lượng giác thực",
            "Sau kiểm tra xác định tốt của đối tượng con, kết quả lượng giác thực là thực",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl RealTrigInComplexBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real trigonometric value as a complex number",
            "A defined real trigonometric value is real and therefore also belongs to C",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实三角函数值也属于复数",
            "有定义的实三角函数值属于实数，因而也属于复数集合 C",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "實三角函數值也屬於複數",
            "有定義的實三角函數值屬於實數，因而也屬於複數集合 C",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Valeur trigonométrique réelle vue comme complexe",
            "Une valeur trigonométrique réelle bien définie est réelle et appartient donc aussi à C",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Вещественное тригонометрическое значение как комплексное число",
            "Корректно определённое вещественное тригонометрическое значение вещественно и потому принадлежит C",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Valor trigonométrico real como complejo",
            "Un valor trigonométrico real bien definido es real y por tanto también pertenece a C",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة المثلثية الحقيقية كعدد مركب",
            "القيمة المثلثية الحقيقية حسنة التعريف حقيقية ومن ثم تنتمي أيضًا إلى C",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "実三角関数の値の複素数への所属",
            "良定義な実三角関数の値は実数なので C にも属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "실수 삼각함수 값의 복소수 소속",
            "잘 정의된 실수 삼각함수 값은 실수이므로 C에도 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị lượng giác thực thuộc số phức",
            "Giá trị lượng giác thực xác định là số thực nên cũng thuộc C",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ComplexCoordinateInRealBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Complex Coordinate In Real",
            "The modulus, real part and imaginary part of a well-defined complex number are real",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("复坐标属于实数", "模与实部虚部属于实数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "複數座標屬於實數",
            "良定驗證後 `C_abs(z)`、`re(z)`、`img(z)` 為實數",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Coordonnée complexe dans les réels",
            "Après vérification de bonne définition, `C_abs(z)`, `re(z)` et `img(z)` sont réels",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Комплексная координата в вещественных",
            "После проверки корректности `C_abs(z)`, `re(z)`, `img(z)` вещественны",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Coordenada compleja en reales",
            "Tras verificar buena definición, `C_abs(z)`, `re(z)` e `img(z)` son reales",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "إحداثي مركب في الأعداد الحقيقية",
            "بعد التحقق من حسن التعريف تكون `C_abs(z)` و`re(z)` و`img(z)` حقيقية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "複素座標の実数への所属",
            "定義の検証後、`C_abs(z)`、`re(z)`、`img(z)` は実数です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "복소수 좌표의 실수 소속",
            "정의 검증 후 `C_abs(z)`, `re(z)`, `img(z)`는 실수입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tọa độ phức trong số thực",
            "Sau kiểm tra xác định tốt, `C_abs(z)`, `re(z)`, `img(z)` là thực",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ComplexCoordinateInComplexBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Complex Coordinate In Complex",
            "Complex modulus / coordinates also inhabit C via R ⊂ C",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("复坐标属于复数", "模与实部虚部属于复数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("複數座標屬於複數", "複數模或座標亦經 R ⊂ C 屬於 C")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Coordonnée complexe dans les complexes",
            "Le module et les coordonnées complexes appartiennent aussi à C via R ⊂ C",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Комплексная координата в комплексных",
            "Комплексный модуль и координаты также принадлежат C через R ⊂ C",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Coordenada compleja en complejos",
            "El módulo y las coordenadas complejas también pertenecen a C por R ⊂ C",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "إحداثي مركب في الأعداد المركبة",
            "المقياس والإحداثيات المركبة تنتمي أيضًا إلى C عبر R ⊂ C",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "複素座標の複素数への所属",
            "複素数の絶対値と座標は R ⊂ C により C にも属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "복소수 좌표의 복소수 소속",
            "복소수 절댓값과 좌표는 R ⊂ C로 C에도 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tọa độ phức trong số phức",
            "Môđun và tọa độ phức cũng thuộc C qua R ⊂ C",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl RealArithmeticClosureBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real Arithmetic Closure",
            "Absolute value, square root, logarithm and natural logarithm return real values on their checked real domains",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数运算封闭", "良定的实数运算结果属于实数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "實數運算封閉",
            "定義域良定後，abs、sqrt、log、ln 的結果為實數",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Clôture arithmétique réelle",
            "Après bonne définition du domaine, abs, sqrt, log et ln donnent des réels",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Замкнутость вещественной арифметики",
            "После корректности области abs, sqrt, log и ln дают вещественные значения",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Clausura aritmética real",
            "Tras buena definición del dominio, abs, sqrt, log y ln dan valores reales",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انغلاق الحساب الحقيقي",
            "بعد حسن تعريف المجال تكون نتائج abs وsqrt وlog وln حقيقية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "実数演算の閉性",
            "定義域の検証後、abs、sqrt、log、ln の結果は実数です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "실수 산술 닫힘",
            "정의역 검증 후 abs, sqrt, log, ln의 결과는 실수입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đóng của số học thực",
            "Sau kiểm tra xác định tốt của miền, abs, sqrt, log, ln cho kết quả thực",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl StandardSetSubsetMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Standard Set Subset Membership",
            "Membership in a standard number set implies membership in a containing standard number set",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("标准集链上传成员", "沿标准集包含链提升成员关系")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "標準集合子集成員",
            "標準集合中 `x $in S` 與 `S $subset T` 推出 `x $in T`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance par inclusion standard",
            "Pour les ensembles standards, `x $in S` et `S $subset T` impliquent `x $in T`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность по стандартному включению",
            "Для стандартных множеств `x $in S` и `S $subset T` влекут `x $in T`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia por inclusión estándar",
            "En conjuntos estándar, `x $in S` y `S $subset T` implican `x $in T`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء عبر احتواء قياسي",
            "للمجموعات القياسية `x $in S` و`S $subset T` تستلزمان `x $in T`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "標準集合の包含による所属",
            "標準集合では `x $in S` と `S $subset T` から `x $in T` を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "표준 집합 포함 소속",
            "표준 집합에서 `x $in S`와 `S $subset T`로 `x $in T`를 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc về qua tập con chuẩn",
            "Trong tập chuẩn, `x $in S` và `S $subset T` suy ra `x $in T`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetSubsetMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Finite Set Subset Membership",
            "the element belongs to a finite set whose every member belongs to the target carrier",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集成员类型提升",
            "元素属于有限集，且每个列出的成员都属于目标集合",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合子集成員",
            "元素屬於有限集合，該集合每個成員均屬於目標載體",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
                "Appartenance par sous-ensemble fini",
                "L'élément appartient à un ensemble fini dont chaque membre appartient à l'ensemble porteur cible",
            )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
                "Принадлежность по конечному подмножеству",
                "Элемент принадлежит конечному множеству, каждый член которого принадлежит целевому носителю",
            )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
                "Pertenencia por subconjunto finito",
                "El elemento pertenece a conjunto finito cuyos miembros pertenecen al portador objetivo",
            )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء عبر مجموعة جزئية منتهية",
            "العنصر ينتمي إلى مجموعة منتهية ينتمي كل عنصر منها إلى المجموعة الحاملة الهدف",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限部分集合による所属",
            "要素はすべての要素が対象台集合に属する有限集合に属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한 부분집합 소속",
            "원소는 모든 원소가 대상 바탕 집합에 속하는 유한 집합에 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc về qua tập con hữu hạn",
            "Phần tử thuộc tập hữu hạn mà mọi phần tử thuộc tập nền mục tiêu",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl SetBuilderMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Set Builder Membership",
            "Set-builder membership from base membership plus defining facts",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("集合构造成员", "由底集成员与定义事实得集合构造成员")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("集合構造成員", "由基礎成員關係及定義命題得集合構造成員")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l'ensemble en compréhension",
            "Appartenance à la compréhension depuis l'appartenance de base et les propositions définissantes",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность множеству по условию",
            "Принадлежность множеству по условию из базовой принадлежности и определяющих утверждений",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a conjunto por comprensión",
            "Pertenencia a comprensión desde pertenencia base y proposiciones definitorias",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لمجموعة مبنية",
            "انتماء للمجموعة المبنية من الانتماء الأساسي وقضايا التعريف",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "内包表記集合への所属",
            "基底集合への所属と定義命題から内包表記集合への所属を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "조건제시 집합 소속",
            "기초 소속과 정의 명제로 조건제시 집합 소속을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc tập dựng",
            "Thuộc tập dựng từ sự thuộc về cơ sở và các mệnh đề định nghĩa",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NativeConstantMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Native Constant Membership",
            "Native mathematical constants inhabit fixed carriers",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("内置常数成员", "内置数学常数属于固定载体")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("內建常數成員", "內建數學常數屬於固定載體")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance de constante native",
            "Les constantes mathématiques natives appartiennent à des ensembles porteurs fixes",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность встроенной константы",
            "Встроенные математические константы принадлежат фиксированным носителям",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia de constante nativa",
            "Las constantes matemáticas nativas pertenecen a portadores fijos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء ثابت أصلي",
            "الثوابت الرياضية الأصلية تنتمي إلى مجموعات حاملة ثابتة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "組み込み定数の所属",
            "組み込みの数学定数は固定の台集合に属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "내장 상수 소속",
            "내장 수학 상수는 고정된 바탕 집합에 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc về hằng tích hợp",
            "Các hằng toán học tích hợp thuộc tập nền cố định",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ListSetElementMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "List Set Element Membership",
            "An element equal to one of the explicitly listed members belongs to that set",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("列表集元素成员", "等于某一列出元素则属于列表集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "列表集合元素成員",
            "x 等於某個列出元素時屬於 `{a_1, …, a_n}`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance d'élément d'ensemble liste",
            "Si x égale un élément listé, il appartient à `{a_1, …, a_n}`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность элемента списочного множества",
            "Если x равен указанному элементу, он принадлежит `{a_1, …, a_n}`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia de elemento de conjunto de lista",
            "Si x es igual a un elemento listado, pertenece a `{a_1, …, a_n}`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء عنصر مجموعة قائمة",
            "إذا ساوت x عنصرًا مدرجًا فإنها تنتمي إلى `{a_1, …, a_n}`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "リスト集合の要素の所属",
            "x が列挙された要素に等しければ `{a_1, …, a_n}` に属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "목록 집합 원소 소속",
            "x가 열거된 원소와 같으면 `{a_1, …, a_n}`에 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc phần tử tập danh sách",
            "Nếu x bằng phần tử liệt kê thì thuộc `{a_1, …, a_n}`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl CartMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Cart Membership", "The complete domain matches the finite coordinate domain and every coordinate belongs to its factor")
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "笛卡尔积成员",
            "完整定义域等于有限坐标域，且每个坐标属于对应因子",
        )
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "笛卡兒積成員",
            "完整定義域等於有限座標域，且每個座標屬於對應因子",
        )
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Appartenance au produit cartésien", "Le domaine complet est le domaine fini des coordonnées et chaque coordonnée appartient à son facteur")
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Принадлежность декартову произведению", "Полная область равна конечной области координат, и каждая координата принадлежит своему множителю")
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Pertenencia a producto cartesiano", "El dominio completo es el dominio finito de coordenadas y cada coordenada pertenece a su factor")
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لحاصل الضرب الديكارتي",
            "المجال الكامل يساوي مجال الإحداثيات المنتهي وكل إحداثي ينتمي إلى عامله",
        )
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "直積への所属",
            "完全な定義域が有限の座標域と一致し、各座標が対応する因子に属します",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "데카르트 곱 소속",
            "전체 정의역이 유한 좌표 정의역과 일치하고 각 좌표가 해당 인자에 속합니다",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc tích Descartes",
            "Miền đầy đủ bằng miền tọa độ hữu hạn và mỗi tọa độ thuộc thừa số tương ứng",
        )
    }
    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PowerSetMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Power Set Membership",
            "if `A $subset B`, then `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("幂集成员", "子集关系推出幂集成员")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "冪集成員",
            "冪集成員給出以下關係: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l'ensemble des parties",
            "La règle « Appartenance à l'ensemble des parties » établit la relation suivante: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность множеству подмножеств",
            "Правило «Принадлежность множеству подмножеств» устанавливает следующее соотношение: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a conjunto potencia",
            "La regla «Pertenencia a conjunto potencia» establece la siguiente relación: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لمجموعة القوى",
            "تثبت قاعدة «انتماء لمجموعة القوى» العلاقة التالية: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "べき集合への所属",
            "べき集合への所属により次の関係が得られます: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "멱집합 소속",
            "멱집합 소속에 따라 다음 관계를 얻습니다: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc tập lũy thừa",
            "Quy tắc «Thuộc tập lũy thừa» thiết lập quan hệ sau: `A $subset B` ⇒ `A $in power_set(B)`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl StructObjMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Struct Obj Membership",
            "An object belongs to the structure type when its fields satisfy the declared types and defining facts",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("结构对象成员", "结构载体与等价律推出结构集成员")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("結構物件成員", "結構載體與等價律推出 `e` 為結構集合成員")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance d'objet de structure",
            "L'ensemble porteur de structure et les lois d'équivalence établissent l'appartenance de `e`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность структурного объекта",
            "Структурный носитель и законы эквивалентности устанавливают принадлежность `e`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia de objeto de estructura",
            "El portador estructural y las leyes de equivalencia establecen pertenencia de `e`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء كائن بنية",
            "المجموعة الحاملة للبنية وقوانين التكافؤ تثبت انتماء `e`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "構造オブジェクトの所属",
            "構造の台集合と同値法則から `e` の構造集合への所属を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "구조 객체 소속",
            "구조 바탕 집합과 동치 법칙으로 `e`의 구조 집합 소속을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc đối tượng cấu trúc",
            "Tập nền cấu trúc và luật tương đương xác lập sự thuộc về của `e`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PredecessorFromNaturalAboveZeroBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Natural predecessor of a positive natural number",
            "The Natural predecessor of a positive natural number law gives: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "正自然数的前驱属于自然数",
            "正自然数的前驱属于自然数可写为：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正自然數的前驅屬於自然數",
            "正自然數的前驅屬於自然數可寫為：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Prédécesseur naturel d’un naturel positif",
            "La propriété « Prédécesseur naturel d’un naturel positif » donne: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Натуральный предшественник положительного натурального числа",
            "Свойство «Натуральный предшественник положительного натурального числа» выражается равенством: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Predecesor natural de un natural positivo",
            "La propiedad «Predecesor natural de un natural positivo» se expresa como: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "السابق الطبيعي لعدد طبيعي موجب",
            "تُكتب خاصية «السابق الطبيعي لعدد طبيعي موجب» كما يلي: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の自然数の前の数は自然数",
            "正の自然数の前の数は自然数は次の式で表されます：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양의 자연수의 이전 수는 자연수",
            "양의 자연수의 이전 수는 자연수은 다음 식으로 나타납니다: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số liền trước của số tự nhiên dương là số tự nhiên",
            "Tính chất «Số liền trước của số tự nhiên dương là số tự nhiên» được biểu diễn bởi: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PredecessorFromPositiveNaturalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Natural predecessor of a positive natural number",
            "The Natural predecessor of a positive natural number law gives: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "正自然数的前驱属于自然数",
            "正自然数的前驱属于自然数可写为：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正自然數的前驅屬於自然數",
            "正自然數的前驅屬於自然數可寫為：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Prédécesseur naturel d’un naturel positif",
            "La propriété « Prédécesseur naturel d’un naturel positif » donne: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Натуральный предшественник положительного натурального числа",
            "Свойство «Натуральный предшественник положительного натурального числа» выражается равенством: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Predecesor natural de un natural positivo",
            "La propiedad «Predecesor natural de un natural positivo» se expresa como: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "السابق الطبيعي لعدد طبيعي موجب",
            "تُكتب خاصية «السابق الطبيعي لعدد طبيعي موجب» كما يلي: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の自然数の前の数は自然数",
            "正の自然数の前の数は自然数は次の式で表されます：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양의 자연수의 이전 수는 자연수",
            "양의 자연수의 이전 수는 자연수은 다음 식으로 나타납니다: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số liền trước của số tự nhiên dương là số tự nhiên",
            "Tính chất «Số liền trước của số tự nhiên dương là số tự nhiên» được biểu diễn bởi: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PredecessorInNaturalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Natural predecessor of a positive natural number",
            "The Natural predecessor of a positive natural number law gives: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "正自然数的前驱属于自然数",
            "正自然数的前驱属于自然数可写为：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正自然數的前驅屬於自然數",
            "正自然數的前驅屬於自然數可寫為：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Prédécesseur naturel d’un naturel positif",
            "La propriété « Prédécesseur naturel d’un naturel positif » donne: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Натуральный предшественник положительного натурального числа",
            "Свойство «Натуральный предшественник положительного натурального числа» выражается равенством: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Predecesor natural de un natural positivo",
            "La propiedad «Predecesor natural de un natural positivo» se expresa como: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "السابق الطبيعي لعدد طبيعي موجب",
            "تُكتب خاصية «السابق الطبيعي لعدد طبيعي موجب» كما يلي: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の自然数の前の数は自然数",
            "正の自然数の前の数は自然数は次の式で表されます：x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양의 자연수의 이전 수는 자연수",
            "양의 자연수의 이전 수는 자연수은 다음 식으로 나타납니다: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số liền trước của số tự nhiên dương là số tự nhiên",
            "Tính chất «Số liền trước của số tự nhiên dương là số tự nhiên» được biểu diễn bởi: x ∈ N ∧ x ≥ 1 ⇒ x-1 ∈ N",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AnonymousFnApplicationInFnRangeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Anonymous function application in range",
            "A well-defined application of an anonymous function belongs to its range",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("匿名函数应用落在值域", "良定的匿名函数应用落在该函数值域")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("匿名函數套用落在值域", "良定的匿名函數套用屬於其值域")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Application de fonction anonyme dans l'image",
            "Une application bien définie d'une fonction anonyme appartient à son image",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Применение анонимной функции в области значений",
            "Корректно определённое применение анонимной функции принадлежит её области значений",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Aplicación de función anónima en rango",
            "Una aplicación bien definida de función anónima pertenece a su rango",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تطبيق دالة مجهولة في المدى",
            "التطبيق حسن التعريف لدالة مجهولة ينتمي إلى مداها",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "無名関数の適用の値域への所属",
            "適切に定義された無名関数の適用はその値域に属します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "익명 함수 적용의 치역 소속",
            "타당하게 정의된 익명 함수 적용은 그 치역에 속합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Áp dụng hàm ẩn danh trong miền giá trị",
            "Áp dụng xác định tốt của hàm ẩn danh thuộc miền giá trị của nó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl UnionMembershipFromLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union membership from the left set",
            "The Union membership from the left set law gives: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由左集合成员关系得到并集成员关系",
            "由左集合成员关系得到并集成员关系可写为：x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由左集合成員關係得到聯集成員關係",
            "由左集合成員關係得到聯集成員關係可寫為：x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l’union par l’ensemble de gauche",
            "La propriété « Appartenance à l’union par l’ensemble de gauche » donne: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность объединению из левого множества",
            "Свойство «Принадлежность объединению из левого множества» выражается равенством: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a la unión desde el conjunto izquierdo",
            "La propiedad «Pertenencia a la unión desde el conjunto izquierdo» se expresa como: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الانتماء إلى الاتحاد من المجموعة اليسرى",
            "تُكتب خاصية «الانتماء إلى الاتحاد من المجموعة اليسرى» كما يلي: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "左の集合からの和集合への所属",
            "左の集合からの和集合への所属は次の式で表されます：x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "왼쪽 집합으로부터 합집합 소속",
            "왼쪽 집합으로부터 합집합 소속은 다음 식으로 나타납니다: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc hợp từ tập bên trái",
            "Tính chất «Thuộc hợp từ tập bên trái» được biểu diễn bởi: x ∈ A ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl UnionMembershipFromRightBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union membership from the right set",
            "The Union membership from the right set law gives: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由右集合成员关系得到并集成员关系",
            "由右集合成员关系得到并集成员关系可写为：x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由右集合成員關係得到聯集成員關係",
            "由右集合成員關係得到聯集成員關係可寫為：x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l’union par l’ensemble de droite",
            "La propriété « Appartenance à l’union par l’ensemble de droite » donne: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность объединению из правого множества",
            "Свойство «Принадлежность объединению из правого множества» выражается равенством: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a la unión desde el conjunto derecho",
            "La propiedad «Pertenencia a la unión desde el conjunto derecho» se expresa como: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الانتماء إلى الاتحاد من المجموعة اليمنى",
            "تُكتب خاصية «الانتماء إلى الاتحاد من المجموعة اليمنى» كما يلي: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "右の集合からの和集合への所属",
            "右の集合からの和集合への所属は次の式で表されます：x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "오른쪽 집합으로부터 합집합 소속",
            "오른쪽 집합으로부터 합집합 소속은 다음 식으로 나타납니다: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc hợp từ tập bên phải",
            "Tính chất «Thuộc hợp từ tập bên phải» được biểu diễn bởi: x ∈ B ⇒ x ∈ A ∪ B",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IntersectMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Membership of both sets implies membership of their intersection",
            "The Membership of both sets implies membership of their intersection law gives: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "同时属于两集合则属于其交集",
            "同时属于两集合则属于其交集可写为：x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "同時屬於兩集合則屬於其交集",
            "同時屬於兩集合則屬於其交集可寫為：x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance aux deux ensembles et à leur intersection",
            "La propriété « Appartenance aux deux ensembles et à leur intersection » donne: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность обоим множествам даёт принадлежность пересечению",
            "Свойство «Принадлежность обоим множествам даёт принадлежность пересечению» выражается равенством: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a ambos conjuntos implica pertenencia a su intersección",
            "La propiedad «Pertenencia a ambos conjuntos implica pertenencia a su intersección» se expresa como: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الانتماء إلى المجموعتين يستلزم الانتماء إلى تقاطعهما",
            "تُكتب خاصية «الانتماء إلى المجموعتين يستلزم الانتماء إلى تقاطعهما» كما يلي: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "両集合への所属による共通部分への所属",
            "両集合への所属による共通部分への所属は次の式で表されます：x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "두 집합 소속에 따른 교집합 소속",
            "두 집합 소속에 따른 교집합 소속은 다음 식으로 나타납니다: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc cả hai tập suy ra thuộc giao",
            "Tính chất «Thuộc cả hai tập suy ra thuộc giao» được biểu diễn bởi: x ∈ A ∧ x ∈ B ⇒ x ∈ A ∩ B",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl SetMinusMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Set Minus Membership",
            "`x $in A` and `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("差集成员", "属于左且不属于右则属于差集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "差集成員",
            "差集成員給出以下關係: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à la différence",
            "La règle « Appartenance à la différence » établit la relation suivante: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность разности",
            "Правило «Принадлежность разности» устанавливает следующее соотношение: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a diferencia",
            "La regla «Pertenencia a diferencia» establece la siguiente relación: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء للفرق",
            "تثبت قاعدة «انتماء للفرق» العلاقة التالية: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "差集合への所属",
            "差集合への所属により次の関係が得られます: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "차집합 소속",
            "차집합 소속에 따라 다음 관계를 얻습니다: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc hiệu",
            "Quy tắc «Thuộc hiệu» thiết lập quan hệ sau: `x $in A` ∧ `not x $in B` ⇒ `x $in set_minus(A, B)`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FamilyUnionMembershipFromMemberBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Family Union Membership From Member",
            "`A $in F` and `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("由成员集得族并成员", "属于族中某集则属于族并")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由集合族成員得聯集成員",
            "由集合族成員得聯集成員給出以下關係: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l'union d'une famille depuis un membre",
            "La règle « Appartenance à l'union d'une famille depuis un membre » établit la relation suivante: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность объединению семейства из элемента",
            "Правило «Принадлежность объединению семейства из элемента» устанавливает следующее соотношение: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a unión de familia desde miembro",
            "La regla «Pertenencia a unión de familia desde miembro» establece la siguiente relación: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لاتحاد عائلة من عنصر",
            "تثبت قاعدة «انتماء لاتحاد عائلة من عنصر» العلاقة التالية: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "集合族の要素から和への所属",
            "集合族の要素から和への所属により次の関係が得られます: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "집합족 원소로 합집합 소속",
            "집합족 원소로 합집합 소속에 따라 다음 관계를 얻습니다: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc hợp của họ từ phần tử",
            "Quy tắc «Thuộc hợp của họ từ phần tử» thiết lập quan hệ sau: `A $in F` ∧ `x $in A` ⇒ `x $in family_union(F)`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IndexUnionMembershipFromIndexBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Index Union Membership From Index",
            "`i $in I` and `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("由指标得指标并成员", "属于某指标纤维则属于指标并")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由索引得帶索引聯集成員",
            "由索引得帶索引聯集成員給出以下關係: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l'union indexée depuis l'indice",
            "La règle « Appartenance à l'union indexée depuis l'indice » établit la relation suivante: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность индексированному объединению из индекса",
            "Правило «Принадлежность индексированному объединению из индекса» устанавливает следующее соотношение: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a unión indexada desde índice",
            "La regla «Pertenencia a unión indexada desde índice» establece la siguiente relación: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لاتحاد مفهرس من فهرس",
            "تثبت قاعدة «انتماء لاتحاد مفهرس من فهرس» العلاقة التالية: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "添字から添字付きの和への所属",
            "添字から添字付きの和への所属により次の関係が得られます: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "인덱스로 인덱스 합집합 소속",
            "인덱스로 인덱스 합집합 소속에 따라 다음 관계를 얻습니다: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc hợp theo chỉ số từ chỉ số",
            "Quy tắc «Thuộc hợp theo chỉ số từ chỉ số» thiết lập quan hệ sau: `i $in I` ∧ `x $in A(i)` ⇒ `x $in index_union(I, X, A)`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IntervalMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Interval Membership",
            "`x $in R` plus the matching open/closed endpoint inequalities",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("区间成员", "由载体与端点界推出区间成员")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("區間成員", "`x $in R` 及對應開閉端點不等式")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à l'intervalle",
            "`x $in R` et les inégalités correspondantes aux extrémités ouvertes ou fermées",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность интервалу",
            "`x $in R` и соответствующие неравенства открытых или замкнутых границ",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a intervalo",
            "`x $in R` y desigualdades correspondientes de extremos abiertos o cerrados",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لفترة",
            "`x $in R` والمتباينات المقابلة للأطراف المفتوحة أو المغلقة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "区間への所属",
            "`x $in R` と対応する開端点または閉端点の不等式",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "구간 소속",
            "`x $in R`과 대응하는 열린 또는 닫힌 끝점 부등식",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc khoảng",
            "`x $in R` cùng các bất đẳng thức đầu mút mở hoặc đóng tương ứng",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl OneSideInfinityIntervalMembershipBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "One Side Infinity Interval Membership",
            "One-sided real ray membership from carrier and the finite endpoint bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("单侧无穷区间成员", "由载体与有限端点界推出射线成员")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單側無限區間成員", "由載體與有限端點界得單側實射線成員")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Appartenance à un intervalle non borné d'un côté",
            "Appartenance à une demi-droite réelle depuis l'ensemble porteur et la borne d'extrémité finie",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Принадлежность интервалу с одной бесконечной границей",
            "Принадлежность вещественному лучу по носителю и конечной границе",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Pertenencia a intervalo infinito por un lado",
            "Pertenencia a semirrecta real desde portador y cota del extremo finito",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انتماء لفترة غير محدودة من جانب واحد",
            "انتماء لشعاع حقيقي من المجموعة الحاملة وحد الطرف المنتهي",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "片側が無限の区間への所属",
            "台集合と有限端点の境界から片側実数半直線への所属を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한쪽 무한 구간 소속",
            "바탕 집합과 유한 끝점 경계로 실수 반직선 소속을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thuộc khoảng vô hạn một phía",
            "Thuộc tia thực một phía từ tập nền và cận đầu mút hữu hạn",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AddInNaturalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closure of natural numbers under addition",
            "The Closure of natural numbers under addition law gives: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "自然数加法封闭性",
            "自然数加法封闭性可写为：a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "自然數加法封閉性",
            "自然數加法封閉性可寫為：a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Stabilité des naturels par addition",
            "La propriété « Stabilité des naturels par addition » donne: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Замкнутость натуральных чисел относительно сложения",
            "Свойство «Замкнутость натуральных чисел относительно сложения» выражается равенством: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Clausura de los naturales bajo suma",
            "La propiedad «Clausura de los naturales bajo suma» se expresa como: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انغلاق الأعداد الطبيعية تحت الجمع",
            "تُكتب خاصية «انغلاق الأعداد الطبيعية تحت الجمع» كما يلي: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "自然数の加法の閉性",
            "自然数の加法の閉性は次の式で表されます：a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "자연수 덧셈의 닫힘성",
            "자연수 덧셈의 닫힘성은 다음 식으로 나타납니다: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính đóng của số tự nhiên đối với phép cộng",
            "Tính chất «Tính đóng của số tự nhiên đối với phép cộng» được biểu diễn bởi: a ∈ N ∧ b ∈ N ⇒ a+b ∈ N",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl MulInNaturalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closure of natural numbers under multiplication",
            "The Closure of natural numbers under multiplication law gives: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "自然数乘法封闭性",
            "自然数乘法封闭性可写为：a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "自然數乘法封閉性",
            "自然數乘法封閉性可寫為：a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Stabilité des naturels par multiplication",
            "La propriété « Stabilité des naturels par multiplication » donne: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Замкнутость натуральных чисел относительно умножения",
            "Свойство «Замкнутость натуральных чисел относительно умножения» выражается равенством: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Clausura de los naturales bajo multiplicación",
            "La propiedad «Clausura de los naturales bajo multiplicación» se expresa como: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انغلاق الأعداد الطبيعية تحت الضرب",
            "تُكتب خاصية «انغلاق الأعداد الطبيعية تحت الضرب» كما يلي: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "自然数の乗法の閉性",
            "自然数の乗法の閉性は次の式で表されます：a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "자연수 곱셈의 닫힘성",
            "자연수 곱셈의 닫힘성은 다음 식으로 나타납니다: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính đóng của số tự nhiên đối với phép nhân",
            "Tính chất «Tính đóng của số tự nhiên đối với phép nhân» được biểu diễn bởi: a ∈ N ∧ b ∈ N ⇒ a·b ∈ N",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NativeScalarCodomainBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "Native Scalar Codomain".to_string(),
            message: format!(
                "after input-domain WD, the native result belongs to {} and its standard-set supertypes",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "原生标量返回类型".to_string(),
            message: format!(
                "参数定义域已通过良定检查，原生运算结果属于 {} 及其标准集合超集",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "原生純量陪域".to_string(),
            message: format!(
                "輸入定義域良定後，原生結果屬於 {} 及其標準集合超集",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "Codomaine scalaire natif".to_string(),
            message: format!(
                "Après bonne définition du domaine d'entrée, le résultat natif appartient à {} et à ses sur-ensembles standards",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "Встроенная скалярная область значений".to_string(),
            message: format!(
                "После корректности входной области встроенный результат принадлежит {} и его стандартным надмножествам",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "Codominio escalar nativo".to_string(),
            message: format!(
                "Tras buena definición del dominio de entrada, el resultado nativo pertenece a {} y a sus superconjuntos estándar",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "مجال مقابل قياسي أصلي".to_string(),
            message: format!(
                "بعد حسن تعريف مجال الإدخال تنتمي النتيجة الأصلية إلى {} ومجموعاتها القياسية الفوقية",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "組み込みスカラー終域".to_string(),
            message: format!(
                "入力定義域の検証後、組み込みの結果は {} とその標準上位集合に属します",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "내장 스칼라 공역".to_string(),
            message: format!(
                "입력 정의역 검증 후 내장 결과는 {}와 표준 상위집합에 속합니다",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: "Đối miền vô hướng tích hợp".to_string(),
            message: format!(
                "Sau kiểm tra xác định tốt của miền đầu vào, kết quả tích hợp thuộc {} và các tập cha chuẩn",
                self.codomain.ir().as_str(),
            ),
        }
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AnonymousFnInDeclaredFnSetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Anonymous function in declared function set",
            "the checked function's signature matches the target modulo bound-name renaming",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "匿名函数属于声明的函数集",
            "函数已通过良定检查，目标签名仅在绑定参数名称上不同",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "匿名函數屬於宣告函數集",
            "經檢查函數的簽章在繫結名稱改名後符合目標",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text("Fonction anonyme dans l'ensemble de fonctions déclaré", "La signature vérifiée de la fonction correspond à la cible après renommage des noms liés")
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Анонимная функция в объявленном множестве функций", "Проверенная сигнатура функции совпадает с целью с точностью до переименования связанных имён")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text("Función anónima en conjunto de funciones declarado", "La firma comprobada de función coincide con objetivo salvo renombrado de nombres ligados")
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "دالة مجهولة في مجموعة الدوال المعلنة",
            "توقيع الدالة المتحقق منه يطابق الهدف بعد إعادة تسمية الأسماء المرتبطة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "宣言された関数集合への無名関数の所属",
            "検査済みの関数の型は束縛名の変更を除いて目標と一致します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "선언된 함수 집합의 익명 함수",
            "검사된 함수의 시그니처는 바인딩 이름 변경을 제외하고 목표와 일치합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hàm ẩn danh trong tập hàm đã khai báo",
            "Chữ ký hàm đã kiểm tra khớp mục tiêu sau đổi tên biến ràng buộc",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PositiveIntegerInNPosBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        let (name, message) = (
            "Positive integer membership",
            "An integer strictly greater than zero belongs to N+",
        );
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        let (name, message) = ("正整数成员", "整数且严格大于零的对象属于 N+");
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        let (name, message) = ("正整數成員關係", "嚴格大於零的整數屬於 N+");
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        let (name, message) = (
            "Appartenance aux entiers positifs",
            "Un entier strictement positif appartient à N+",
        );
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        let (name, message) = (
            "Принадлежность положительным целым",
            "Целое строго больше нуля принадлежит N+",
        );
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        let (name, message) = (
            "Pertenencia a enteros positivos",
            "Un entero estrictamente mayor que cero pertenece a N+",
        );
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        let (name, message) = (
            "انتماء للأعداد الصحيحة الموجبة",
            "العدد الصحيح الأكبر تمامًا من صفر ينتمي إلى N+",
        );
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        let (name, message) = (
            "正の整数への所属",
            "ゼロより厳密に大きい整数は N+ に属します",
        );
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        let (name, message) = ("양의 정수 소속", "0보다 엄격히 큰 정수는 N+에 속합니다");
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        let (name, message) = ("Thuộc số nguyên dương", "Số nguyên dương thuộc N+");
        BuiltinRuleText {
            rule_name: name.into(),
            message: message.into(),
        }
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetMaxMemberBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Finite set maximum member",
            "A well-defined finite nonempty real set contains its maximum",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合最大值是成员",
            "良定的有限非空实数集合包含它的最大值",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合最大值是成員",
            "良定的有限非空實數集合包含它的最大值",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Maximum dans un ensemble fini",
            "Un ensemble réel fini non vide contient son maximum",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "максимум конечного множества",
            "Непустое конечное вещественное множество содержит свой максимум",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "máximo de conjunto finito",
            "Un conjunto real finito no vacío contiene su máximo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قيمتها العظمى مجموعة منتهية",
            "تحتوي المجموعة الحقيقية المنتهية غير الفارغة على قيمتها العظمى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の最大値は元",
            "有限非空実数集合はその最大値を含みます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한 집합의 최댓값 원소",
            "비어 있지 않은 유한 실수 집합은 그 최댓값을 포함합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị lớn nhất thuộc tập hữu hạn",
            "Tập số thực hữu hạn khác rỗng chứa Giá trị lớn nhất của nó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetMinMemberBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Finite set minimum member",
            "A well-defined finite nonempty real set contains its minimum",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合最小值是成员",
            "良定的有限非空实数集合包含它的最小值",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合最小值是成員",
            "良定的有限非空實數集合包含它的最小值",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Minimum dans un ensemble fini",
            "Un ensemble réel fini non vide contient son minimum",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "минимум конечного множества",
            "Непустое конечное вещественное множество содержит свой минимум",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "mínimo de conjunto finito",
            "Un conjunto real finito no vacío contiene su mínimo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قيمتها الصغرى مجموعة منتهية",
            "تحتوي المجموعة الحقيقية المنتهية غير الفارغة على قيمتها الصغرى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の最小値は元",
            "有限非空実数集合はその最小値を含みます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한 집합의 최솟값 원소",
            "비어 있지 않은 유한 실수 집합은 그 최솟값을 포함합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị nhỏ nhất thuộc tập hữu hạn",
            "Tập số thực hữu hạn khác rỗng chứa Giá trị nhỏ nhất của nó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}
