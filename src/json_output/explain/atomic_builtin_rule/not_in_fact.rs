//! Leaf explain for atomic family group `not_in_fact`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::{
    ClosedNumericNonMembershipBuiltinRuleProof,
    ListSetExhaustiveDisequalityBuiltinRuleProof,
    NonMembershipOfIntersectFromLeftBuiltinRuleProof,
    NonMembershipOfIntersectFromRightBuiltinRuleProof,
    NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof,
    NonMembershipOfIntervalOutsideBuiltinRuleProof,
    NonMembershipOfSetMinusFromLeftBuiltinRuleProof,
    NonMembershipOfSetMinusFromRightBuiltinRuleProof,
    NonMembershipOfUnionBuiltinRuleProof,
    NotInFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotInFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_en(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_en(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_en(),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_zh(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_zh(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_zh(),
        }
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_zh_hant(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_zh_hant(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_zh_hant(),
        }
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_fr(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_fr(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_fr(),
        }
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_ru(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_ru(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_ru(),
        }
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_es(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_es(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_es(),
        }
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_ar(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_ar(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_ar(),
        }
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_ja(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_ja(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_ja(),
        }
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_ko(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_ko(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_ko(),
        }
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message_vi(),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message_vi(),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message_vi(),
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ClosedNumericNonMembership(_) => None,
            Self::ListSetExhaustiveDisequality(_) => None,
            Self::NonMembershipOfIntersectFromLeft(_) => None,
            Self::NonMembershipOfIntersectFromRight(_) => None,
            Self::NonMembershipOfUnion(_) => None,
            Self::NonMembershipOfSetMinusFromRight(_) => None,
            Self::NonMembershipOfSetMinusFromLeft(_) => None,
            Self::NonMembershipOfIntervalAtOpenEndpoint(_) => None,
            Self::NonMembershipOfIntervalOutside(_) => None,
        }
    }
}

impl ClosedNumericNonMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "Nonmembership by evaluating a closed expression",
            "The evaluated value of the closed expression does not belong to the target set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "闭式求值确认非成员关系",
            "闭式的求值结果不属于目标集合",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "閉式求值確認非成員關係",
            "閉式的求值結果不屬於目標集合",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "Non-appartenance par évaluation d’une expression fermée",
            "La valeur évaluée de l’expression fermée n’appartient pas à l’ensemble cible",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "Непринадлежность по вычислению замкнутого выражения",
            "Вычисленное значение замкнутого выражения не принадлежит целевому множеству",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "No pertenencia por evaluación de una expresión cerrada",
            "El valor evaluado de la expresión cerrada no pertenece al conjunto objetivo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "عدم الانتماء بتقييم تعبير مغلق",
            "القيمة المحسوبة للتعبير المغلق لا تنتمي إلى المجموعة المستهدفة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "閉じた式の評価による非所属",
            "閉じた式の評価値は対象集合に属しません",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "닫힌 식 평가에 따른 비소속",
            "닫힌 식의 평가값이 대상 집합에 속하지 않습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "Quan hệ không thuộc bằng tính biểu thức đóng",
            "Giá trị tính được của biểu thức đóng không thuộc tập đích",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ListSetExhaustiveDisequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "List Set Exhaustive Disequality",
            "An element unequal to every explicitly listed member does not belong to that set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "列表集穷举不等",
            "与每个列出元素都不等则不属于列表集",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "列表集合窮舉不等",
            "與每個列出元素 `a_i` 都不等，則不屬於 `{a_1, …, a_n}`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "Inégalité exhaustive d'ensemble liste",
            "Si `x != a_i` pour chaque élément listé, x n'appartient pas à `{a_1, …, a_n}`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "Полный перебор неравенств списочного множества",
            "Если `x != a_i` для каждого указанного элемента, x не принадлежит `{a_1, …, a_n}`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "Desigualdad exhaustiva de conjunto de lista",
            "Si `x != a_i` para cada elemento listado, x no pertenece a `{a_1, …, a_n}`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "عدم مساواة شامل لمجموعة قائمة",
            "إذا كانت `x != a_i` لكل عنصر مدرج فإن x لا تنتمي إلى `{a_1, …, a_n}`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "リスト集合の全要素との不等性",
            "すべての列挙要素について `x != a_i` なら x は `{a_1, …, a_n}` に属しません",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "목록 집합의 모든 원소와의 불일치",
            "열거된 모든 원소에 대해 `x != a_i`이면 x는 `{a_1, …, a_n}`에 속하지 않습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "Bất đẳng thức vét cạn của tập danh sách",
            "Nếu `x != a_i` với mọi phần tử liệt kê thì x không thuộc `{a_1, …, a_n}`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfIntersectFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "Non Membership Of Intersect From Left",
            "The Non Membership Of Intersect From Left rule establishes the following relation: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "由左非成员得交非成员",
            "不属于左因子则不属于交",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "由左非成員得交集非成員",
            "由左非成員得交集非成員給出以下關係: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "Non-appartenance à l'intersection depuis la gauche",
            "La règle « Non-appartenance à l'intersection depuis la gauche » établit la relation suivante: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "Непринадлежность пересечению из левого множества",
            "Правило «Непринадлежность пересечению из левого множества» устанавливает следующее соотношение: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "No pertenencia a intersección desde la izquierda",
            "La regla «No pertenencia a intersección desde la izquierda» establece la siguiente relación: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "عدم الانتماء للتقاطع من اليسار",
            "تثبت قاعدة «عدم الانتماء للتقاطع من اليسار» العلاقة التالية: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "左側の非所属から交差への非所属",
            "左側の非所属から交差への非所属により次の関係が得られます: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "왼쪽 비소속으로 교집합 비소속",
            "왼쪽 비소속으로 교집합 비소속에 따라 다음 관계를 얻습니다: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "Không thuộc giao từ vế trái",
            "Quy tắc «Không thuộc giao từ vế trái» thiết lập quan hệ sau: `not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfIntersectFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "Non Membership Of Intersect From Right",
            "The Non Membership Of Intersect From Right rule establishes the following relation: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "由右非成员得交非成员",
            "不属于右因子则不属于交",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "由右非成員得交集非成員",
            "由右非成員得交集非成員給出以下關係: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "Non-appartenance à l'intersection depuis la droite",
            "La règle « Non-appartenance à l'intersection depuis la droite » établit la relation suivante: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "Непринадлежность пересечению из правого множества",
            "Правило «Непринадлежность пересечению из правого множества» устанавливает следующее соотношение: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "No pertenencia a intersección desde la derecha",
            "La regla «No pertenencia a intersección desde la derecha» establece la siguiente relación: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "عدم الانتماء للتقاطع من اليمين",
            "تثبت قاعدة «عدم الانتماء للتقاطع من اليمين» العلاقة التالية: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "右側の非所属から交差への非所属",
            "右側の非所属から交差への非所属により次の関係が得られます: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "오른쪽 비소속으로 교집합 비소속",
            "오른쪽 비소속으로 교집합 비소속에 따라 다음 관계를 얻습니다: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "Không thuộc giao từ vế phải",
            "Quy tắc «Không thuộc giao từ vế phải» thiết lập quan hệ sau: `not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "Non Membership Of Union",
            "An element absent from both sets is absent from their union",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "两边非成员得并非成员",
            "两边都不属于则不属于并",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "兩邊非成員得聯集非成員",
            "`not x $in A` 與 `not x $in B` 推出 `not x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "Non-appartenance à l'union",
            "`not x $in A` et `not x $in B` impliquent `not x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "Непринадлежность объединению",
            "`not x $in A` и `not x $in B` влекут `not x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "No pertenencia a unión",
            "`not x $in A` y `not x $in B` implican `not x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "عدم الانتماء للاتحاد",
            "`not x $in A` و`not x $in B` تستلزمان `not x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "和集合への非所属",
            "`not x $in A` と `not x $in B` から `not x $in union(A, B)` を導きます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "합집합 비소속",
            "`not x $in A`와 `not x $in B`로 `not x $in union(A, B)`를 도출합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "Không thuộc hợp",
            "`not x $in A` và `not x $in B` suy ra `not x $in union(A, B)`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfSetMinusFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "Non Membership Of Set Minus From Right",
            "The Non Membership Of Set Minus From Right rule establishes the following relation: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "由右成员得差集非成员",
            "属于右因子则不属于差集",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "由右成員得差集非成員",
            "由右成員得差集非成員給出以下關係: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "Non-appartenance à la différence depuis la droite",
            "La règle « Non-appartenance à la différence depuis la droite » établit la relation suivante: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "Непринадлежность разности из правого множества",
            "Правило «Непринадлежность разности из правого множества» устанавливает следующее соотношение: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "No pertenencia a diferencia desde la derecha",
            "La regla «No pertenencia a diferencia desde la derecha» establece la siguiente relación: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "عدم الانتماء للفرق من اليمين",
            "تثبت قاعدة «عدم الانتماء للفرق من اليمين» العلاقة التالية: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "右側の所属から差集合への非所属",
            "右側の所属から差集合への非所属により次の関係が得られます: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "오른쪽 소속으로 차집합 비소속",
            "오른쪽 소속으로 차집합 비소속에 따라 다음 관계를 얻습니다: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "Không thuộc hiệu từ vế phải",
            "Quy tắc «Không thuộc hiệu từ vế phải» thiết lập quan hệ sau: `x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfSetMinusFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "Non Membership Of Set Minus From Left",
            "The Non Membership Of Set Minus From Left rule establishes the following relation: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "由左非成员得差集非成员",
            "不属于左因子则不属于差集",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "由左非成員得差集非成員",
            "由左非成員得差集非成員給出以下關係: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "Non-appartenance à la différence depuis la gauche",
            "La règle « Non-appartenance à la différence depuis la gauche » établit la relation suivante: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "Непринадлежность разности из левого множества",
            "Правило «Непринадлежность разности из левого множества» устанавливает следующее соотношение: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "No pertenencia a diferencia desde la izquierda",
            "La regla «No pertenencia a diferencia desde la izquierda» establece la siguiente relación: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "عدم الانتماء للفرق من اليسار",
            "تثبت قاعدة «عدم الانتماء للفرق من اليسار» العلاقة التالية: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "左側の非所属から差集合への非所属",
            "左側の非所属から差集合への非所属により次の関係が得られます: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "왼쪽 비소속으로 차집합 비소속",
            "왼쪽 비소속으로 차집합 비소속에 따라 다음 관계를 얻습니다: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "Không thuộc hiệu từ vế trái",
            "Quy tắc «Không thuộc hiệu từ vế trái» thiết lập quan hệ sau: `not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "Non Membership Of Interval At Open Endpoint",
            "An open endpoint is excluded from its interval",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "开端点非成员",
            "开端点处不属于区间",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "開端點非成員",
            "開端點處不屬於區間",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "Non-appartenance à l'extrémité ouverte",
            "Une extrémité ouverte n'appartient pas à l'intervalle",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "Непринадлежность на открытой границе интервала",
            "Открытая граница не принадлежит интервалу",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "No pertenencia en extremo abierto",
            "Un extremo abierto no pertenece al intervalo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "عدم الانتماء عند طرف مفتوح",
            "الطرف المفتوح لا ينتمي إلى الفترة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "開いた端点での非所属",
            "開いた端点は区間に属しません",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "열린 끝점에서의 비소속",
            "열린 끝점은 구간에 속하지 않습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "Không thuộc khoảng tại đầu mút mở",
            "Đầu mút mở không thuộc khoảng",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NonMembershipOfIntervalOutsideBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "Non Membership Of Interval Outside",
            "A real number strictly outside the interval endpoints does not belong to the interval",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "区间外非成员",
            "落在区间外则不属于",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "區間外非成員",
            "`x < a` 或 `b < x` 表示在區間外；閉端點以嚴格序否定 `<=`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "Non-appartenance hors intervalle",
            "`x < a` ou `b < x` place x hors intervalle ; aux extrémités fermées, l'ordre strict nie `<=`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "Непринадлежность вне интервала",
            "`x < a` или `b < x` означает положение вне интервала; на замкнутых границах строгий порядок отрицает `<=`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "No pertenencia fuera del intervalo",
            "`x < a` o `b < x` sitúa x fuera del intervalo; en extremos cerrados, el orden estricto niega `<=`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "عدم الانتماء خارج الفترة",
            "`x < a` أو `b < x` يعني خارج الفترة؛ عند الأطراف المغلقة ينفي الترتيب الصارم `<=`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "区間外での非所属",
            "`x < a` または `b < x` なら区間外です。閉端点では狭義順序で `<=` を否定します",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "구간 밖에서의 비소속",
            "`x < a` 또는 `b < x`이면 구간 밖입니다. 닫힌 끝점에서는 엄격한 순서로 `<=`를 부정합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "Không thuộc khoảng khi ở ngoài",
            "`x < a` hoặc `b < x` nghĩa là ngoài khoảng; tại đầu mút đóng, thứ tự nghiêm ngặt phủ định `<=`",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}
