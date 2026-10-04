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
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericNonMembership(p) => p.rule_id_and_message(lang),
            Self::ListSetExhaustiveDisequality(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntersectFromLeft(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntersectFromRight(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfUnion(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfSetMinusFromRight(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfSetMinusFromLeft(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntervalAtOpenEndpoint(p) => p.rule_id_and_message(lang),
            Self::NonMembershipOfIntervalOutside(p) => p.rule_id_and_message(lang),
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
            "Closed Numeric Non Membership",
            "a closed expression that evaluates to a normalized",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericNonMembership",
            "封闭数值非成员",
            "封闭表达式算出的值不属于目标集合",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedNumericNonMembership",
                "封閉數值非成員",
                "封閉運算式求出的值不屬於目標集合",
            ),
            OutputLanguage::French => text(
                "ClosedNumericNonMembership",
                "Non-appartenance numérique fermée",
                "La valeur évaluée d'une expression fermée n'appartient pas à l'ensemble cible",
            ),
            OutputLanguage::Russian => text(
                "ClosedNumericNonMembership",
                "Непринадлежность замкнутого числового выражения",
                "Вычисленное значение замкнутого выражения не принадлежит целевому множеству",
            ),
            OutputLanguage::Spanish => text(
                "ClosedNumericNonMembership",
                "No pertenencia numérica cerrada",
                "El valor evaluado de una expresión cerrada no pertenece al conjunto objetivo",
            ),
            OutputLanguage::Arabic => text(
                "ClosedNumericNonMembership",
                "عدم انتماء عددي مغلق",
                "قيمة التعبير المغلق المحسوبة لا تنتمي إلى المجموعة الهدف",
            ),
            OutputLanguage::Japanese => text(
                "ClosedNumericNonMembership",
                "閉じた数値式の非所属",
                "閉じた式の評価値は対象集合に属しません",
            ),
            OutputLanguage::Korean => text(
                "ClosedNumericNonMembership",
                "닫힌 수치 식의 비소속",
                "닫힌 식의 평가값이 대상 집합에 속하지 않습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedNumericNonMembership",
                "Không thuộc về của biểu thức số đóng",
                "Giá trị tính được của biểu thức đóng không thuộc tập mục tiêu",
            ),
        }
    }
}

impl ListSetExhaustiveDisequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "List Set Exhaustive Disequality",
            "if `x != a_i` for every `a_i` in `{a_1, …, a_n}`,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetExhaustiveDisequality",
            "列表集穷举不等",
            "与每个列出元素都不等则不属于列表集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ListSetExhaustiveDisequality",
                "列表集合窮舉不等",
                "與每個列出元素 `a_i` 都不等，則不屬於 `{a_1, …, a_n}`",
            ),
            OutputLanguage::French => text(
                "ListSetExhaustiveDisequality",
                "Inégalité exhaustive d'ensemble liste",
                "Si `x != a_i` pour chaque élément listé, x n'appartient pas à `{a_1, …, a_n}`",
            ),
            OutputLanguage::Russian => text(
                "ListSetExhaustiveDisequality",
                "Полный перебор неравенств списочного множества",
                "Если `x != a_i` для каждого указанного элемента, x не принадлежит `{a_1, …, a_n}`",
            ),
            OutputLanguage::Spanish => text(
                "ListSetExhaustiveDisequality",
                "Desigualdad exhaustiva de conjunto de lista",
                "Si `x != a_i` para cada elemento listado, x no pertenece a `{a_1, …, a_n}`",
            ),
            OutputLanguage::Arabic => text(
                "ListSetExhaustiveDisequality",
                "عدم مساواة شامل لمجموعة قائمة",
                "إذا كانت `x != a_i` لكل عنصر مدرج فإن x لا تنتمي إلى `{a_1, …, a_n}`",
            ),
            OutputLanguage::Japanese => text(
                "ListSetExhaustiveDisequality",
                "リスト集合の全要素との不等性",
                "すべての列挙要素について `x != a_i` なら x は `{a_1, …, a_n}` に属しません",
            ),
            OutputLanguage::Korean => text(
                "ListSetExhaustiveDisequality",
                "목록 집합의 모든 원소와의 불일치",
                "열거된 모든 원소에 대해 `x != a_i`이면 x는 `{a_1, …, a_n}`에 속하지 않습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ListSetExhaustiveDisequality",
                "Bất đẳng thức vét cạn của tập danh sách",
                "Nếu `x != a_i` với mọi phần tử liệt kê thì x không thuộc `{a_1, …, a_n}`",
            ),
        }
    }
}

impl NonMembershipOfIntersectFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "Non Membership Of Intersect From Left",
            "`not x $in A` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromLeft",
            "由左非成员得交非成员",
            "不属于左因子则不属于交",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonMembershipOfIntersectFromLeft",
                "由左非成員得交集非成員",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::French => text(
                "NonMembershipOfIntersectFromLeft",
                "Non-appartenance à l'intersection depuis la gauche",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "NonMembershipOfIntersectFromLeft",
                "Непринадлежность пересечению из левого множества",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "NonMembershipOfIntersectFromLeft",
                "No pertenencia a intersección desde la izquierda",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "NonMembershipOfIntersectFromLeft",
                "عدم الانتماء للتقاطع من اليسار",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "NonMembershipOfIntersectFromLeft",
                "左側の非所属から交差への非所属",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "NonMembershipOfIntersectFromLeft",
                "왼쪽 비소속으로 교집합 비소속",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "NonMembershipOfIntersectFromLeft",
                "Không thuộc giao từ vế trái",
                "`not x $in A` ⇒ `not x $in intersect(A, B)`",
            ),
        }
    }
}

impl NonMembershipOfIntersectFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "Non Membership Of Intersect From Right",
            "`not x $in B` ⇒ `not x $in intersect(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntersectFromRight",
            "由右非成员得交非成员",
            "不属于右因子则不属于交",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonMembershipOfIntersectFromRight",
                "由右非成員得交集非成員",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::French => text(
                "NonMembershipOfIntersectFromRight",
                "Non-appartenance à l'intersection depuis la droite",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "NonMembershipOfIntersectFromRight",
                "Непринадлежность пересечению из правого множества",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "NonMembershipOfIntersectFromRight",
                "No pertenencia a intersección desde la derecha",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "NonMembershipOfIntersectFromRight",
                "عدم الانتماء للتقاطع من اليمين",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "NonMembershipOfIntersectFromRight",
                "右側の非所属から交差への非所属",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "NonMembershipOfIntersectFromRight",
                "오른쪽 비소속으로 교집합 비소속",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "NonMembershipOfIntersectFromRight",
                "Không thuộc giao từ vế phải",
                "`not x $in B` ⇒ `not x $in intersect(A, B)`",
            ),
        }
    }
}

impl NonMembershipOfUnionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "Non Membership Of Union",
            "`not x $in A` and `not x $in B` ⇒",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfUnion",
            "两边非成员得并非成员",
            "两边都不属于则不属于并",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonMembershipOfUnion",
                "兩邊非成員得聯集非成員",
                "`not x $in A` 與 `not x $in B` 推出 `not x $in union(A, B)`",
            ),
            OutputLanguage::French => text(
                "NonMembershipOfUnion",
                "Non-appartenance à l'union",
                "`not x $in A` et `not x $in B` impliquent `not x $in union(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "NonMembershipOfUnion",
                "Непринадлежность объединению",
                "`not x $in A` и `not x $in B` влекут `not x $in union(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "NonMembershipOfUnion",
                "No pertenencia a unión",
                "`not x $in A` y `not x $in B` implican `not x $in union(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "NonMembershipOfUnion",
                "عدم الانتماء للاتحاد",
                "`not x $in A` و`not x $in B` تستلزمان `not x $in union(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "NonMembershipOfUnion",
                "和集合への非所属",
                "`not x $in A` と `not x $in B` から `not x $in union(A, B)` を導きます",
            ),
            OutputLanguage::Korean => text(
                "NonMembershipOfUnion",
                "합집합 비소속",
                "`not x $in A`와 `not x $in B`로 `not x $in union(A, B)`를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NonMembershipOfUnion",
                "Không thuộc hợp",
                "`not x $in A` và `not x $in B` suy ra `not x $in union(A, B)`",
            ),
        }
    }
}

impl NonMembershipOfSetMinusFromRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "Non Membership Of Set Minus From Right",
            "`x $in B` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromRight",
            "由右成员得差集非成员",
            "属于右因子则不属于差集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonMembershipOfSetMinusFromRight",
                "由右成員得差集非成員",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::French => text(
                "NonMembershipOfSetMinusFromRight",
                "Non-appartenance à la différence depuis la droite",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "NonMembershipOfSetMinusFromRight",
                "Непринадлежность разности из правого множества",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "NonMembershipOfSetMinusFromRight",
                "No pertenencia a diferencia desde la derecha",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "NonMembershipOfSetMinusFromRight",
                "عدم الانتماء للفرق من اليمين",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "NonMembershipOfSetMinusFromRight",
                "右側の所属から差集合への非所属",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "NonMembershipOfSetMinusFromRight",
                "오른쪽 소속으로 차집합 비소속",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "NonMembershipOfSetMinusFromRight",
                "Không thuộc hiệu từ vế phải",
                "`x $in B` ⇒ `not x $in set_minus(A, B)`",
            ),
        }
    }
}

impl NonMembershipOfSetMinusFromLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "Non Membership Of Set Minus From Left",
            "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfSetMinusFromLeft",
            "由左非成员得差集非成员",
            "不属于左因子则不属于差集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonMembershipOfSetMinusFromLeft",
                "由左非成員得差集非成員",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::French => text(
                "NonMembershipOfSetMinusFromLeft",
                "Non-appartenance à la différence depuis la gauche",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "NonMembershipOfSetMinusFromLeft",
                "Непринадлежность разности из левого множества",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "NonMembershipOfSetMinusFromLeft",
                "No pertenencia a diferencia desde la izquierda",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "NonMembershipOfSetMinusFromLeft",
                "عدم الانتماء للفرق من اليسار",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "NonMembershipOfSetMinusFromLeft",
                "左側の非所属から差集合への非所属",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "NonMembershipOfSetMinusFromLeft",
                "왼쪽 비소속으로 차집합 비소속",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "NonMembershipOfSetMinusFromLeft",
                "Không thuộc hiệu từ vế trái",
                "`not x $in A` ⇒ `not x $in set_minus(A, B)`",
            ),
        }
    }
}

impl NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "Non Membership Of Interval At Open Endpoint",
            "if the left (resp. right) end is open and `x = a`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalAtOpenEndpoint",
            "开端点非成员",
            "开端点处不属于区间",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "開端點非成員",
                "開端點處不屬於區間",
            ),
            OutputLanguage::French => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "Non-appartenance à l'extrémité ouverte",
                "Une extrémité ouverte n'appartient pas à l'intervalle",
            ),
            OutputLanguage::Russian => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "Непринадлежность на открытой границе интервала",
                "Открытая граница не принадлежит интервалу",
            ),
            OutputLanguage::Spanish => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "No pertenencia en extremo abierto",
                "Un extremo abierto no pertenece al intervalo",
            ),
            OutputLanguage::Arabic => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "عدم الانتماء عند طرف مفتوح",
                "الطرف المفتوح لا ينتمي إلى الفترة",
            ),
            OutputLanguage::Japanese => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "開いた端点での非所属",
                "開いた端点は区間に属しません",
            ),
            OutputLanguage::Korean => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "열린 끝점에서의 비소속",
                "열린 끝점은 구간에 속하지 않습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NonMembershipOfIntervalAtOpenEndpoint",
                "Không thuộc khoảng tại đầu mút mở",
                "Đầu mút mở không thuộc khoảng",
            ),
        }
    }
}

impl NonMembershipOfIntervalOutsideBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "Non Membership Of Interval Outside",
            "`x < a` or `b < x` (with closed ends using `<=` denial via strict)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonMembershipOfIntervalOutside",
            "区间外非成员",
            "落在区间外则不属于",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "NonMembershipOfIntervalOutside",
            "區間外非成員",
            "`x < a` 或 `b < x` 表示在區間外；閉端點以嚴格序否定 `<=`",
        )
    },
            OutputLanguage::French => {
        text(
            "NonMembershipOfIntervalOutside",
            "Non-appartenance hors intervalle",
            "`x < a` ou `b < x` place x hors intervalle ; aux extrémités fermées, l'ordre strict nie `<=`",
        )
    },
            OutputLanguage::Russian => {
        text(
            "NonMembershipOfIntervalOutside",
            "Непринадлежность вне интервала",
            "`x < a` или `b < x` означает положение вне интервала; на замкнутых границах строгий порядок отрицает `<=`",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "NonMembershipOfIntervalOutside",
            "No pertenencia fuera del intervalo",
            "`x < a` o `b < x` sitúa x fuera del intervalo; en extremos cerrados, el orden estricto niega `<=`",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "NonMembershipOfIntervalOutside",
            "عدم الانتماء خارج الفترة",
            "`x < a` أو `b < x` يعني خارج الفترة؛ عند الأطراف المغلقة ينفي الترتيب الصارم `<=`",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "NonMembershipOfIntervalOutside",
            "区間外での非所属",
            "`x < a` または `b < x` なら区間外です。閉端点では狭義順序で `<=` を否定します",
        )
    },
            OutputLanguage::Korean => {
        text(
            "NonMembershipOfIntervalOutside",
            "구간 밖에서의 비소속",
            "`x < a` 또는 `b < x`이면 구간 밖입니다. 닫힌 끝점에서는 엄격한 순서로 `<=`를 부정합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "NonMembershipOfIntervalOutside",
            "Không thuộc khoảng khi ở ngoài",
            "`x < a` hoặc `b < x` nghĩa là ngoài khoảng; tại đầu mút đóng, thứ tự nghiêm ngặt phủ định `<=`",
        )
    },

        }
    }
}
