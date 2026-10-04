//! Leaf explain for atomic family group `not_is_finite_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_finite_set::{
    NotIsFiniteSetFactSearchProofByBuiltinRule,
    SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof,
    StandardInfiniteSetBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotIsFiniteSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardInfiniteSet(p) => p.rule_id_and_message(lang),
            Self::SetMinusInfiniteOfInfiniteFinite(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::StandardInfiniteSet(_) => None,
            Self::SetMinusInfiniteOfInfiniteFinite(_) => None,
        }
    }
}

impl StandardInfiniteSetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardInfiniteSet",
            "Standard Infinite Set",
            "every standard number set (N, Z, Q, R, C, and signed/star variants)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("StandardInfiniteSet", "标准无穷集", "标准数集载体无穷")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "StandardInfiniteSet",
            "標準無限集合",
            "標準數集（N、Z、Q、R、C 及帶符號或星號的變體）均為無限",
        )
    },
            OutputLanguage::French => {
        text(
            "StandardInfiniteSet",
            "Ensemble infini standard",
            "Tout ensemble numérique standard (N, Z, Q, R, C et variantes signées ou étoilées) est infini",
        )
    },
            OutputLanguage::Russian => {
        text(
            "StandardInfiniteSet",
            "Стандартное бесконечное множество",
            "Любое стандартное числовое множество (N, Z, Q, R, C и варианты со знаками или звёздочкой) бесконечно",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "StandardInfiniteSet",
            "Conjunto infinito estándar",
            "Todo conjunto numérico estándar (N, Z, Q, R, C y variantes con signo o asterisco) es infinito",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "StandardInfiniteSet",
            "مجموعة قياسية غير منتهية",
            "كل مجموعة أعداد قياسية (N وZ وQ وR وC ومتغيراتها بالإشارة أو النجمة) غير منتهية",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "StandardInfiniteSet",
            "標準的な無限集合",
            "標準的な数集合（N、Z、Q、R、C および符号や星印付きの変種）は無限です",
        )
    },
            OutputLanguage::Korean => {
        text(
            "StandardInfiniteSet",
            "표준 무한 집합",
            "표준 수 집합(N, Z, Q, R, C 및 부호나 별표 변형)은 모두 무한합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "StandardInfiniteSet",
            "Tập vô hạn chuẩn",
            "Mọi tập số chuẩn (N, Z, Q, R, C và biến thể có dấu hoặc sao) đều vô hạn",
        )
    },

        }
    }
}

impl SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusInfiniteOfInfiniteFinite",
            "Set Minus Infinite Of Infinite Finite",
            "if `A` is infinite and `B` is finite, then `set_minus(A, B)` is infinite",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusInfiniteOfInfiniteFinite",
            "无穷减有限仍无穷",
            "无穷集减去有限集仍无穷",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "無限集合減有限集合仍無限",
                "`A` 無限且 `B` 有限時，`set_minus(A, B)` 無限",
            ),
            OutputLanguage::French => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "Différence d'un ensemble infini et d'un ensemble fini",
                "Si `A` est infini et `B` fini, alors `set_minus(A, B)` est infini",
            ),
            OutputLanguage::Russian => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "Разность бесконечного и конечного множества",
                "Если `A` бесконечно, а `B` конечно, то `set_minus(A, B)` бесконечно",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "Diferencia de conjunto infinito y finito",
                "Si `A` es infinito y `B` finito, `set_minus(A, B)` es infinito",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "فرق مجموعة غير منتهية ومجموعة منتهية",
                "إذا كانت `A` غير منتهية و`B` منتهية فإن `set_minus(A, B)` غير منتهية",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "無限集合と有限集合の差",
                "`A` が無限、`B` が有限なら `set_minus(A, B)` は無限です",
            ),
            OutputLanguage::Korean => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "무한 집합과 유한 집합의 차",
                "`A`가 무한하고 `B`가 유한하면 `set_minus(A, B)`는 무한합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusInfiniteOfInfiniteFinite",
                "Hiệu tập vô hạn và tập hữu hạn",
                "Nếu `A` vô hạn và `B` hữu hạn thì `set_minus(A, B)` vô hạn",
            ),
        }
    }
}
