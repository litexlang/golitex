//! Leaf explain for atomic family group `is_nonempty_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::{
    IsNonemptySetFactSearchProofByBuiltinRule,
    LiteralListSetNonemptyBuiltinRuleProof,
    OneSideInfinityIntervalNonemptyBuiltinRuleProof,
    PowerSetNonemptyBuiltinRuleProof,
    StandardSetNonemptyBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsNonemptySetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_id_and_message(lang),
            Self::LiteralListSetNonempty(p) => p.rule_id_and_message(lang),
            Self::PowerSetNonempty(p) => p.rule_id_and_message(lang),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::StandardSetNonempty(_) => None,
            Self::LiteralListSetNonempty(_) => None,
            Self::PowerSetNonempty(_) => None,
            Self::OneSideInfinityIntervalNonempty(_) => None,
        }
    }
}

impl StandardSetNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetNonempty",
            "Standard Set Nonempty",
            "Verified by the standard Set Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("StandardSetNonempty", "标准集非空", "标准数集非空")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "StandardSetNonempty",
                "標準集合非空",
                "由標準集合非空內建規則驗證",
            ),
            OutputLanguage::French => text(
                "StandardSetNonempty",
                "Ensemble standard non vide",
                "Vérifié par la règle intégrée de non-vacuité d'ensemble standard",
            ),
            OutputLanguage::Russian => text(
                "StandardSetNonempty",
                "Непустое стандартное множество",
                "Проверено встроенным правилом непустоты стандартного множества",
            ),
            OutputLanguage::Spanish => text(
                "StandardSetNonempty",
                "Conjunto estándar no vacío",
                "Verificado por la regla incorporada de conjunto estándar no vacío",
            ),
            OutputLanguage::Arabic => text(
                "StandardSetNonempty",
                "مجموعة قياسية غير خالية",
                "تم التحقق بقاعدة عدم خلو المجموعة القياسية المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "StandardSetNonempty",
                "標準集合が空でないこと",
                "標準集合が空でないことの組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "StandardSetNonempty",
                "표준 집합이 비어 있지 않음",
                "표준 집합의 비어 있지 않음 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "StandardSetNonempty",
                "Tập chuẩn không rỗng",
                "Đã kiểm chứng bằng quy tắc tích hợp tập chuẩn không rỗng",
            ),
        }
    }
}

impl LiteralListSetNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LiteralListSetNonempty",
            "Literal List Set Nonempty",
            "Verified by the literal List Set Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LiteralListSetNonempty",
            "字面列表集非空",
            "非空字面列表集非空",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LiteralListSetNonempty",
                "字面列表集合非空",
                "由字面列表集合非空內建規則驗證",
            ),
            OutputLanguage::French => text(
                "LiteralListSetNonempty",
                "Ensemble liste littéral non vide",
                "Vérifié par la règle intégrée de non-vacuité d'ensemble liste littéral",
            ),
            OutputLanguage::Russian => text(
                "LiteralListSetNonempty",
                "Непустое литеральное списочное множество",
                "Проверено встроенным правилом непустоты литерального списочного множества",
            ),
            OutputLanguage::Spanish => text(
                "LiteralListSetNonempty",
                "Conjunto de lista literal no vacío",
                "Verificado por la regla incorporada de lista literal no vacía",
            ),
            OutputLanguage::Arabic => text(
                "LiteralListSetNonempty",
                "مجموعة قائمة حرفية غير خالية",
                "تم التحقق بقاعدة عدم خلو مجموعة القائمة الحرفية المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "LiteralListSetNonempty",
                "リテラルのリスト集合が空でないこと",
                "リテラルのリスト集合が空でないことの組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "LiteralListSetNonempty",
                "리터럴 목록 집합이 비어 있지 않음",
                "리터럴 목록 집합의 비어 있지 않음 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LiteralListSetNonempty",
                "Tập danh sách literal không rỗng",
                "Đã kiểm chứng bằng quy tắc tích hợp tập danh sách literal không rỗng",
            ),
        }
    }
}

impl PowerSetNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowerSetNonempty",
            "Power Set Nonempty",
            "Verified by the power Set Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowerSetNonempty", "幂集非空", "任意集合的幂集非空")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PowerSetNonempty", "冪集非空", "由冪集非空內建規則驗證")
            }
            OutputLanguage::French => text(
                "PowerSetNonempty",
                "Ensemble des parties non vide",
                "Vérifié par la règle intégrée de non-vacuité de l'ensemble des parties",
            ),
            OutputLanguage::Russian => text(
                "PowerSetNonempty",
                "Непустое множество подмножеств",
                "Проверено встроенным правилом непустоты множества подмножеств",
            ),
            OutputLanguage::Spanish => text(
                "PowerSetNonempty",
                "Conjunto potencia no vacío",
                "Verificado por la regla incorporada de conjunto potencia no vacío",
            ),
            OutputLanguage::Arabic => text(
                "PowerSetNonempty",
                "مجموعة قوى غير خالية",
                "تم التحقق بقاعدة عدم خلو مجموعة القوى المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "PowerSetNonempty",
                "べき集合が空でないこと",
                "べき集合が空でないことの組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "PowerSetNonempty",
                "멱집합이 비어 있지 않음",
                "멱집합의 비어 있지 않음 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PowerSetNonempty",
                "Tập lũy thừa không rỗng",
                "Đã kiểm chứng bằng quy tắc tích hợp tập lũy thừa không rỗng",
            ),
        }
    }
}

impl OneSideInfinityIntervalNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalNonempty",
            "One Side Infinity Interval Nonempty",
            "Verified by the one Side Infinity Interval Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalNonempty",
            "单侧无穷区间非空",
            "单侧无穷实区间非空",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "OneSideInfinityIntervalNonempty",
                "單側無限區間非空",
                "由單側無限區間非空內建規則驗證",
            ),
            OutputLanguage::French => text(
                "OneSideInfinityIntervalNonempty",
                "Intervalle non borné d'un côté non vide",
                "Vérifié par la règle intégrée de non-vacuité d'intervalle non borné d'un côté",
            ),
            OutputLanguage::Russian => text(
                "OneSideInfinityIntervalNonempty",
                "Непустой интервал с одной бесконечной границей",
                "Проверено встроенным правилом непустоты интервала с бесконечной границей",
            ),
            OutputLanguage::Spanish => text(
                "OneSideInfinityIntervalNonempty",
                "Intervalo infinito por un lado no vacío",
                "Verificado por la regla incorporada de intervalo infinito por un lado no vacío",
            ),
            OutputLanguage::Arabic => text(
                "OneSideInfinityIntervalNonempty",
                "فترة غير محدودة من جانب واحد وغير خالية",
                "تم التحقق بقاعدة عدم خلو الفترة غير المحدودة من جانب واحد المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "OneSideInfinityIntervalNonempty",
                "片側が無限の区間が空でないこと",
                "片側が無限の区間が空でないことの組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "OneSideInfinityIntervalNonempty",
                "한쪽이 무한한 구간이 비어 있지 않음",
                "한쪽이 무한한 구간의 비어 있지 않음 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "OneSideInfinityIntervalNonempty",
                "Khoảng vô hạn một phía không rỗng",
                "Đã kiểm chứng bằng quy tắc tích hợp khoảng vô hạn một phía không rỗng",
            ),
        }
    }
}
