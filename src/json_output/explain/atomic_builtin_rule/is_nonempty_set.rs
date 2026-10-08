//! Leaf explain for atomic family group `is_nonempty_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::{
    IsNonemptySetFactSearchProofByBuiltinRule,
    LiteralListSetNonemptyBuiltinRuleProof,
    OneSideInfinityIntervalNonemptyBuiltinRuleProof,
    PowerSetNonemptyBuiltinRuleProof,
    StandardSetNonemptyBuiltinRuleProof,
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl IsNonemptySetFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_en(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_en(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_en(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_zh(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_zh(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_zh(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_zh_hant(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_zh_hant(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_zh_hant(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_fr(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_fr(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_fr(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_ru(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_ru(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_ru(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_es(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_es(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_es(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_ar(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_ar(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_ar(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_ja(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_ja(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_ja(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_ko(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_ko(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_ko(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_name_and_message_vi(),
            Self::LiteralListSetNonempty(p) => p.rule_name_and_message_vi(),
            Self::PowerSetNonempty(p) => p.rule_name_and_message_vi(),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_name_and_message_vi(),
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
            Self::StandardSetNonempty(_) => None,
            Self::LiteralListSetNonempty(_) => None,
            Self::PowerSetNonempty(_) => None,
            Self::OneSideInfinityIntervalNonempty(_) => None,
        }
    }
}

impl StandardSetNonemptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Standard Set Nonempty",
            "Verified by the standard Set Nonempty builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("标准集非空", "标准数集非空")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("標準集合非空", "由標準集合非空內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ensemble standard non vide",
            "Vérifié par la règle intégrée de non-vacuité d'ensemble standard",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Непустое стандартное множество",
            "Проверено встроенным правилом непустоты стандартного множества",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conjunto estándar no vacío",
            "Verificado por la regla incorporada de conjunto estándar no vacío",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموعة قياسية غير خالية",
            "تم التحقق بقاعدة عدم خلو المجموعة القياسية المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "標準集合が空でないこと",
            "標準集合が空でないことの組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "표준 집합이 비어 있지 않음",
            "표준 집합의 비어 있지 않음 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập chuẩn không rỗng",
            "Đã kiểm chứng bằng quy tắc tích hợp tập chuẩn không rỗng",
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

impl LiteralListSetNonemptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Literal List Set Nonempty",
            "Verified by the literal List Set Nonempty builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("字面列表集非空", "非空字面列表集非空")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("字面列表集合非空", "由字面列表集合非空內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ensemble liste littéral non vide",
            "Vérifié par la règle intégrée de non-vacuité d'ensemble liste littéral",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Непустое литеральное списочное множество",
            "Проверено встроенным правилом непустоты литерального списочного множества",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conjunto de lista literal no vacío",
            "Verificado por la regla incorporada de lista literal no vacía",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموعة قائمة حرفية غير خالية",
            "تم التحقق بقاعدة عدم خلو مجموعة القائمة الحرفية المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "リテラルのリスト集合が空でないこと",
            "リテラルのリスト集合が空でないことの組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "리터럴 목록 집합이 비어 있지 않음",
            "리터럴 목록 집합의 비어 있지 않음 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập danh sách literal không rỗng",
            "Đã kiểm chứng bằng quy tắc tích hợp tập danh sách literal không rỗng",
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

impl PowerSetNonemptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Power Set Nonempty",
            "Verified by the power Set Nonempty builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("幂集非空", "任意集合的幂集非空")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("冪集非空", "由冪集非空內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ensemble des parties non vide",
            "Vérifié par la règle intégrée de non-vacuité de l'ensemble des parties",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Непустое множество подмножеств",
            "Проверено встроенным правилом непустоты множества подмножеств",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conjunto potencia no vacío",
            "Verificado por la regla incorporada de conjunto potencia no vacío",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموعة قوى غير خالية",
            "تم التحقق بقاعدة عدم خلو مجموعة القوى المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "べき集合が空でないこと",
            "べき集合が空でないことの組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "멱집합이 비어 있지 않음",
            "멱집합의 비어 있지 않음 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập lũy thừa không rỗng",
            "Đã kiểm chứng bằng quy tắc tích hợp tập lũy thừa không rỗng",
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

impl OneSideInfinityIntervalNonemptyBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "One Side Infinity Interval Nonempty",
            "Verified by the one Side Infinity Interval Nonempty builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("单侧无穷区间非空", "单侧无穷实区间非空")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單側無限區間非空", "由單側無限區間非空內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intervalle non borné d'un côté non vide",
            "Vérifié par la règle intégrée de non-vacuité d'intervalle non borné d'un côté",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Непустой интервал с одной бесконечной границей",
            "Проверено встроенным правилом непустоты интервала с бесконечной границей",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intervalo infinito por un lado no vacío",
            "Verificado por la regla incorporada de intervalo infinito por un lado no vacío",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فترة غير محدودة من جانب واحد وغير خالية",
            "تم التحقق بقاعدة عدم خلو الفترة غير المحدودة من جانب واحد المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "片側が無限の区間が空でないこと",
            "片側が無限の区間が空でないことの組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "한쪽이 무한한 구간이 비어 있지 않음",
            "한쪽이 무한한 구간의 비어 있지 않음 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khoảng vô hạn một phía không rỗng",
            "Đã kiểm chứng bằng quy tắc tích hợp khoảng vô hạn một phía không rỗng",
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
