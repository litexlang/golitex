//! Leaf explain for atomic family group `is_finite_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_finite_set::{
    ClosedRangeFiniteBuiltinRuleProof,
    FiniteSeqFromFiniteCodomainBuiltinRuleProof,
    FiniteSeqZeroLengthFiniteBuiltinRuleProof,
    IsFiniteSetFactSearchProofByBuiltinRule,
    ListSetFiniteBuiltinRuleProof,
    RangeFiniteBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsFiniteSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => match lang {
                OutputLanguage::English => text(
                    "FunctionRangeOfFiniteDomain",
                    "Finite function range",
                    "The range of a checked function with finite domain is finite",
                ),
                OutputLanguage::ChineseTraditional => text(
                    "FunctionRangeOfFiniteDomain",
                    "有限函數值域",
                    "經驗證的有限定義域函數之值域有限",
                ),
                OutputLanguage::French => text(
                    "FunctionRangeOfFiniteDomain",
                    "Image finie d'une fonction",
                    "L'image d'une fonction vérifiée à domaine fini est finie",
                ),
                OutputLanguage::Russian => text(
                    "FunctionRangeOfFiniteDomain",
                    "Конечная область значений функции",
                    "Область значений проверенной функции с конечной областью определения конечна",
                ),
                OutputLanguage::Spanish => text(
                    "FunctionRangeOfFiniteDomain",
                    "Rango finito de función",
                    "El rango de una función comprobada con dominio finito es finito",
                ),
                OutputLanguage::Arabic => text(
                    "FunctionRangeOfFiniteDomain",
                    "مدى دالة منتهٍ",
                    "مدى الدالة المتحقق منها ذات المجال المنتهي منتهٍ",
                ),
                OutputLanguage::Japanese => text(
                    "FunctionRangeOfFiniteDomain",
                    "有限な関数の値域",
                    "有限な定義域を持つ検証済み関数の値域は有限です",
                ),
                OutputLanguage::Korean => text(
                    "FunctionRangeOfFiniteDomain",
                    "유한한 함수 치역",
                    "유한 정의역을 가진 검증된 함수의 치역은 유한합니다",
                ),
                OutputLanguage::Vietnamese => text(
                    "FunctionRangeOfFiniteDomain",
                    "Miền giá trị hàm hữu hạn",
                    "Miền giá trị của hàm đã kiểm tra có miền xác định hữu hạn là hữu hạn",
                ),

                OutputLanguage::Chinese => text(
                    "FunctionRangeOfFiniteDomain",
                    "有限函数像",
                    "已验证函数在有限定义域上的像是有限集",
                ),
            },
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "Finite surjective image",
                "A surjection from a checked finite domain has finite codomain",
            ),
            Self::ListSet(p) => p.rule_id_and_message(lang),
            Self::ClosedRange(p) => p.rule_id_and_message(lang),
            Self::Range(p) => p.rule_id_and_message(lang),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message(lang),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => None,
            Self::SurjectiveImageOfFiniteSet(p) => Some(p.cite_surjective_fact_id),
            Self::ListSet(_) => None,
            Self::ClosedRange(_) => None,
            Self::Range(_) => None,
            Self::FiniteSeqZeroLength(_) => None,
            Self::FiniteSeqFromFiniteCodomain(_) => None,
        }
    }
}

impl ListSetFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "List Set",
            "Verified by the list Set builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ListSet", "列表集有限", "有限列表集是有限集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ListSet", "列表集合", "由列表集合內建規則驗證")
            }
            OutputLanguage::French => text(
                "ListSet",
                "Ensemble liste",
                "Vérifié par la règle intégrée d'ensemble liste",
            ),
            OutputLanguage::Russian => text(
                "ListSet",
                "Списочное множество",
                "Проверено встроенным правилом списочного множества",
            ),
            OutputLanguage::Spanish => text(
                "ListSet",
                "Conjunto de lista",
                "Verificado por la regla incorporada de conjunto de lista",
            ),
            OutputLanguage::Arabic => text(
                "ListSet",
                "مجموعة قائمة",
                "تم التحقق بقاعدة مجموعة القائمة المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "ListSet",
                "リスト集合",
                "リスト集合の組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "ListSet",
                "목록 집합",
                "목록 집합 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ListSet",
                "Tập danh sách",
                "Đã kiểm chứng bằng quy tắc tích hợp tập danh sách",
            ),
        }
    }
}

impl ClosedRangeFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Closed Range",
            "Verified by the closed Range builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ClosedRange", "闭区间有限", "整数闭区间是有限集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ClosedRange", "封閉區間", "由封閉區間內建規則驗證")
            }
            OutputLanguage::French => text(
                "ClosedRange",
                "Intervalle fermé",
                "Vérifié par la règle intégrée d'intervalle fermé",
            ),
            OutputLanguage::Russian => text(
                "ClosedRange",
                "Замкнутый интервал",
                "Проверено встроенным правилом замкнутого интервала",
            ),
            OutputLanguage::Spanish => text(
                "ClosedRange",
                "Intervalo cerrado",
                "Verificado por la regla incorporada de intervalo cerrado",
            ),
            OutputLanguage::Arabic => text(
                "ClosedRange",
                "فترة مغلقة",
                "تم التحقق بقاعدة الفترة المغلقة المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "ClosedRange",
                "閉区間",
                "閉区間の組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "ClosedRange",
                "닫힌 구간",
                "닫힌 구간 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedRange",
                "Khoảng đóng",
                "Đã kiểm chứng bằng quy tắc tích hợp khoảng đóng",
            ),
        }
    }
}

impl RangeFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("Range", "Range", "Verified by the range builtin rule")
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("Range", "区间有限", "整数区间是有限集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("Range", "值域", "由值域內建規則驗證"),
            OutputLanguage::French => {
                text("Range", "Image", "Vérifié par la règle intégrée d'image")
            }
            OutputLanguage::Russian => text(
                "Range",
                "Область значений",
                "Проверено встроенным правилом области значений",
            ),
            OutputLanguage::Spanish => text(
                "Range",
                "Rango",
                "Verificado por la regla incorporada de rango",
            ),
            OutputLanguage::Arabic => text("Range", "مدى", "تم التحقق بقاعدة المدى المدمجة"),
            OutputLanguage::Japanese => text("Range", "値域", "値域の組み込み規則で検証しました"),
            OutputLanguage::Korean => text("Range", "치역", "치역 내장 규칙으로 검증했습니다"),
            OutputLanguage::Vietnamese => text(
                "Range",
                "Miền giá trị",
                "Đã kiểm chứng bằng quy tắc tích hợp miền giá trị",
            ),
        }
    }
}

impl FiniteSeqZeroLengthFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "Finite Seq Zero Length",
            "Length-zero finite sequence carrier is always finite (one empty sequence)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "零长度有限序列",
            "零长度有限序列载体有限",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "FiniteSeqZeroLength",
            "長度為零的有限序列",
            "長度為零的序列載體恆有限（只有一個空序列）",
        )
    },
            OutputLanguage::French => {
        text(
            "FiniteSeqZeroLength",
            "Suite finie de longueur nulle",
            "L'ensemble porteur des suites de longueur nulle est toujours fini (une suite vide)",
        )
    },
            OutputLanguage::Russian => {
        text(
            "FiniteSeqZeroLength",
            "Конечная последовательность нулевой длины",
            "Носитель последовательностей нулевой длины всегда конечен (одна пустая последовательность)",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "FiniteSeqZeroLength",
            "Secuencia finita de longitud cero",
            "El conjunto portador de secuencias de longitud cero siempre es finito (una secuencia vacía)",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "FiniteSeqZeroLength",
            "متتالية منتهية بطول صفر",
            "المجموعة الحاملة للمتتاليات بطول صفر منتهية دائمًا (متتالية خالية واحدة)",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "FiniteSeqZeroLength",
            "長さゼロの有限列",
            "長さゼロの列の台集合は常に有限です（空列一つ）",
        )
    },
            OutputLanguage::Korean => {
        text(
            "FiniteSeqZeroLength",
            "길이 0인 유한 수열",
            "길이 0 수열의 바탕 집합은 항상 유한합니다(빈 수열 하나)",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "FiniteSeqZeroLength",
            "Dãy hữu hạn độ dài không",
            "Tập nền các dãy độ dài không luôn hữu hạn (một dãy rỗng)",
        )
    },

        }
    }
}

impl FiniteSeqFromFiniteCodomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "Finite Seq From Finite Codomain",
            "Finite codomain ⇒ finite length-n sequence carrier",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "有限陪域的有限序列",
            "有限陪域上的定长序列载体有限",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSeqFromFiniteCodomain",
                "有限陪域的有限序列",
                "有限陪域 ⇒ 長度 n 的序列載體有限",
            ),
            OutputLanguage::French => text(
                "FiniteSeqFromFiniteCodomain",
                "Suite finie sur codomaine fini",
                "Codomaine fini ⇒ ensemble porteur fini des suites de longueur n",
            ),
            OutputLanguage::Russian => text(
                "FiniteSeqFromFiniteCodomain",
                "Конечные последовательности с конечной областью значений",
                "Конечная область значений ⇒ конечный носитель последовательностей длины n",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSeqFromFiniteCodomain",
                "Secuencia finita de codominio finito",
                "Codominio finito ⇒ conjunto portador finito de secuencias de longitud n",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSeqFromFiniteCodomain",
                "متتالية منتهية من مجال مقابل منتهٍ",
                "مجال مقابل منتهٍ ⇒ مجموعة حاملة منتهية للمتتاليات بطول n",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSeqFromFiniteCodomain",
                "有限終域上の有限列",
                "終域が有限 ⇒ 長さ n の列の台集合は有限",
            ),
            OutputLanguage::Korean => text(
                "FiniteSeqFromFiniteCodomain",
                "유한 공역의 유한 수열",
                "유한 공역 ⇒ 길이 n 수열의 바탕 집합이 유한",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSeqFromFiniteCodomain",
                "Dãy hữu hạn trên đối miền hữu hạn",
                "Đối miền hữu hạn ⇒ tập nền các dãy độ dài n hữu hạn",
            ),
        }
    }
}
