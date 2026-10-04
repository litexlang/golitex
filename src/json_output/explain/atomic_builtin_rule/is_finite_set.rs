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
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "Finite function range",
                "The range of a checked function with finite domain is finite",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "Finiteness of a surjective image",
                "A surjection with a checked finite domain has a finite codomain",
            ),
            Self::ListSet(p) => p.rule_id_and_message_en(),
            Self::ClosedRange(p) => p.rule_id_and_message_en(),
            Self::Range(p) => p.rule_id_and_message_en(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_en(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_en(),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "有限函数像",
                "已验证函数在有限定义域上的像是有限集",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "有限集合满射像的有限性",
                "经验证的满射若定义域有限，则陪域也有限",
            ),
            Self::ListSet(p) => p.rule_id_and_message_zh(),
            Self::ClosedRange(p) => p.rule_id_and_message_zh(),
            Self::Range(p) => p.rule_id_and_message_zh(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_zh(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_zh(),
        }
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "有限函數值域",
                "經驗證的有限定義域函數之值域有限",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "有限集合滿射像的有限性",
                "經驗證的滿射若定義域有限，則陪域也有限",
            ),
            Self::ListSet(p) => p.rule_id_and_message_zh_hant(),
            Self::ClosedRange(p) => p.rule_id_and_message_zh_hant(),
            Self::Range(p) => p.rule_id_and_message_zh_hant(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_zh_hant(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_zh_hant(),
        }
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "Image finie d'une fonction",
                "L'image d'une fonction vérifiée à domaine fini est finie",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "Finitude d’une image surjective",
                "Une surjection de domaine fini vérifié a un codomaine fini",
            ),
            Self::ListSet(p) => p.rule_id_and_message_fr(),
            Self::ClosedRange(p) => p.rule_id_and_message_fr(),
            Self::Range(p) => p.rule_id_and_message_fr(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_fr(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_fr(),
        }
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "Конечная область значений функции",
                "Область значений проверенной функции с конечной областью определения конечна",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "Конечность сюръективного образа",
                "Сюръекция с проверенной конечной областью определения имеет конечную область прибытия",
            ),
            Self::ListSet(p) => p.rule_id_and_message_ru(),
            Self::ClosedRange(p) => p.rule_id_and_message_ru(),
            Self::Range(p) => p.rule_id_and_message_ru(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_ru(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_ru(),
        }
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "Rango finito de función",
                "El rango de una función comprobada con dominio finito es finito",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "Finitud de una imagen sobreyectiva",
                "Una sobreyección con dominio finito comprobado tiene codominio finito",
            ),
            Self::ListSet(p) => p.rule_id_and_message_es(),
            Self::ClosedRange(p) => p.rule_id_and_message_es(),
            Self::Range(p) => p.rule_id_and_message_es(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_es(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_es(),
        }
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "مدى دالة منتهٍ",
                "مدى الدالة المتحقق منها ذات المجال المنتهي منتهٍ",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "انتهاء صورة شاملة",
                "الدالة الشاملة ذات المجال المنتهي المتحقق منه لها مجال مقابل منتهٍ",
            ),
            Self::ListSet(p) => p.rule_id_and_message_ar(),
            Self::ClosedRange(p) => p.rule_id_and_message_ar(),
            Self::Range(p) => p.rule_id_and_message_ar(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_ar(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_ar(),
        }
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "有限な関数の値域",
                "有限な定義域を持つ検証済み関数の値域は有限です",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "全射による像の有限性",
                "確認済みの有限な定義域からの全射の終域は有限です",
            ),
            Self::ListSet(p) => p.rule_id_and_message_ja(),
            Self::ClosedRange(p) => p.rule_id_and_message_ja(),
            Self::Range(p) => p.rule_id_and_message_ja(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_ja(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_ja(),
        }
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "유한한 함수 치역",
                "유한 정의역을 가진 검증된 함수의 치역은 유한합니다",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "전사상에 의한 상의 유한성",
                "검사된 유한 정의역을 갖는 전사상의 공역은 유한합니다",
            ),
            Self::ListSet(p) => p.rule_id_and_message_ko(),
            Self::ClosedRange(p) => p.rule_id_and_message_ko(),
            Self::Range(p) => p.rule_id_and_message_ko(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_ko(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_ko(),
        }
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::FunctionRangeOfFiniteDomain(_) => text(
                "FunctionRangeOfFiniteDomain",
                "Miền giá trị hàm hữu hạn",
                "Miền giá trị của hàm đã kiểm tra có miền xác định hữu hạn là hữu hạn",
            ),
            Self::SurjectiveImageOfFiniteSet(_) => text(
                "SurjectiveImageOfFiniteSet",
                "Tính hữu hạn của ảnh toàn ánh",
                "Một toàn ánh có miền xác định hữu hạn đã kiểm tra có đối miền hữu hạn",
            ),
            Self::ListSet(p) => p.rule_id_and_message_vi(),
            Self::ClosedRange(p) => p.rule_id_and_message_vi(),
            Self::Range(p) => p.rule_id_and_message_vi(),
            Self::FiniteSeqZeroLength(p) => p.rule_id_and_message_vi(),
            Self::FiniteSeqFromFiniteCodomain(p) => p.rule_id_and_message_vi(),
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
            "Finiteness of an explicitly listed set",
            "A set given by a finite list of elements is finite",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ListSet", "显式列举的集合是有限集", "由有限个元素列举而成的集合是有限集")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("ListSet", "顯式列舉的集合是有限集", "由有限個元素列舉而成的集合是有限集")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "Finitude d’un ensemble énuméré",
            "Un ensemble donné par une liste finie d’éléments est fini",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "Конечность явно перечисленного множества",
            "Множество, заданное конечным списком элементов, конечно",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "Finitud de un conjunto enumerado",
            "Un conjunto dado por una lista finita de elementos es finito",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "انتهاء مجموعة معدودة صراحة",
            "المجموعة المعطاة بقائمة منتهية من العناصر منتهية",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "列挙された集合の有限性",
            "有限個の要素を列挙した集合は有限集合です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "명시적으로 나열한 집합의 유한성",
            "유한 개의 원소를 나열해 정의한 집합은 유한집합입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ListSet",
            "Tính hữu hạn của tập được liệt kê",
            "Tập cho bởi một danh sách hữu hạn phần tử là hữu hạn",
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

impl ClosedRangeFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Finiteness of a bounded integer range",
            "A range between checked finite integer endpoints contains only finitely many integers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ClosedRange", "有界整数区间是有限集", "经检查的有限整数端点之间只含有限个整数")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("ClosedRange", "有界整數區間是有限集", "經檢查的有限整數端點之間只含有限個整數")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Finitude d’un intervalle entier borné",
            "Un intervalle entre deux bornes entières finies vérifiées contient un nombre fini d’entiers",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Конечность ограниченного целочисленного диапазона",
            "Диапазон между проверенными конечными целочисленными границами содержит конечное число целых",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Finitud de un intervalo entero acotado",
            "Un intervalo entre extremos enteros finitos comprobados contiene un número finito de enteros",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "انتهاء المجال الصحيح المحدود",
            "المجال بين طرفين صحيحين منتهيين متحقق منهما يحتوي عددًا منتهيًا من الأعداد الصحيحة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "有界な整数範囲の有限性",
            "確認済みの有限な整数の両端の間には有限個の整数しかありません",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "유계 정수 범위의 유한성",
            "검사된 유한한 정수 양 끝점 사이에는 유한 개의 정수만 있습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ClosedRange",
            "Tính hữu hạn của khoảng nguyên bị chặn",
            "Khoảng giữa hai đầu mút nguyên hữu hạn đã kiểm tra chỉ chứa hữu hạn số nguyên",
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

impl RangeFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("Range", "Finiteness of a bounded integer range", "A range between checked finite integer endpoints contains only finitely many integers")
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("Range", "有界整数区间是有限集", "经检查的有限整数端点之间只含有限个整数")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("Range", "有界整數區間是有限集", "經檢查的有限整數端點之間只含有限個整數")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text("Range", "Finitude d’un intervalle entier borné", "Un intervalle entre deux bornes entières finies vérifiées contient un nombre fini d’entiers")
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Range",
            "Конечность ограниченного целочисленного диапазона",
            "Диапазон между проверенными конечными целочисленными границами содержит конечное число целых",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Range",
            "Finitud de un intervalo entero acotado",
            "Un intervalo entre extremos enteros finitos comprobados contiene un número finito de enteros",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text("Range", "انتهاء المجال الصحيح المحدود", "المجال بين طرفين صحيحين منتهيين متحقق منهما يحتوي عددًا منتهيًا من الأعداد الصحيحة")
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text("Range", "有界な整数範囲の有限性", "確認済みの有限な整数の両端の間には有限個の整数しかありません")
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text("Range", "유계 정수 범위의 유한성", "검사된 유한한 정수 양 끝점 사이에는 유한 개의 정수만 있습니다")
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Range",
            "Tính hữu hạn của khoảng nguyên bị chặn",
            "Khoảng giữa hai đầu mút nguyên hữu hạn đã kiểm tra chỉ chứa hữu hạn số nguyên",
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

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "長度為零的有限序列",
            "長度為零的序列載體恆有限（只有一個空序列）",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "Suite finie de longueur nulle",
            "L'ensemble porteur des suites de longueur nulle est toujours fini (une suite vide)",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "Конечная последовательность нулевой длины",
            "Носитель последовательностей нулевой длины всегда конечен (одна пустая последовательность)",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "Secuencia finita de longitud cero",
            "El conjunto portador de secuencias de longitud cero siempre es finito (una secuencia vacía)",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "متتالية منتهية بطول صفر",
            "المجموعة الحاملة للمتتاليات بطول صفر منتهية دائمًا (متتالية خالية واحدة)",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "長さゼロの有限列",
            "長さゼロの列の台集合は常に有限です（空列一つ）",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "길이 0인 유한 수열",
            "길이 0 수열의 바탕 집합은 항상 유한합니다(빈 수열 하나)",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqZeroLength",
            "Dãy hữu hạn độ dài không",
            "Tập nền các dãy độ dài không luôn hữu hạn (một dãy rỗng)",
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

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "有限陪域的有限序列",
            "有限陪域 ⇒ 長度 n 的序列載體有限",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "Suite finie sur codomaine fini",
            "Codomaine fini ⇒ ensemble porteur fini des suites de longueur n",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "Конечные последовательности с конечной областью значений",
            "Конечная область значений ⇒ конечный носитель последовательностей длины n",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "Secuencia finita de codominio finito",
            "Codominio finito ⇒ conjunto portador finito de secuencias de longitud n",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "متتالية منتهية من مجال مقابل منتهٍ",
            "مجال مقابل منتهٍ ⇒ مجموعة حاملة منتهية للمتتاليات بطول n",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "有限終域上の有限列",
            "終域が有限 ⇒ 長さ n の列の台集合は有限",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "유한 공역의 유한 수열",
            "유한 공역 ⇒ 길이 n 수열의 바탕 집합이 유한",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FiniteSeqFromFiniteCodomain",
            "Dãy hữu hạn trên đối miền hữu hạn",
            "Đối miền hữu hạn ⇒ tập nền các dãy độ dài n hữu hạn",
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
