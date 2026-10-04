//! Explain + cite for `NotEqualFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{NotEqualFactSearchProofByBuiltinRule,
    AbsNonzeroFromArgBuiltinRuleProof,
    AddNonzeroFromNotEqualNegationBuiltinRuleProof,
    ClosedDecimalNotEqualBuiltinRuleProof,
    CosNonzeroAtZeroBuiltinRuleProof,
    CosNonzeroOnOpenHalfPiBuiltinRuleProof,
    DiffNonzeroFromInequalityBuiltinRuleProof,
    DivNonzeroFromFactorsBuiltinRuleProof,
    EmptySetFromNonemptyBuiltinRuleProof,
    FromKnownStrictOrderBuiltinRuleProof,
    ListSetDifferentLengthBuiltinRuleProof,
    MembershipContradictionBuiltinRuleProof,
    NotEqualSymmetryBuiltinRuleProof,
    PowNonzeroFromBaseBuiltinRuleProof,
    ProductComponentNonzeroBuiltinRuleProof,
    SinNonzeroAtHalfPiBuiltinRuleProof,
    SinNonzeroOnOpenPiBuiltinRuleProof,
    SqrtNonzeroFromPositiveArgBuiltinRuleProof,
    SquareSumNonzeroFromComponentBuiltinRuleProof,
    ZeroFromNatAndOneLeBuiltinRuleProof
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::PeriodicTrigNonzero(_) => match lang {
                OutputLanguage::English => text("PeriodicTrigNonzero", "Nonzero periodic trigonometric value", "The exact pi coefficient and checked integer terms exclude sine/cosine zeros"),
                OutputLanguage::ChineseTraditional => text("PeriodicTrigNonzero", "週期三角值非零", "精確 pi 係數與已驗證的整數項排除正弦或餘弦零點"),
                OutputLanguage::French => text("PeriodicTrigNonzero", "Valeur trigonométrique périodique non nulle", "Le coefficient exact de pi et les termes entiers vérifiés excluent les zéros du sinus ou cosinus"),
                OutputLanguage::Russian => text("PeriodicTrigNonzero", "Ненулевое периодическое тригонометрическое значение", "Точный коэффициент pi и проверенные целочисленные члены исключают нули синуса или косинуса"),
                OutputLanguage::Spanish => text("PeriodicTrigNonzero", "Valor trigonométrico periódico no nulo", "El coeficiente exacto de pi y los términos enteros comprobados excluyen ceros de seno o coseno"),
                OutputLanguage::Arabic => text("PeriodicTrigNonzero", "قيمة مثلثية دورية غير صفرية", "معامل pi الدقيق والحدود الصحيحة المتحقق منها يستبعدان أصفار الجيب أو جيب التمام"),
                OutputLanguage::Japanese => text("PeriodicTrigNonzero", "周期的三角関数値の非ゼロ性", "正確な pi の係数と検証済みの整数項が正弦または余弦の零点を除外します"),
                OutputLanguage::Korean => text("PeriodicTrigNonzero", "주기 삼각함숫값이 0이 아님", "정확한 pi 계수와 검증된 정수 항이 사인 또는 코사인의 영점을 배제합니다"),
                OutputLanguage::Vietnamese => text("PeriodicTrigNonzero", "Giá trị lượng giác tuần hoàn khác không", "Hệ số pi chính xác và các hạng nguyên đã kiểm tra loại trừ điểm không của sin hoặc cos"),

                OutputLanguage::Chinese => text("PeriodicTrigNonzero", "周期三角值非零", "精确 pi 系数和已验证的整数项排除了正弦或余弦的零点"),
            },
            Self::NonzeroFromSignedBound(_) => text("NonzeroFromSignedBound", "Nonzero from signed bound", "A checked bound strictly separates the value from zero"),
            Self::ImaginaryUnitNonzero(_) => match lang {
                OutputLanguage::English => text("ImaginaryUnitNonzero", "i ≠ 0", "The reserved imaginary unit satisfies i² = -1 and is nonzero"),
                OutputLanguage::ChineseTraditional => text("ImaginaryUnitNonzero", "i ≠ 0", "保留的虛數單位滿足 i² = -1 且非零"),
                OutputLanguage::French => text("ImaginaryUnitNonzero", "i ≠ 0", "L'unité imaginaire réservée vérifie i² = -1 et est non nulle"),
                OutputLanguage::Russian => text("ImaginaryUnitNonzero", "i ≠ 0", "Зарезервированная мнимая единица удовлетворяет i² = -1 и ненулевая"),
                OutputLanguage::Spanish => text("ImaginaryUnitNonzero", "i ≠ 0", "La unidad imaginaria reservada cumple i² = -1 y es no nula"),
                OutputLanguage::Arabic => text("ImaginaryUnitNonzero", "i ≠ 0", "الوحدة التخيلية المحجوزة تحقق i² = -1 وهي غير صفرية"),
                OutputLanguage::Japanese => text("ImaginaryUnitNonzero", "i ≠ 0", "予約された虚数単位は i² = -1 を満たし、非ゼロです"),
                OutputLanguage::Korean => text("ImaginaryUnitNonzero", "i ≠ 0", "예약된 허수 단위는 i² = -1을 만족하며 0이 아닙니다"),
                OutputLanguage::Vietnamese => text("ImaginaryUnitNonzero", "i ≠ 0", "Đơn vị ảo dành riêng thỏa i² = -1 và khác không"),

                OutputLanguage::Chinese => text("ImaginaryUnitNonzero", "虚数单位非零", "内建虚数单位满足 i² = -1，因而不等于零"),
            },
            Self::InequalityFromDifferenceNonzero(_) => text("InequalityFromDifferenceNonzero", "Nonzero difference", "A checked nonzero difference implies unequal operands"),
            Self::InequalityFromSumNonzero(_) => text("InequalityFromSumNonzero", "Nonzero sum", "A checked nonzero sum excludes opposite operands"),
            Self::ComplexModulusNonzero(_) => text("ComplexModulusNonzero", "Nonzero complex modulus", "A nonzero complex number has nonzero modulus"),
            Self::PiNonzero(_) => text("PiNonzero", "π ≠ 0", "The real constant π is strictly positive, hence nonzero"),
            Self::ClosedDecimal(p) => p.rule_id_and_message(lang),
            Self::ClosedRational(_) => match lang {
                OutputLanguage::English => text("ClosedRationalNotEqual", "Exact rational inequality", "Exact closed fractions have different normalized values"),
                OutputLanguage::ChineseTraditional => text("ClosedRationalNotEqual", "精確有理數不等", "精確封閉分數的正規化值不同"),
                OutputLanguage::French => text("ClosedRationalNotEqual", "Inégalité rationnelle exacte", "Les fractions fermées exactes ont des valeurs normalisées différentes"),
                OutputLanguage::Russian => text("ClosedRationalNotEqual", "Точное рациональное неравенство", "Точные замкнутые дроби имеют различные нормализованные значения"),
                OutputLanguage::Spanish => text("ClosedRationalNotEqual", "Desigualdad racional exacta", "Las fracciones cerradas exactas tienen valores normalizados distintos"),
                OutputLanguage::Arabic => text("ClosedRationalNotEqual", "عدم مساواة نسبية دقيقة", "الكسور المغلقة الدقيقة لها قيم مطبّعة مختلفة"),
                OutputLanguage::Japanese => text("ClosedRationalNotEqual", "有理数の正確な不等性", "正確な閉じた分数の正規化値が異なります"),
                OutputLanguage::Korean => text("ClosedRationalNotEqual", "정확한 유리수 불일치", "정확한 닫힌 분수의 정규화 값이 다릅니다"),
                OutputLanguage::Vietnamese => text("ClosedRationalNotEqual", "Bất đẳng thức hữu tỉ chính xác", "Các phân số đóng chính xác có giá trị chuẩn hóa khác nhau"),

                OutputLanguage::Chinese => text("ClosedRationalNotEqual", "精确分数不等", "两边的精确分数规范化后不同"),
            },
            Self::ClosedComplex(_) => match lang {
                OutputLanguage::English => text("ClosedComplexNotEqual", "Exact complex inequality", "The exact real or imaginary coordinates differ"),
                OutputLanguage::ChineseTraditional => text("ClosedComplexNotEqual", "精確複數不等", "精確實部或虛部座標不同"),
                OutputLanguage::French => text("ClosedComplexNotEqual", "Inégalité complexe exacte", "Les coordonnées réelles ou imaginaires exactes diffèrent"),
                OutputLanguage::Russian => text("ClosedComplexNotEqual", "Точное комплексное неравенство", "Точные действительные или мнимые координаты различаются"),
                OutputLanguage::Spanish => text("ClosedComplexNotEqual", "Desigualdad compleja exacta", "Las coordenadas reales o imaginarias exactas difieren"),
                OutputLanguage::Arabic => text("ClosedComplexNotEqual", "عدم مساواة مركبة دقيقة", "الإحداثيات الحقيقية أو التخيلية الدقيقة مختلفة"),
                OutputLanguage::Japanese => text("ClosedComplexNotEqual", "複素数の正確な不等性", "正確な実部または虚部の座標が異なります"),
                OutputLanguage::Korean => text("ClosedComplexNotEqual", "정확한 복소수 불일치", "정확한 실수부 또는 허수부 좌표가 다릅니다"),
                OutputLanguage::Vietnamese => text("ClosedComplexNotEqual", "Bất đẳng thức phức chính xác", "Các tọa độ thực hoặc ảo chính xác khác nhau"),

                OutputLanguage::Chinese => text("ClosedComplexNotEqual", "精确复数不等", "精确实部或虚部不同"),
            },
            Self::NotEqualSymmetry(p) => p.rule_id_and_message(lang),
            Self::ListSetDifferentLength(p) => p.rule_id_and_message(lang),
            Self::FromKnownStrictOrder(p) => p.rule_id_and_message(lang),
            Self::CosNonzeroOnOpenHalfPi(p) => p.rule_id_and_message(lang),
            Self::CosNonzeroAtZero(p) => p.rule_id_and_message(lang),
            Self::SinNonzeroOnOpenPi(p) => p.rule_id_and_message(lang),
            Self::SinNonzeroAtHalfPi(p) => p.rule_id_and_message(lang),
            Self::AbsNonzeroFromArg(p) => p.rule_id_and_message(lang),
            Self::DiffNonzeroFromInequality(p) => p.rule_id_and_message(lang),
            Self::EmptySetFromNonempty(p) => p.rule_id_and_message(lang),
            Self::ZeroFromNatAndOneLe(p) => p.rule_id_and_message(lang),
            Self::PowNonzeroFromBase(p) => p.rule_id_and_message(lang),
            Self::DivNonzeroFromFactors(p) => p.rule_id_and_message(lang),
            Self::ProductComponentNonzero(p) => p.rule_id_and_message(lang),
            Self::SqrtNonzeroFromPositiveArg(p) => p.rule_id_and_message(lang),
            Self::SquareSumNonzeroFromComponent(p) => p.rule_id_and_message(lang),
            Self::AddNonzeroFromNotEqualNegation(p) => p.rule_id_and_message(lang),
            Self::MembershipContradiction(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::NonzeroFromSignedBound(p) => Some(p.cite_fact_id),
            Self::FromKnownStrictOrder(p) => p.premise_proof.cite_fact_id(),
            Self::InequalityFromDifferenceNonzero(p) => p.premise_proof.cite_fact_id(),
            Self::InequalityFromSumNonzero(p) => p.premise_proof.cite_fact_id(),
            _ => None,
        }
    }
}

impl ClosedDecimalNotEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedDecimalNotEqual",
            "Closed decimal inequality",
            "Both sides evaluate to different closed numbers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedDecimalNotEqual",
            "封闭数值不等",
            "两边算出不同的封闭数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedDecimalNotEqual",
                "封閉十進位不等",
                "兩邊算出不同的封閉數值",
            ),
            OutputLanguage::French => text(
                "ClosedDecimalNotEqual",
                "Inégalité décimale fermée",
                "Les deux membres donnent des nombres fermés différents",
            ),
            OutputLanguage::Russian => text(
                "ClosedDecimalNotEqual",
                "Неравенство замкнутых десятичных значений",
                "Обе части вычисляются в различные замкнутые числа",
            ),
            OutputLanguage::Spanish => text(
                "ClosedDecimalNotEqual",
                "Desigualdad decimal cerrada",
                "Ambos lados dan números cerrados diferentes",
            ),
            OutputLanguage::Arabic => text(
                "ClosedDecimalNotEqual",
                "عدم مساواة عشرية مغلقة",
                "يُقيَّم الطرفان إلى عددين مغلقين مختلفين",
            ),
            OutputLanguage::Japanese => text(
                "ClosedDecimalNotEqual",
                "閉じた小数値の不等性",
                "両辺の評価値は異なる閉じた数値です",
            ),
            OutputLanguage::Korean => text(
                "ClosedDecimalNotEqual",
                "닫힌 소수 값의 불일치",
                "양변의 평가값은 서로 다른 닫힌 수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedDecimalNotEqual",
                "Bất đẳng thức thập phân đóng",
                "Hai vế cho các số đóng khác nhau",
            ),
        }
    }
}

impl NotEqualSymmetryBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NotEqualSymmetry",
            "Inequality symmetry",
            "Inequality is symmetric in its two sides",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("NotEqualSymmetry", "不等号对称性", "不等关系对两边对称")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("NotEqualSymmetry", "不等關係對稱性", "不等關係的兩邊對稱")
            }
            OutputLanguage::French => text(
                "NotEqualSymmetry",
                "Symétrie de l'inégalité de valeurs",
                "L'inégalité de valeurs est symétrique entre ses deux membres",
            ),
            OutputLanguage::Russian => text(
                "NotEqualSymmetry",
                "Симметрия неравенства значений",
                "Неравенство значений симметрично относительно обеих частей",
            ),
            OutputLanguage::Spanish => text(
                "NotEqualSymmetry",
                "Simetría de desigualdad de valores",
                "La desigualdad de valores es simétrica entre sus dos lados",
            ),
            OutputLanguage::Arabic => text(
                "NotEqualSymmetry",
                "تناظر عدم المساواة",
                "عدم المساواة متناظرة في طرفيها",
            ),
            OutputLanguage::Japanese => text(
                "NotEqualSymmetry",
                "非等値関係の対称性",
                "非等値関係は両辺について対称です",
            ),
            OutputLanguage::Korean => text(
                "NotEqualSymmetry",
                "불일치 대칭성",
                "같지 않음 관계는 양변에 대해 대칭입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NotEqualSymmetry",
                "Tính đối xứng của không bằng nhau",
                "Quan hệ không bằng nhau đối xứng theo hai vế",
            ),
        }
    }
}

impl ListSetDifferentLengthBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetDifferentLength",
            "List sets ≠ by length",
            "List sets of different lengths are unequal",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetDifferentLength",
            "列表集因长度不等",
            "不同长度的列表集不等",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ListSetDifferentLength",
                "由長度得列表集合不等",
                "長度不同的列表集合不相等",
            ),
            OutputLanguage::French => text(
                "ListSetDifferentLength",
                "Inégalité d'ensembles listes par longueur",
                "Des ensembles listes de longueurs différentes sont inégaux",
            ),
            OutputLanguage::Russian => text(
                "ListSetDifferentLength",
                "Неравенство списочных множеств по длине",
                "Списочные множества различной длины не равны",
            ),
            OutputLanguage::Spanish => text(
                "ListSetDifferentLength",
                "Desigualdad de conjuntos de lista por longitud",
                "Conjuntos de lista de distinta longitud son desiguales",
            ),
            OutputLanguage::Arabic => text(
                "ListSetDifferentLength",
                "عدم مساواة مجموعات القوائم بالطول",
                "مجموعات القوائم ذات الأطوال المختلفة غير متساوية",
            ),
            OutputLanguage::Japanese => text(
                "ListSetDifferentLength",
                "長さによるリスト集合の不等性",
                "長さの異なるリスト集合は等しくありません",
            ),
            OutputLanguage::Korean => text(
                "ListSetDifferentLength",
                "길이에 의한 목록 집합 불일치",
                "길이가 다른 목록 집합은 같지 않습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ListSetDifferentLength",
                "Tập danh sách khác nhau theo độ dài",
                "Các tập danh sách có độ dài khác nhau không bằng nhau",
            ),
        }
    }
}

impl FromKnownStrictOrderBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownStrictOrder",
            "From known strict order",
            "Inequality follows from a known strict order fact",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownStrictOrder",
            "由已知严格序",
            "不等关系由已知严格序事实推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FromKnownStrictOrder",
                "由已知嚴格序",
                "不等由已知嚴格序命題得出",
            ),
            OutputLanguage::French => text(
                "FromKnownStrictOrder",
                "Depuis un ordre strict connu",
                "L'inégalité découle d'une proposition d'ordre strict connue",
            ),
            OutputLanguage::Russian => text(
                "FromKnownStrictOrder",
                "Из известного строгого порядка",
                "Неравенство следует из известного утверждения строгого порядка",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownStrictOrder",
                "Desde orden estricto conocido",
                "La desigualdad se deduce de una proposición de orden estricto conocida",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownStrictOrder",
                "من ترتيب صارم معلوم",
                "تنتج عدم المساواة من قضية ترتيب صارم معلومة",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownStrictOrder",
                "既知の狭義順序から",
                "不等性は既知の狭義順序の命題から導かれます",
            ),
            OutputLanguage::Korean => text(
                "FromKnownStrictOrder",
                "알려진 엄격한 순서에서",
                "불일치는 알려진 엄격한 순서 명제에서 도출됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownStrictOrder",
                "Từ thứ tự nghiêm ngặt đã biết",
                "Bất đẳng thức suy ra từ mệnh đề thứ tự nghiêm ngặt đã biết",
            ),
        }
    }
}

impl CosNonzeroOnOpenHalfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CosNonzeroOnOpenHalfPi",
            "cos ≠ 0 on (-π/2,π/2)",
            "cosine is nonzero on the open half-pi interval",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "CosNonzeroOnOpenHalfPi",
            "cos 在 (-π/2,π/2) 非零",
            "余弦在开半 π 区间上非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "CosNonzeroOnOpenHalfPi",
                "(-π/2,π/2) 上 cos ≠ 0",
                "餘弦在開半 pi 區間上非零",
            ),
            OutputLanguage::French => text(
                "CosNonzeroOnOpenHalfPi",
                "cos ≠ 0 sur (-π/2,π/2)",
                "Le cosinus est non nul sur l'intervalle ouvert de demi-pi",
            ),
            OutputLanguage::Russian => text(
                "CosNonzeroOnOpenHalfPi",
                "cos ≠ 0 на (-π/2,π/2)",
                "Косинус ненулевой на открытом интервале половины pi",
            ),
            OutputLanguage::Spanish => text(
                "CosNonzeroOnOpenHalfPi",
                "cos ≠ 0 en (-π/2,π/2)",
                "El coseno es no nulo en el intervalo abierto de medio pi",
            ),
            OutputLanguage::Arabic => text(
                "CosNonzeroOnOpenHalfPi",
                "cos ≠ 0 على (-π/2,π/2)",
                "جيب التمام غير صفري على فترة نصف pi المفتوحة",
            ),
            OutputLanguage::Japanese => text(
                "CosNonzeroOnOpenHalfPi",
                "(-π/2,π/2) 上で cos ≠ 0",
                "余弦は開いた半 pi 区間上で非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "CosNonzeroOnOpenHalfPi",
                "(-π/2,π/2)에서 cos ≠ 0",
                "코사인은 열린 반 pi 구간에서 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "CosNonzeroOnOpenHalfPi",
                "cos ≠ 0 trên (-π/2,π/2)",
                "Cos khác không trên khoảng nửa pi mở",
            ),
        }
    }
}

impl CosNonzeroAtZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CosNonzeroAtZero",
            "cos(0) ≠ 0",
            "cosine is nonzero at zero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CosNonzeroAtZero", "cos(0) ≠ 0", "余弦在 0 处非零")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("CosNonzeroAtZero", "cos(0) ≠ 0", "餘弦在零處非零")
            }
            OutputLanguage::French => text(
                "CosNonzeroAtZero",
                "cos(0) ≠ 0",
                "Le cosinus est non nul en zéro",
            ),
            OutputLanguage::Russian => {
                text("CosNonzeroAtZero", "cos(0) ≠ 0", "Косинус ненулевой в нуле")
            }
            OutputLanguage::Spanish => text(
                "CosNonzeroAtZero",
                "cos(0) ≠ 0",
                "El coseno es no nulo en cero",
            ),
            OutputLanguage::Arabic => text(
                "CosNonzeroAtZero",
                "cos(0) ≠ 0",
                "جيب التمام غير صفري عند الصفر",
            ),
            OutputLanguage::Japanese => {
                text("CosNonzeroAtZero", "cos(0) ≠ 0", "余弦はゼロで非ゼロです")
            }
            OutputLanguage::Korean => text(
                "CosNonzeroAtZero",
                "cos(0) ≠ 0",
                "코사인은 0에서 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => {
                text("CosNonzeroAtZero", "cos(0) ≠ 0", "Cos khác không tại không")
            }
        }
    }
}

impl SinNonzeroOnOpenPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SinNonzeroOnOpenPi",
            "sin ≠ 0 on (0,π)",
            "sine is nonzero on the open pi interval",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SinNonzeroOnOpenPi",
            "sin 在 (0,π) 非零",
            "正弦在开 π 区间上非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SinNonzeroOnOpenPi",
                "(0,π) 上 sin ≠ 0",
                "正弦在開 pi 區間上非零",
            ),
            OutputLanguage::French => text(
                "SinNonzeroOnOpenPi",
                "sin ≠ 0 sur (0,π)",
                "Le sinus est non nul sur l'intervalle ouvert de pi",
            ),
            OutputLanguage::Russian => text(
                "SinNonzeroOnOpenPi",
                "sin ≠ 0 на (0,π)",
                "Синус ненулевой на открытом интервале pi",
            ),
            OutputLanguage::Spanish => text(
                "SinNonzeroOnOpenPi",
                "sin ≠ 0 en (0,π)",
                "El seno es no nulo en el intervalo abierto de pi",
            ),
            OutputLanguage::Arabic => text(
                "SinNonzeroOnOpenPi",
                "sin ≠ 0 على (0,π)",
                "الجيب غير صفري على فترة pi المفتوحة",
            ),
            OutputLanguage::Japanese => text(
                "SinNonzeroOnOpenPi",
                "(0,π) 上で sin ≠ 0",
                "正弦は開いた pi 区間上で非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "SinNonzeroOnOpenPi",
                "(0,π)에서 sin ≠ 0",
                "사인은 열린 pi 구간에서 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SinNonzeroOnOpenPi",
                "sin ≠ 0 trên (0,π)",
                "Sin khác không trên khoảng pi mở",
            ),
        }
    }
}

impl SinNonzeroAtHalfPiBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SinNonzeroAtHalfPi",
            "sin(π/2) ≠ 0",
            "sine is nonzero at half pi",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SinNonzeroAtHalfPi", "sin(π/2) ≠ 0", "正弦在 π/2 处非零")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SinNonzeroAtHalfPi", "sin(π/2) ≠ 0", "正弦在半 pi 處非零")
            }
            OutputLanguage::French => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "Le sinus est non nul en demi-pi",
            ),
            OutputLanguage::Russian => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "Синус ненулевой в половине pi",
            ),
            OutputLanguage::Spanish => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "El seno es no nulo en medio pi",
            ),
            OutputLanguage::Arabic => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "الجيب غير صفري عند نصف pi",
            ),
            OutputLanguage::Japanese => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "正弦は半 pi で非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "사인은 반 pi에서 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SinNonzeroAtHalfPi",
                "sin(π/2) ≠ 0",
                "Sin khác không tại nửa pi",
            ),
        }
    }
}

impl AbsNonzeroFromArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsNonzeroFromArg",
            "|x| ≠ 0 from x ≠ 0",
            "Absolute value is nonzero when the argument is nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsNonzeroFromArg",
            "由 x ≠ 0 得 |x| ≠ 0",
            "当参数非零时绝对值非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "引數非零時絕對值非零",
            ),
            OutputLanguage::French => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "La valeur absolue est non nulle si l'argument est non nul",
            ),
            OutputLanguage::Russian => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "Модуль ненулевой, если аргумент ненулевой",
            ),
            OutputLanguage::Spanish => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "El valor absoluto es no nulo si el argumento es no nulo",
            ),
            OutputLanguage::Arabic => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "القيمة المطلقة غير صفرية إذا كان الوسيط غير صفري",
            ),
            OutputLanguage::Japanese => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "引数が非ゼロなら絶対値は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "인수가 0이 아니면 절댓값은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsNonzeroFromArg",
                "x ≠ 0 ⇒ |x| ≠ 0",
                "Giá trị tuyệt đối khác không khi đối số khác không",
            ),
        }
    }
}

impl DiffNonzeroFromInequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DiffNonzeroFromInequality",
            "a-b ≠ 0 from a ≠ b",
            "A difference is nonzero when the operands are unequal",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DiffNonzeroFromInequality",
            "由 a ≠ b 得 a-b ≠ 0",
            "两边不等则差非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "運算元不等時差非零",
            ),
            OutputLanguage::French => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "Une différence est non nulle si les opérandes sont différents",
            ),
            OutputLanguage::Russian => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "Разность ненулевая, если операнды не равны",
            ),
            OutputLanguage::Spanish => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "La diferencia es no nula si los operandos son distintos",
            ),
            OutputLanguage::Arabic => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "الفرق غير صفري إذا كان المعاملان غير متساويين",
            ),
            OutputLanguage::Japanese => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "被演算子が異なれば差は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "피연산자가 다르면 차는 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "DiffNonzeroFromInequality",
                "a ≠ b ⇒ a-b ≠ 0",
                "Hiệu khác không khi các toán hạng không bằng nhau",
            ),
        }
    }
}

impl EmptySetFromNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EmptySetFromNonempty",
            "∅ ≠ nonempty",
            "The empty set is unequal to a nonempty set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EmptySetFromNonempty", "∅ ≠ 非空", "空集不等于非空集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "EmptySetFromNonempty",
                "∅ 不等於非空集合",
                "空集合不等於非空集合",
            ),
            OutputLanguage::French => text(
                "EmptySetFromNonempty",
                "∅ ≠ ensemble non vide",
                "L'ensemble vide est différent d'un ensemble non vide",
            ),
            OutputLanguage::Russian => text(
                "EmptySetFromNonempty",
                "∅ ≠ непустое множество",
                "Пустое множество не равно непустому",
            ),
            OutputLanguage::Spanish => text(
                "EmptySetFromNonempty",
                "∅ ≠ conjunto no vacío",
                "El conjunto vacío no es igual a un conjunto no vacío",
            ),
            OutputLanguage::Arabic => text(
                "EmptySetFromNonempty",
                "∅ ≠ مجموعة غير خالية",
                "المجموعة الخالية لا تساوي مجموعة غير خالية",
            ),
            OutputLanguage::Japanese => text(
                "EmptySetFromNonempty",
                "∅ ≠ 空でない集合",
                "空集合は空でない集合と等しくありません",
            ),
            OutputLanguage::Korean => text(
                "EmptySetFromNonempty",
                "∅ ≠ 비어 있지 않은 집합",
                "공집합은 비어 있지 않은 집합과 같지 않습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "EmptySetFromNonempty",
                "∅ ≠ tập không rỗng",
                "Tập rỗng không bằng tập không rỗng",
            ),
        }
    }
}

impl ZeroFromNatAndOneLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ZeroFromNatAndOneLe",
            "0 from n∈N and 1≤n false path",
            "Zero follows from natural membership with a one-lower-bound contradiction path",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ZeroFromNatAndOneLe",
            "由 n∈N 与 1≤n 矛盾得 0",
            "由自然数成员与 1 下界矛盾路径得到零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "ZeroFromNatAndOneLe",
            "由 n∈N 與 1≤n 的矛盾路徑得零",
            "由自然數成員關係與下界一的矛盾路徑得零",
        )
    },
            OutputLanguage::French => {
        text(
            "ZeroFromNatAndOneLe",
            "Zéro depuis n∈N et une contradiction avec 1≤n",
            "Zéro découle de l'appartenance aux naturels avec une contradiction sur la borne inférieure un",
        )
    },
            OutputLanguage::Russian => {
        text(
            "ZeroFromNatAndOneLe",
            "Ноль из n∈N и противоречия с 1≤n",
            "Ноль следует из принадлежности натуральным с противоречием нижней границе один",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "ZeroFromNatAndOneLe",
            "Cero desde n∈N y contradicción con 1≤n",
            "Cero se deduce de pertenencia a naturales con contradicción de cota inferior uno",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "ZeroFromNatAndOneLe",
            "صفر من n∈N ومسار تناقض مع 1≤n",
            "ينتج الصفر من الانتماء للطبيعيين مع مسار تناقض للحد الأدنى واحد",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "ZeroFromNatAndOneLe",
            "n∈N と 1≤n の矛盾経路からゼロ",
            "自然数への所属と下界一の矛盾経路からゼロを導きます",
        )
    },
            OutputLanguage::Korean => {
        text(
            "ZeroFromNatAndOneLe",
            "n∈N과 1≤n 모순 경로에서 0",
            "자연수 소속과 하한 1의 모순 경로에서 0을 도출합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "ZeroFromNatAndOneLe",
            "Không từ n∈N và đường mâu thuẫn với 1≤n",
            "Không suy ra từ sự thuộc về số tự nhiên với đường mâu thuẫn cận dưới một",
        )
    },

        }
    }
}

impl PowNonzeroFromBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowNonzeroFromBase",
            "pow ≠ 0 from base",
            "A power is nonzero when the base is nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PowNonzeroFromBase", "由底非零得幂非零", "底非零则幂非零")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PowNonzeroFromBase",
                "由底數非零得冪非零",
                "底數非零時冪非零",
            ),
            OutputLanguage::French => text(
                "PowNonzeroFromBase",
                "Puissance ≠ 0 depuis la base",
                "Une puissance est non nulle si la base est non nulle",
            ),
            OutputLanguage::Russian => text(
                "PowNonzeroFromBase",
                "Степень ≠ 0 из основания",
                "Степень ненулевая, если основание ненулевое",
            ),
            OutputLanguage::Spanish => text(
                "PowNonzeroFromBase",
                "Potencia ≠ 0 desde la base",
                "Una potencia es no nula si la base es no nula",
            ),
            OutputLanguage::Arabic => text(
                "PowNonzeroFromBase",
                "القوة ≠ 0 من الأساس",
                "القوة غير صفرية إذا كان الأساس غير صفري",
            ),
            OutputLanguage::Japanese => text(
                "PowNonzeroFromBase",
                "底から冪 ≠ 0",
                "底が非ゼロなら冪は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "PowNonzeroFromBase",
                "밑으로 거듭제곱 ≠ 0",
                "밑이 0이 아니면 거듭제곱은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PowNonzeroFromBase",
                "Lũy thừa ≠ 0 từ cơ số",
                "Lũy thừa khác không khi cơ số khác không",
            ),
        }
    }
}

impl DivNonzeroFromFactorsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivNonzeroFromFactors",
            "a/b ≠ 0 from factors",
            "A quotient is nonzero when numerator and denominator are nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivNonzeroFromFactors",
            "由因子得 a/b ≠ 0",
            "分子分母都非零则商非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DivNonzeroFromFactors",
                "由因子非零得 a/b ≠ 0",
                "分子與分母非零時商非零",
            ),
            OutputLanguage::French => text(
                "DivNonzeroFromFactors",
                "a/b ≠ 0 depuis les facteurs",
                "Un quotient est non nul si le numérateur et le dénominateur sont non nuls",
            ),
            OutputLanguage::Russian => text(
                "DivNonzeroFromFactors",
                "a/b ≠ 0 из множителей",
                "Частное ненулевое, если числитель и знаменатель ненулевые",
            ),
            OutputLanguage::Spanish => text(
                "DivNonzeroFromFactors",
                "a/b ≠ 0 a partir de factores",
                "Un cociente es no nulo si numerador y denominador son no nulos",
            ),
            OutputLanguage::Arabic => text(
                "DivNonzeroFromFactors",
                "a/b ≠ 0 من العوامل",
                "خارج القسمة غير صفري إذا كان البسط والمقام غير صفريين",
            ),
            OutputLanguage::Japanese => text(
                "DivNonzeroFromFactors",
                "因子から a/b ≠ 0",
                "分子と分母が非ゼロなら商は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "DivNonzeroFromFactors",
                "인자로 a/b ≠ 0",
                "분자와 분모가 0이 아니면 몫은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "DivNonzeroFromFactors",
                "a/b ≠ 0 từ các thừa số",
                "Thương khác không khi tử và mẫu khác không",
            ),
        }
    }
}

impl ProductComponentNonzeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductComponentNonzero",
            "Product ≠ 0 from component",
            "A product is nonzero when a component is nonzero under nonzero companions",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ProductComponentNonzero",
            "由分量得积 ≠ 0",
            "在同伴非零时，分量非零则积非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ProductComponentNonzero",
                "由分量非零得乘積非零",
                "一因子非零且其他因子非零時乘積非零",
            ),
            OutputLanguage::French => text(
                "ProductComponentNonzero",
                "Produit ≠ 0 depuis une composante",
                "Un produit est non nul si une composante et ses facteurs associés sont non nuls",
            ),
            OutputLanguage::Russian => text(
                "ProductComponentNonzero",
                "Произведение ≠ 0 из компоненты",
                "Произведение ненулевое, если компонента и остальные множители ненулевые",
            ),
            OutputLanguage::Spanish => text(
                "ProductComponentNonzero",
                "Producto ≠ 0 desde componente",
                "Un producto es no nulo si una componente y los factores acompañantes son no nulos",
            ),
            OutputLanguage::Arabic => text(
                "ProductComponentNonzero",
                "حاصل الضرب ≠ 0 من مكوّن",
                "حاصل الضرب غير صفري إذا كان أحد المكونات ومرافقاته غير صفرية",
            ),
            OutputLanguage::Japanese => text(
                "ProductComponentNonzero",
                "成分から積 ≠ 0",
                "一つの成分と他の因子が非ゼロなら積は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "ProductComponentNonzero",
                "성분으로 곱 ≠ 0",
                "한 성분과 나머지 인자가 모두 0이 아니면 곱은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductComponentNonzero",
                "Tích ≠ 0 từ thành phần",
                "Tích khác không khi một thành phần và các thừa số đi kèm khác không",
            ),
        }
    }
}

impl SqrtNonzeroFromPositiveArgBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtNonzeroFromPositiveArg",
            "√ ≠ 0 from positive arg",
            "Square root is nonzero when the argument is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtNonzeroFromPositiveArg",
            "由正参数得 √ ≠ 0",
            "当参数为正时平方根非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SqrtNonzeroFromPositiveArg",
                "由正引數得 √ 非零",
                "引數正時平方根非零",
            ),
            OutputLanguage::French => text(
                "SqrtNonzeroFromPositiveArg",
                "√ ≠ 0 depuis un argument positif",
                "La racine carrée est non nulle si l'argument est positif",
            ),
            OutputLanguage::Russian => text(
                "SqrtNonzeroFromPositiveArg",
                "√ ≠ 0 из положительного аргумента",
                "Квадратный корень ненулевой, если аргумент положителен",
            ),
            OutputLanguage::Spanish => text(
                "SqrtNonzeroFromPositiveArg",
                "√ ≠ 0 desde argumento positivo",
                "La raíz cuadrada es no nula si el argumento es positivo",
            ),
            OutputLanguage::Arabic => text(
                "SqrtNonzeroFromPositiveArg",
                "√ ≠ 0 من وسيط موجب",
                "الجذر التربيعي غير صفري إذا كان الوسيط موجبًا",
            ),
            OutputLanguage::Japanese => text(
                "SqrtNonzeroFromPositiveArg",
                "正の引数から √ ≠ 0",
                "引数が正なら平方根は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "SqrtNonzeroFromPositiveArg",
                "양수 인수로 √ ≠ 0",
                "인수가 양수이면 제곱근은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SqrtNonzeroFromPositiveArg",
                "√ ≠ 0 từ đối số dương",
                "Căn bậc hai khác không khi đối số dương",
            ),
        }
    }
}

impl SquareSumNonzeroFromComponentBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SquareSumNonzeroFromComponent",
            "a²+b² ≠ 0",
            "A sum of squares is nonzero when a component is nonzero",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SquareSumNonzeroFromComponent",
            "a²+b² ≠ 0",
            "分量非零则平方和非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "一分量非零時平方和非零",
            ),
            OutputLanguage::French => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "Une somme de carrés est non nulle si une composante est non nulle",
            ),
            OutputLanguage::Russian => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "Сумма квадратов ненулевая, если одна компонента ненулевая",
            ),
            OutputLanguage::Spanish => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "Una suma de cuadrados es no nula si una componente es no nula",
            ),
            OutputLanguage::Arabic => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "مجموع المربعات غير صفري إذا كان أحد المكونات غير صفري",
            ),
            OutputLanguage::Japanese => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "一つの成分が非ゼロなら平方和は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "한 성분이 0이 아니면 제곱합은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SquareSumNonzeroFromComponent",
                "a²+b² ≠ 0",
                "Tổng bình phương khác không khi một thành phần khác không",
            ),
        }
    }
}

impl AddNonzeroFromNotEqualNegationBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddNonzeroFromNotEqualNegation",
            "a+b ≠ 0 from a ≠ -b",
            "A sum is nonzero when the summands are not negatives",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddNonzeroFromNotEqualNegation",
            "由 a ≠ -b 得 a+b ≠ 0",
            "加数互不为相反数则和非零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "加數不是互為相反數時和非零",
            ),
            OutputLanguage::French => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "Une somme est non nulle si les termes ne sont pas opposés",
            ),
            OutputLanguage::Russian => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "Сумма ненулевая, если слагаемые не противоположны",
            ),
            OutputLanguage::Spanish => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "Una suma es no nula si los sumandos no son opuestos",
            ),
            OutputLanguage::Arabic => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "المجموع غير صفري إذا لم يكن الحدّان متعاكسين",
            ),
            OutputLanguage::Japanese => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "加数が互いに逆符号の同値でなければ和は非ゼロです",
            ),
            OutputLanguage::Korean => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "두 항이 서로 반대수가 아니면 합은 0이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddNonzeroFromNotEqualNegation",
                "a ≠ -b ⇒ a+b ≠ 0",
                "Tổng khác không khi các số hạng không đối nhau",
            ),
        }
    }
}

impl MembershipContradictionBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MembershipContradiction",
            "Membership contradiction",
            "Conflicting membership facts yield inequality",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MembershipContradiction",
            "成员关系矛盾",
            "冲突的成员关系推出不等",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MembershipContradiction",
                "成員關係矛盾",
                "衝突的成員關係得出不等",
            ),
            OutputLanguage::French => text(
                "MembershipContradiction",
                "Contradiction d'appartenance",
                "Des appartenances incompatibles impliquent l'inégalité",
            ),
            OutputLanguage::Russian => text(
                "MembershipContradiction",
                "Противоречие принадлежности",
                "Противоречивые принадлежности дают неравенство",
            ),
            OutputLanguage::Spanish => text(
                "MembershipContradiction",
                "Contradicción de pertenencia",
                "Pertenencias incompatibles implican desigualdad",
            ),
            OutputLanguage::Arabic => text(
                "MembershipContradiction",
                "تناقض الانتماء",
                "قضايا انتماء متعارضة تؤدي إلى عدم المساواة",
            ),
            OutputLanguage::Japanese => text(
                "MembershipContradiction",
                "所属の矛盾",
                "矛盾する所属命題から不等性を導きます",
            ),
            OutputLanguage::Korean => text(
                "MembershipContradiction",
                "소속 모순",
                "상충하는 소속 명제로 불일치를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "MembershipContradiction",
                "Mâu thuẫn thuộc về",
                "Các mệnh đề thuộc về mâu thuẫn suy ra bất đẳng thức",
            ),
        }
    }
}
