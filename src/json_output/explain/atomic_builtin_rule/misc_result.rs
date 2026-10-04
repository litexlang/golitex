//! Leaf explain for atomic family group `search_atomic_except_equality_fact_proof_by_builtin_rule_result`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    BijectiveFactSearchProofByBuiltinRule,
    CoprimeByComputation,
    CoprimeFactSearchProofByBuiltinRule,
    DvdFactSearchProofByBuiltinRule,
    InjectiveFactSearchProofByBuiltinRule,
    IsChoiceFunctionForFactSearchProofByBuiltinRule,
    NormalAtomicFactSearchProofByBuiltinRule,
    NotBijectiveFactSearchProofByBuiltinRule,
    NotCoprimeByComputation,
    NotCoprimeFactSearchProofByBuiltinRule,
    NotDvdFactSearchProofByBuiltinRule,
    NotInjectiveFactSearchProofByBuiltinRule,
    NotIsCartFactSearchProofByBuiltinRule,
    NotIsChoiceFunctionForFactSearchProofByBuiltinRule,
    NotIsSetFactSearchProofByBuiltinRule,
    NotIsTupleFactSearchProofByBuiltinRule,
    NotNormalAtomicFactSearchProofByBuiltinRule,
    NotPrimeByComputation,
    NotPrimeFactSearchProofByBuiltinRule,
    NotProperSubsetFactSearchProofByBuiltinRule,
    NotProperSupersetFactSearchProofByBuiltinRule,
    NotSurjectiveFactSearchProofByBuiltinRule,
    PrimeByComputation,
    PrimeFactSearchProofByBuiltinRule,
    ProperSubsetFactSearchProofByBuiltinRule,
    ProperSupersetFactSearchProofByBuiltinRule,
    SurjectiveFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl ProperSubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl ProperSupersetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl PrimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::PrimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::PrimeByComputation(_) => None,
        }
    }
}

impl PrimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PrimeByComputation",
            "Prime By Computation",
            "`$prime(n)` for a resolved nonnegative integer prime",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PrimeByComputation",
            "计算素性",
            "由封闭非负整数计算判定素数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PrimeByComputation",
                "計算質數性",
                "對已求值的非負整數判定 `$prime(n)`",
            ),
            OutputLanguage::French => text(
                "PrimeByComputation",
                "Primalité par calcul",
                "Déterminer `$prime(n)` pour un entier non négatif évalué et premier",
            ),
            OutputLanguage::Russian => text(
                "PrimeByComputation",
                "Простота вычислением",
                "Установить `$prime(n)` для вычисленного неотрицательного простого целого",
            ),
            OutputLanguage::Spanish => text(
                "PrimeByComputation",
                "Primalidad por cálculo",
                "Determinar `$prime(n)` para un entero no negativo evaluado y primo",
            ),
            OutputLanguage::Arabic => text(
                "PrimeByComputation",
                "أولية بالحساب",
                "تحديد `$prime(n)` لعدد صحيح غير سالب محسوب وأولي",
            ),
            OutputLanguage::Japanese => text(
                "PrimeByComputation",
                "計算による素数の判定",
                "評価済みの非負整数が素数であることから `$prime(n)` を判定します",
            ),
            OutputLanguage::Korean => text(
                "PrimeByComputation",
                "계산으로 소수 판정",
                "평가된 음이 아닌 정수가 소수임으로 `$prime(n)`을 판정합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PrimeByComputation",
                "Kiểm tra nguyên tố bằng tính toán",
                "Xác định `$prime(n)` cho số nguyên không âm đã tính và là số nguyên tố",
            ),
        }
    }
}

impl CoprimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::CoprimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::CoprimeByComputation(_) => None,
        }
    }
}

impl CoprimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CoprimeByComputation",
            "Coprime By Computation",
            "`$coprime(a, b)` when resolved nonnegative integers",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CoprimeByComputation", "计算互素", "由 gcd 为 1 判定互素")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "CoprimeByComputation",
            "計算互質性",
            "對已求值的非負整數，以 gcd 為 1 判定 `$coprime(a, b)`",
        )
    },
            OutputLanguage::French => {
        text(
            "CoprimeByComputation",
            "Coprimalité par calcul",
            "Déterminer `$coprime(a, b)` par un gcd égal à 1 pour les entiers non négatifs évalués",
        )
    },
            OutputLanguage::Russian => {
        text(
            "CoprimeByComputation",
            "Взаимная простота вычислением",
            "Установить `$coprime(a, b)` по gcd, равному 1, для вычисленных неотрицательных целых",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "CoprimeByComputation",
            "Coprimalidad por cálculo",
            "Determinar `$coprime(a, b)` por gcd igual a 1 para enteros no negativos evaluados",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "CoprimeByComputation",
            "أولية نسبية بالحساب",
            "تحديد `$coprime(a, b)` من gcd يساوي 1 للأعداد الصحيحة غير السالبة المحسوبة",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "CoprimeByComputation",
            "計算による互いに素の判定",
            "評価済みの非負整数について gcd が 1 であることから `$coprime(a, b)` を判定します",
        )
    },
            OutputLanguage::Korean => {
        text(
            "CoprimeByComputation",
            "계산으로 서로소 판정",
            "평가된 음이 아닌 정수의 gcd가 1임으로 `$coprime(a, b)`를 판정합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "CoprimeByComputation",
            "Kiểm tra nguyên tố cùng nhau bằng tính toán",
            "Xác định `$coprime(a, b)` bằng gcd bằng 1 cho các số nguyên không âm đã tính",
        )
    },

        }
    }
}

impl DvdFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl InjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl SurjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl BijectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl IsChoiceFunctionForFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NormalAtomicFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotNormalAtomicFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsCartFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsTupleFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotProperSubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotProperSupersetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotPrimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::NotPrimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::NotPrimeByComputation(_) => None,
        }
    }
}

impl NotPrimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NotPrimeByComputation",
            "Not Prime By Computation",
            "`not $prime(n)` for a resolved nonnegative non-prime",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NotPrimeByComputation",
            "计算非素性",
            "由封闭非负整数计算判定非素数",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "NotPrimeByComputation",
            "計算非質數性",
            "對已求值的非負非質數判定 `not $prime(n)`",
        )
    },
            OutputLanguage::French => {
        text(
            "NotPrimeByComputation",
            "Non-primalité par calcul",
            "Déterminer `not $prime(n)` pour un entier non négatif évalué et non premier",
        )
    },
            OutputLanguage::Russian => {
        text(
            "NotPrimeByComputation",
            "Составность или непростота вычислением",
            "Установить `not $prime(n)` для вычисленного неотрицательного непростого целого",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "NotPrimeByComputation",
            "No primalidad por cálculo",
            "Determinar `not $prime(n)` para un entero no negativo evaluado y no primo",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "NotPrimeByComputation",
            "عدم الأولية بالحساب",
            "تحديد `not $prime(n)` لعدد صحيح غير سالب محسوب وغير أولي",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "NotPrimeByComputation",
            "計算による非素数の判定",
            "評価済みの非負整数が素数でないことから `not $prime(n)` を判定します",
        )
    },
            OutputLanguage::Korean => {
        text(
            "NotPrimeByComputation",
            "계산으로 비소수 판정",
            "평가된 음이 아닌 정수가 소수가 아님으로 `not $prime(n)`을 판정합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "NotPrimeByComputation",
            "Kiểm tra không nguyên tố bằng tính toán",
            "Xác định `not $prime(n)` cho số nguyên không âm đã tính và không phải số nguyên tố",
        )
    },

        }
    }
}

impl NotCoprimeFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::NotCoprimeByComputation(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::NotCoprimeByComputation(_) => None,
        }
    }
}

impl NotCoprimeByComputation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NotCoprimeByComputation",
            "Not Coprime By Computation",
            "`not $coprime(a, b)` when resolved nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("NotCoprimeByComputation", "计算非互素", "由 gcd 判定非互素")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NotCoprimeByComputation",
                "計算非互質性",
                "對已求值的非負整數，以 gcd 判定 `not $coprime(a, b)`",
            ),
            OutputLanguage::French => text(
                "NotCoprimeByComputation",
                "Non-coprimalité par calcul",
                "Déterminer `not $coprime(a, b)` par le gcd des entiers non négatifs évalués",
            ),
            OutputLanguage::Russian => text(
                "NotCoprimeByComputation",
                "Отсутствие взаимной простоты вычислением",
                "Установить `not $coprime(a, b)` по gcd вычисленных неотрицательных целых",
            ),
            OutputLanguage::Spanish => text(
                "NotCoprimeByComputation",
                "No coprimalidad por cálculo",
                "Determinar `not $coprime(a, b)` por el gcd de enteros no negativos evaluados",
            ),
            OutputLanguage::Arabic => text(
                "NotCoprimeByComputation",
                "عدم الأولية النسبية بالحساب",
                "تحديد `not $coprime(a, b)` من gcd للأعداد الصحيحة غير السالبة المحسوبة",
            ),
            OutputLanguage::Japanese => text(
                "NotCoprimeByComputation",
                "計算による非互いに素の判定",
                "評価済みの非負整数の gcd から `not $coprime(a, b)` を判定します",
            ),
            OutputLanguage::Korean => text(
                "NotCoprimeByComputation",
                "계산으로 서로소가 아님을 판정",
                "평가된 음이 아닌 정수의 gcd로 `not $coprime(a, b)`를 판정합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NotCoprimeByComputation",
                "Kiểm tra không nguyên tố cùng nhau bằng tính toán",
                "Xác định `not $coprime(a, b)` bằng gcd của các số nguyên không âm đã tính",
            ),
        }
    }
}

impl NotDvdFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotInjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotSurjectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotBijectiveFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}

impl NotIsChoiceFunctionForFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        let _ = (self, lang);
        unreachable!("empty atomic builtin family has no proof variants")
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        let _ = self;
        unreachable!("empty atomic builtin family has no proof variants")
    }
}
