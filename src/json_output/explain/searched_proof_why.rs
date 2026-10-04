//! Why-text for non-builtin searched-proof routes (Normal JSON).
//! Call sites pass a stable English kind; this module owns EN/ZH copy including
//! the emitted `type` value (no English tokens under Chinese).

use crate::launch_command::OutputLanguage;

pub struct SearchedProofWhyText {
    pub type_tag: &'static str,
    pub rule_name: String,
    pub message: String,
}

pub fn explain_searched_proof_why(kind: &str, lang: OutputLanguage) -> SearchedProofWhyText {
    let (type_tag, rule_name, message) = match (kind, lang) {
        ("structural_membership", OutputLanguage::English) => (
            "by_structural_membership", "Structural membership",
            "Determine the carrier from stored types and checked constructors without proof search",
        ),
        ("structural_membership", OutputLanguage::ChineseTraditional) => (
            "結構歸屬", "結構歸屬",
            "從已儲存類型和已檢查構造子確定載體，不搜尋證明",
        ),
        ("structural_membership", OutputLanguage::French) => (
            "Appartenance structurelle", "Appartenance structurelle",
            "Déterminer l'ensemble porteur à partir des types stockés et des constructeurs vérifiés, sans recherche de preuve",
        ),
        ("structural_membership", OutputLanguage::Russian) => (
            "Структурная принадлежность", "Структурная принадлежность",
            "Определить носитель по сохранённым типам и проверенным конструкторам без поиска доказательства",
        ),
        ("structural_membership", OutputLanguage::Spanish) => (
            "Pertenencia estructural", "Pertenencia estructural",
            "Determinar el conjunto portador a partir de tipos almacenados y constructores comprobados, sin buscar una prueba",
        ),
        ("structural_membership", OutputLanguage::Arabic) => (
            "انتماء بنيوي", "انتماء بنيوي",
            "تحديد المجموعة الحاملة من الأنواع المخزنة والبنّاءات المتحقق منها دون البحث عن برهان",
        ),
        ("structural_membership", OutputLanguage::Japanese) => (
            "構造による所属", "構造による所属",
            "保存済みの型と検査済みの構成子から台集合を決定し、証明探索を行いません",
        ),
        ("structural_membership", OutputLanguage::Korean) => (
            "구조적 소속", "구조적 소속",
            "저장된 유형과 검사된 생성자로 바탕 집합을 결정하며 증명을 탐색하지 않습니다",
        ),
        ("structural_membership", OutputLanguage::Vietnamese) => (
            "Thuộc về theo cấu trúc", "Thuộc về theo cấu trúc",
            "Xác định tập nền từ các kiểu đã lưu và hàm dựng đã kiểm tra, không tìm kiếm chứng minh",
        ),

        ("structural_membership", OutputLanguage::Chinese) => (
            "结构归属", "结构归属", "读取已存类型和已检查运算的返回类型，不递归搜索证明",
        ),
        ("closed_calculation", OutputLanguage::English) => (
            "by_closed_calculation", "Closed calculation",
            "Exact evaluation of closed expressions without proof search",
        ),
        ("closed_calculation", OutputLanguage::ChineseTraditional) => (
            "封閉計算", "封閉計算",
            "精確計算封閉運算式，不搜尋證明",
        ),
        ("closed_calculation", OutputLanguage::French) => (
            "Calcul fermé", "Calcul fermé",
            "Évaluation exacte des expressions fermées sans recherche de preuve",
        ),
        ("closed_calculation", OutputLanguage::Russian) => (
            "Вычисление замкнутого выражения", "Вычисление замкнутого выражения",
            "Точное вычисление замкнутых выражений без поиска доказательства",
        ),
        ("closed_calculation", OutputLanguage::Spanish) => (
            "Cálculo cerrado", "Cálculo cerrado",
            "Evaluación exacta de expresiones cerradas sin buscar una prueba",
        ),
        ("closed_calculation", OutputLanguage::Arabic) => (
            "حساب تعبير مغلق", "حساب تعبير مغلق",
            "تقييم دقيق للتعبيرات المغلقة دون البحث عن برهان",
        ),
        ("closed_calculation", OutputLanguage::Japanese) => (
            "閉じた式の計算", "閉じた式の計算",
            "閉じた式を正確に評価し、証明探索を行いません",
        ),
        ("closed_calculation", OutputLanguage::Korean) => (
            "닫힌 식 계산", "닫힌 식 계산",
            "닫힌 식을 정확하게 평가하며 증명을 탐색하지 않습니다",
        ),
        ("closed_calculation", OutputLanguage::Vietnamese) => (
            "Tính toán biểu thức đóng", "Tính toán biểu thức đóng",
            "Tính chính xác các biểu thức đóng mà không tìm kiếm chứng minh",
        ),

        ("closed_calculation", OutputLanguage::Chinese) => (
            "封闭计算", "封闭计算",
            "精确计算封闭表达式，不递归搜索证明",
        ),
        ("known_special_property", OutputLanguage::English) => (
            "known_special_property", "Known special property",
            "Verified by matching a definition-time object property and existing evidence",
        ),
        ("known_special_property", OutputLanguage::ChineseTraditional) => (
            "已知特殊性質", "已知特殊性質",
            "匹配物件定義時記錄的性質與已有證據",
        ),
        ("known_special_property", OutputLanguage::French) => (
            "Propriété spéciale connue", "Propriété spéciale connue",
            "Vérifié en faisant correspondre une propriété enregistrée à la définition de l'objet avec les preuves existantes",
        ),
        ("known_special_property", OutputLanguage::Russian) => (
            "Известное особое свойство", "Известное особое свойство",
            "Проверено сопоставлением свойства, записанного при определении объекта, с имеющимся свидетельством",
        ),
        ("known_special_property", OutputLanguage::Spanish) => (
            "Propiedad especial conocida", "Propiedad especial conocida",
            "Verificado al cotejar una propiedad registrada al definir el objeto con la evidencia existente",
        ),
        ("known_special_property", OutputLanguage::Arabic) => (
            "خاصية خاصة معلومة", "خاصية خاصة معلومة",
            "تم التحقق بمطابقة خاصية مسجلة عند تعريف الكائن مع الأدلة الموجودة",
        ),
        ("known_special_property", OutputLanguage::Japanese) => (
            "既知の特殊な性質", "既知の特殊な性質",
            "オブジェクトの定義時に記録された性質と既存の証拠を照合して検証しました",
        ),
        ("known_special_property", OutputLanguage::Korean) => (
            "알려진 특수 성질", "알려진 특수 성질",
            "객체 정의 시 기록된 성질과 기존 증거를 대조하여 검증했습니다",
        ),
        ("known_special_property", OutputLanguage::Vietnamese) => (
            "Tính chất đặc biệt đã biết", "Tính chất đặc biệt đã biết",
            "Đã kiểm chứng bằng cách đối chiếu tính chất ghi khi định nghĩa đối tượng với bằng chứng hiện có",
        ),

        ("known_special_property", OutputLanguage::Chinese) => (
            "已知特殊属性", "已知特殊属性", "匹配对象定义时记录的属性与已有证据",
        ),
        ("builtin_strategy", OutputLanguage::English) => (
            "builtin_strategy",
            "Builtin strategy",
            "Verified by a builtin multi-step strategy",
        ),
        ("builtin_strategy", OutputLanguage::ChineseTraditional) => (
            "內建策略",
            "內建策略",
            "由內建多步策略驗證",
        ),
        ("builtin_strategy", OutputLanguage::French) => (
            "Stratégie intégrée",
            "Stratégie intégrée",
            "Vérifié par une stratégie intégrée à plusieurs étapes",
        ),
        ("builtin_strategy", OutputLanguage::Russian) => (
            "Встроенная стратегия",
            "Встроенная стратегия",
            "Проверено встроенной многошаговой стратегией",
        ),
        ("builtin_strategy", OutputLanguage::Spanish) => (
            "Estrategia incorporada",
            "Estrategia incorporada",
            "Verificado mediante una estrategia incorporada de varios pasos",
        ),
        ("builtin_strategy", OutputLanguage::Arabic) => (
            "استراتيجية مدمجة",
            "استراتيجية مدمجة",
            "تم التحقق باستراتيجية مدمجة متعددة الخطوات",
        ),
        ("builtin_strategy", OutputLanguage::Japanese) => (
            "組み込み戦略",
            "組み込み戦略",
            "組み込みの複数ステップの戦略で検証しました",
        ),
        ("builtin_strategy", OutputLanguage::Korean) => (
            "내장 전략",
            "내장 전략",
            "내장 다단계 전략으로 검증했습니다",
        ),
        ("builtin_strategy", OutputLanguage::Vietnamese) => (
            "Chiến lược tích hợp",
            "Chiến lược tích hợp",
            "Đã kiểm chứng bằng chiến lược tích hợp nhiều bước",
        ),

        ("builtin_strategy", OutputLanguage::Chinese) => {
            ("内置策略", "内置策略", "由内置多步策略验证")
        }
        ("by_definition", OutputLanguage::English) => (
            "by_definition",
            "By definition",
            "Verified by unfolding a definition",
        ),
        ("by_definition", OutputLanguage::ChineseTraditional) => (
            "按定義",
            "按定義",
            "透過展開定義驗證",
        ),
        ("by_definition", OutputLanguage::French) => (
            "Par définition",
            "Par définition",
            "Vérifié en développant une définition",
        ),
        ("by_definition", OutputLanguage::Russian) => (
            "По определению",
            "По определению",
            "Проверено раскрытием определения",
        ),
        ("by_definition", OutputLanguage::Spanish) => (
            "Por definición",
            "Por definición",
            "Verificado al desplegar una definición",
        ),
        ("by_definition", OutputLanguage::Arabic) => (
            "بالتعريف",
            "بالتعريف",
            "تم التحقق بتوسيع تعريف",
        ),
        ("by_definition", OutputLanguage::Japanese) => (
            "定義による証明",
            "定義による証明",
            "定義を展開して検証しました",
        ),
        ("by_definition", OutputLanguage::Korean) => (
            "정의에 의한 증명",
            "정의에 의한 증명",
            "정의를 펼쳐 검증했습니다",
        ),
        ("by_definition", OutputLanguage::Vietnamese) => (
            "Theo định nghĩa",
            "Theo định nghĩa",
            "Đã kiểm chứng bằng cách khai triển định nghĩa",
        ),

        ("by_definition", OutputLanguage::Chinese) => ("按定义", "按定义", "通过展开定义验证"),
        ("known_strategy", OutputLanguage::English) => (
            "known_strategy",
            "Known strategy",
            "Verified by applying a known strategy fact",
        ),
        ("known_strategy", OutputLanguage::ChineseTraditional) => (
            "已知策略",
            "已知策略",
            "套用已知策略命題驗證",
        ),
        ("known_strategy", OutputLanguage::French) => (
            "Stratégie connue",
            "Stratégie connue",
            "Vérifié en appliquant une proposition de stratégie connue",
        ),
        ("known_strategy", OutputLanguage::Russian) => (
            "Известная стратегия",
            "Известная стратегия",
            "Проверено применением известного утверждения стратегии",
        ),
        ("known_strategy", OutputLanguage::Spanish) => (
            "Estrategia conocida",
            "Estrategia conocida",
            "Verificado al aplicar una proposición de estrategia conocida",
        ),
        ("known_strategy", OutputLanguage::Arabic) => (
            "استراتيجية معلومة",
            "استراتيجية معلومة",
            "تم التحقق بتطبيق قضية استراتيجية معلومة",
        ),
        ("known_strategy", OutputLanguage::Japanese) => (
            "既知の戦略",
            "既知の戦略",
            "既知の戦略の命題を適用して検証しました",
        ),
        ("known_strategy", OutputLanguage::Korean) => (
            "알려진 전략",
            "알려진 전략",
            "알려진 전략 명제를 적용하여 검증했습니다",
        ),
        ("known_strategy", OutputLanguage::Vietnamese) => (
            "Chiến lược đã biết",
            "Chiến lược đã biết",
            "Đã kiểm chứng bằng cách áp dụng mệnh đề chiến lược đã biết",
        ),

        ("known_strategy", OutputLanguage::Chinese) => {
            ("已知策略", "已知策略", "应用已知策略事实验证")
        }
        ("builtin_rewrite", OutputLanguage::English) => (
            "builtin_rewrite",
            "Builtin rewrite",
            "Verified by a builtin equality rewrite",
        ),
        ("builtin_rewrite", OutputLanguage::ChineseTraditional) => (
            "內建改寫",
            "內建改寫",
            "由內建等式改寫驗證",
        ),
        ("builtin_rewrite", OutputLanguage::French) => (
            "Réécriture intégrée",
            "Réécriture intégrée",
            "Vérifié par une réécriture d'égalité intégrée",
        ),
        ("builtin_rewrite", OutputLanguage::Russian) => (
            "Встроенное переписывание",
            "Встроенное переписывание",
            "Проверено встроенным переписыванием равенства",
        ),
        ("builtin_rewrite", OutputLanguage::Spanish) => (
            "Reescritura incorporada",
            "Reescritura incorporada",
            "Verificado mediante una reescritura de igualdad incorporada",
        ),
        ("builtin_rewrite", OutputLanguage::Arabic) => (
            "إعادة كتابة مدمجة",
            "إعادة كتابة مدمجة",
            "تم التحقق بإعادة كتابة مساواة مدمجة",
        ),
        ("builtin_rewrite", OutputLanguage::Japanese) => (
            "組み込みの書き換え",
            "組み込みの書き換え",
            "組み込みの等式書き換えで検証しました",
        ),
        ("builtin_rewrite", OutputLanguage::Korean) => (
            "내장 재작성",
            "내장 재작성",
            "내장 등식 재작성으로 검증했습니다",
        ),
        ("builtin_rewrite", OutputLanguage::Vietnamese) => (
            "Viết lại tích hợp",
            "Viết lại tích hợp",
            "Đã kiểm chứng bằng cách viết lại đẳng thức tích hợp",
        ),

        ("builtin_rewrite", OutputLanguage::Chinese) => {
            ("内置改写", "内置改写", "由内置等式改写验证")
        }
        ("known_rewrite", OutputLanguage::English) => (
            "known_rewrite",
            "Known rewrite",
            "Verified by rewriting with a known equality",
        ),
        ("known_rewrite", OutputLanguage::ChineseTraditional) => (
            "已知改寫",
            "已知改寫",
            "用已知等式改寫驗證",
        ),
        ("known_rewrite", OutputLanguage::French) => (
            "Réécriture connue",
            "Réécriture connue",
            "Vérifié en réécrivant avec une égalité connue",
        ),
        ("known_rewrite", OutputLanguage::Russian) => (
            "Переписывание по известному равенству",
            "Переписывание по известному равенству",
            "Проверено переписыванием по известному равенству",
        ),
        ("known_rewrite", OutputLanguage::Spanish) => (
            "Reescritura conocida",
            "Reescritura conocida",
            "Verificado al reescribir con una igualdad conocida",
        ),
        ("known_rewrite", OutputLanguage::Arabic) => (
            "إعادة كتابة معلومة",
            "إعادة كتابة معلومة",
            "تم التحقق بإعادة الكتابة باستخدام مساواة معلومة",
        ),
        ("known_rewrite", OutputLanguage::Japanese) => (
            "既知の書き換え",
            "既知の書き換え",
            "既知の等式で書き換えて検証しました",
        ),
        ("known_rewrite", OutputLanguage::Korean) => (
            "알려진 재작성",
            "알려진 재작성",
            "알려진 등식으로 재작성하여 검증했습니다",
        ),
        ("known_rewrite", OutputLanguage::Vietnamese) => (
            "Viết lại đã biết",
            "Viết lại đã biết",
            "Đã kiểm chứng bằng cách viết lại với đẳng thức đã biết",
        ),

        ("known_rewrite", OutputLanguage::Chinese) => {
            ("已知改写", "已知改写", "用已知等式改写验证")
        }
        ("they_are_the_same", OutputLanguage::English) => (
            "they_are_the_same",
            "Same object",
            "Both sides have identical IR or alpha-equivalent binder structure",
        ),
        ("they_are_the_same", OutputLanguage::ChineseTraditional) => (
            "同一物件",
            "同一物件",
            "兩邊內部表示相同，或繫結參數改名後結構相同",
        ),
        ("they_are_the_same", OutputLanguage::French) => (
            "Même objet",
            "Même objet",
            "Les deux membres ont la même représentation interne ou des structures de liaison alpha-équivalentes",
        ),
        ("they_are_the_same", OutputLanguage::Russian) => (
            "Тот же объект",
            "Тот же объект",
            "Обе части имеют одинаковое внутреннее представление или альфа-эквивалентную структуру связывания",
        ),
        ("they_are_the_same", OutputLanguage::Spanish) => (
            "Mismo objeto",
            "Mismo objeto",
            "Ambos lados tienen la misma representación interna o estructuras de vinculación alfa-equivalentes",
        ),
        ("they_are_the_same", OutputLanguage::Arabic) => (
            "الكائن نفسه",
            "الكائن نفسه",
            "للطرفين التمثيل الداخلي نفسه أو بنية ربط متكافئة ألفا",
        ),
        ("they_are_the_same", OutputLanguage::Japanese) => (
            "同一のオブジェクト",
            "同一のオブジェクト",
            "両辺の内部表現が同じ、または束縛変数の構造がアルファ同値です",
        ),
        ("they_are_the_same", OutputLanguage::Korean) => (
            "동일한 객체",
            "동일한 객체",
            "양변의 내부 표현이 같거나 바인더 구조가 알파 동치입니다",
        ),
        ("they_are_the_same", OutputLanguage::Vietnamese) => (
            "Cùng một đối tượng",
            "Cùng một đối tượng",
            "Hai vế có cùng biểu diễn nội bộ hoặc cấu trúc biến ràng buộc tương đương alpha",
        ),

        ("they_are_the_same", OutputLanguage::Chinese) => (
            "同一对象",
            "同一对象",
            "两边内部表示相同，或绑定参数改名后结构相同",
        ),
        ("equivalence_class", OutputLanguage::English) => (
            "equivalence_class",
            "Equivalence class",
            "Equality follows from stored paths, possibly joined by a checked peer proof",
        ),
        ("equivalence_class", OutputLanguage::ChineseTraditional) => (
            "等價類",
            "等價類",
            "由已儲存的等式路徑證明，必要時以已驗證的成員比較連接",
        ),
        ("equivalence_class", OutputLanguage::French) => (
            "Classe d'équivalence",
            "Classe d'équivalence",
            "L'égalité découle des chemins stockés, éventuellement reliés par une preuve vérifiée entre membres",
        ),
        ("equivalence_class", OutputLanguage::Russian) => (
            "Класс эквивалентности",
            "Класс эквивалентности",
            "Равенство следует из сохранённых путей, при необходимости соединённых проверенным доказательством между элементами",
        ),
        ("equivalence_class", OutputLanguage::Spanish) => (
            "Clase de equivalencia",
            "Clase de equivalencia",
            "La igualdad se deduce de rutas almacenadas, conectadas si hace falta por una prueba comprobada entre miembros",
        ),
        ("equivalence_class", OutputLanguage::Arabic) => (
            "فئة تكافؤ",
            "فئة تكافؤ",
            "تنتج المساواة من المسارات المخزنة، وقد يربطها برهان متحقق منه بين العناصر",
        ),
        ("equivalence_class", OutputLanguage::Japanese) => (
            "同値類",
            "同値類",
            "保存済みの経路から等式を導き、必要に応じて検証済みの要素間の証明で接続します",
        ),
        ("equivalence_class", OutputLanguage::Korean) => (
            "동치류",
            "동치류",
            "저장된 경로에서 등식을 도출하며 필요하면 검증된 원소 간 증명으로 연결합니다",
        ),
        ("equivalence_class", OutputLanguage::Vietnamese) => (
            "Lớp tương đương",
            "Lớp tương đương",
            "Đẳng thức suy ra từ các đường đã lưu, có thể nối bằng chứng minh đã kiểm tra giữa các phần tử",
        ),

        ("equivalence_class", OutputLanguage::Chinese) => {
            ("等价类", "等价类", "由已知等式链证明，必要时用已验证的类成员比较连接两条链")
        }
        ("object_definition", OutputLanguage::English) => (
            "object_definition",
            "Object definition",
            "Equality follows from an object definition",
        ),
        ("object_definition", OutputLanguage::ChineseTraditional) => (
            "物件定義",
            "物件定義",
            "等式由物件定義得出",
        ),
        ("object_definition", OutputLanguage::French) => (
            "Définition d'objet",
            "Définition d'objet",
            "L'égalité découle d'une définition d'objet",
        ),
        ("object_definition", OutputLanguage::Russian) => (
            "Определение объекта",
            "Определение объекта",
            "Равенство следует из определения объекта",
        ),
        ("object_definition", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Definición de objeto",
            "La igualdad se deduce de una definición de objeto",
        ),
        ("object_definition", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "تعريف كائن",
            "تنتج المساواة من تعريف كائن",
        ),
        ("object_definition", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "オブジェクト定義",
            "オブジェクトの定義から等式を導きます",
        ),
        ("object_definition", OutputLanguage::Korean) => (
            "객체 정의",
            "객체 정의",
            "객체 정의에서 등식을 도출합니다",
        ),
        ("object_definition", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Định nghĩa đối tượng",
            "Đẳng thức suy ra từ định nghĩa đối tượng",
        ),

        ("object_definition", OutputLanguage::Chinese) => {
            ("对象定义", "对象定义", "等式由对象定义得出")
        }
        ("matching_one_arg_by_one", OutputLanguage::English) => (
            "matching_one_arg_by_one",
            "Match arguments one-by-one",
            "Function / constructor arguments match pairwise",
        ),
        ("matching_one_arg_by_one", OutputLanguage::ChineseTraditional) => (
            "逐一匹配引數",
            "逐一匹配引數",
            "函數或構造子引數逐一匹配",
        ),
        ("matching_one_arg_by_one", OutputLanguage::French) => (
            "Correspondance des arguments deux à deux",
            "Correspondance des arguments deux à deux",
            "Les arguments de fonction ou de constructeur correspondent deux à deux",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Russian) => (
            "Попарное сопоставление аргументов",
            "Попарное сопоставление аргументов",
            "Аргументы функции или конструктора совпадают попарно",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Spanish) => (
            "Cotejo de argumentos uno a uno",
            "Cotejo de argumentos uno a uno",
            "Los argumentos de función o constructor coinciden por pares",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Arabic) => (
            "مطابقة الوسائط واحدًا واحدًا",
            "مطابقة الوسائط واحدًا واحدًا",
            "تتطابق وسائط الدالة أو البنّاء زوجيًا",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Japanese) => (
            "引数の逐次照合",
            "引数の逐次照合",
            "関数または構成子の引数がそれぞれ一致します",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Korean) => (
            "인수의 개별 대조",
            "인수의 개별 대조",
            "함수 또는 생성자의 인수가 쌍별로 일치합니다",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Vietnamese) => (
            "Đối chiếu từng đối số",
            "Đối chiếu từng đối số",
            "Các đối số của hàm hoặc hàm dựng khớp từng cặp",
        ),

        ("matching_one_arg_by_one", OutputLanguage::Chinese) => {
            ("逐个匹配参数", "逐个匹配参数", "函数或构造子参数逐一匹配")
        }
        ("known_forall_via_symmetry", OutputLanguage::English) => (
            "known_forall_via_symmetry",
            "Forall via symmetry",
            "Verified by a known forall fact after symmetry",
        ),
        ("known_forall_via_symmetry", OutputLanguage::ChineseTraditional) => (
            "對稱後的全稱",
            "對稱後的全稱",
            "對已知全稱命題取對稱後驗證",
        ),
        ("known_forall_via_symmetry", OutputLanguage::French) => (
            "Quantification universelle par symétrie",
            "Quantification universelle par symétrie",
            "Vérifié par une proposition universelle connue après symétrie",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Russian) => (
            "Всеобщность через симметрию",
            "Всеобщность через симметрию",
            "Проверено известным всеобщим утверждением после применения симметрии",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Spanish) => (
            "Cuantificación universal por simetría",
            "Cuantificación universal por simetría",
            "Verificado por una proposición universal conocida tras aplicar simetría",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Arabic) => (
            "تكميم كلي بالتناظر",
            "تكميم كلي بالتناظر",
            "تم التحقق بقضية كلية معلومة بعد تطبيق التناظر",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Japanese) => (
            "対称性を用いた全称命題",
            "対称性を用いた全称命題",
            "既知の全称命題に対称性を適用して検証しました",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Korean) => (
            "대칭성을 통한 전칭 명제",
            "대칭성을 통한 전칭 명제",
            "알려진 전칭 명제에 대칭성을 적용하여 검증했습니다",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Vietnamese) => (
            "Mệnh đề phổ quát qua tính đối xứng",
            "Mệnh đề phổ quát qua tính đối xứng",
            "Đã kiểm chứng bằng mệnh đề phổ quát đã biết sau khi áp dụng tính đối xứng",
        ),

        ("known_forall_via_symmetry", OutputLanguage::Chinese) => (
            "对称后的全称",
            "对称后的全称",
            "对已知全称事实取对称后验证",
        ),
        ("failed", OutputLanguage::English) => ("failed", "Failed", "Verification did not succeed"),
        ("failed", OutputLanguage::ChineseTraditional) => ("失敗", "失敗", "驗證未成功"),
        ("failed", OutputLanguage::French) => ("Échec", "Échec", "La vérification a échoué"),
        ("failed", OutputLanguage::Russian) => ("Неудача", "Неудача", "Проверка не удалась"),
        ("failed", OutputLanguage::Spanish) => ("Fallo", "Fallo", "La verificación no tuvo éxito"),
        ("failed", OutputLanguage::Arabic) => ("فشل", "فشل", "لم ينجح التحقق"),
        ("failed", OutputLanguage::Japanese) => ("失敗", "失敗", "検証に成功しませんでした"),
        ("failed", OutputLanguage::Korean) => ("실패", "실패", "검증에 실패했습니다"),
        ("failed", OutputLanguage::Vietnamese) => ("Thất bại", "Thất bại", "Kiểm chứng không thành công"),

        ("failed", OutputLanguage::Chinese) => ("失败", "失败", "验证未成功"),
        (_, OutputLanguage::English) => (
            "searched_proof",
            "Searched proof",
            "Verified by a searched proof route",
        ),
        (_, OutputLanguage::ChineseTraditional) => (
            "搜尋證明",
            "搜尋證明",
            "由搜尋到的證明路徑驗證",
        ),
        (_, OutputLanguage::French) => (
            "Preuve recherchée",
            "Preuve recherchée",
            "Vérifié par un chemin de preuve trouvé",
        ),
        (_, OutputLanguage::Russian) => (
            "Найденное доказательство",
            "Найденное доказательство",
            "Проверено найденным путём доказательства",
        ),
        (_, OutputLanguage::Spanish) => (
            "Prueba buscada",
            "Prueba buscada",
            "Verificado mediante una ruta de prueba encontrada",
        ),
        (_, OutputLanguage::Arabic) => (
            "برهان تم البحث عنه",
            "برهان تم البحث عنه",
            "تم التحقق بمسار برهان عُثر عليه",
        ),
        (_, OutputLanguage::Japanese) => (
            "探索された証明",
            "探索された証明",
            "探索された証明経路で検証しました",
        ),
        (_, OutputLanguage::Korean) => (
            "탐색된 증명",
            "탐색된 증명",
            "탐색된 증명 경로로 검증했습니다",
        ),
        (_, OutputLanguage::Vietnamese) => (
            "Chứng minh được tìm",
            "Chứng minh được tìm",
            "Đã kiểm chứng bằng đường chứng minh tìm được",
        ),

        (_, OutputLanguage::Chinese) => ("搜索证明", "搜索证明", "由搜索到的证明路径验证"),
    };
    SearchedProofWhyText {
        type_tag,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
