//! Localized why-text for statement kinds and compound facts.
//! All localized statement copy lives here (not in execute/).

use crate::launch_command::OutputLanguage;

pub struct StmtWhyText {
    pub type_tag: &'static str,
    pub rule_name: String,
    pub message: String,
}

pub fn explain_define_obj_why(kind: &str, lang: OutputLanguage) -> StmtWhyText {
    explain_stmt_kind(kind, lang)
}

pub fn explain_stmt_kind(kind: &str, lang: OutputLanguage) -> StmtWhyText {
    let (type_tag, rule_name, message) = match (kind, lang) {
        // define-obj
        ("let", OutputLanguage::English) => (
            "define_obj",
            "Let binding",
            "Bind a name to a well-defined value",
        ),
        ("let", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "賦值定義", "把名稱繫結到良定的值")
        }
        ("let", OutputLanguage::French) => (
            "Définition d'objet",
            "Liaison let",
            "Lier un nom à une valeur bien définie",
        ),
        ("let", OutputLanguage::Russian) => (
            "Определение объекта",
            "Связывание let",
            "Связать имя с корректно определённым значением",
        ),
        ("let", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Vinculación let",
            "Vincular un nombre a un valor bien definido",
        ),
        ("let", OutputLanguage::Arabic) => ("تعريف كائن", "ربط let", "ربط اسم بقيمة حسنة التعريف"),
        ("let", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "let による束縛",
            "名前を適切に定義された値に束縛します",
        ),
        ("let", OutputLanguage::Korean) => (
            "객체 정의",
            "let 바인딩",
            "이름을 타당하게 정의된 값에 바인딩합니다",
        ),
        ("let", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Liên kết let",
            "Liên kết tên với một giá trị xác định tốt",
        ),

        ("let", OutputLanguage::Chinese) => ("定义对象", "赋值定义", "把名字绑定到一个良定的值"),
        ("have_in_nonempty", OutputLanguage::English) => (
            "define_obj",
            "Have from nonempty set",
            "Introduce an object from a nonempty carrier / parameter type",
        ),
        ("have_in_nonempty", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "從非空集合引入", "從非空載體或參數類型引入物件")
        }
        ("have_in_nonempty", OutputLanguage::French) => (
            "Définition d'objet",
            "Introduction depuis un ensemble non vide",
            "Introduire un objet d'un ensemble porteur ou type de paramètre non vide",
        ),
        ("have_in_nonempty", OutputLanguage::Russian) => (
            "Определение объекта",
            "Введение из непустого множества",
            "Ввести объект из непустого носителя или типа параметра",
        ),
        ("have_in_nonempty", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Introducción desde conjunto no vacío",
            "Introducir un objeto de un conjunto portador o tipo de parámetro no vacío",
        ),
        ("have_in_nonempty", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "إدخال من مجموعة غير خالية",
            "إدخال كائن من مجموعة حاملة أو نوع معامل غير خالٍ",
        ),
        ("have_in_nonempty", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "空でない集合からの導入",
            "空でない台集合またはパラメータ型からオブジェクトを導入します",
        ),
        ("have_in_nonempty", OutputLanguage::Korean) => (
            "객체 정의",
            "공집합이 아닌 집합에서 도입",
            "공집합이 아닌 바탕 집합 또는 매개변수 유형에서 객체를 도입합니다",
        ),
        ("have_in_nonempty", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Đưa vào từ tập không rỗng",
            "Đưa vào đối tượng từ tập nền hoặc kiểu tham số không rỗng",
        ),

        ("have_in_nonempty", OutputLanguage::Chinese) => {
            ("定义对象", "从非空集合引入", "从非空载体或参数类型引入对象")
        }
        ("have_equal", OutputLanguage::English) => (
            "define_obj",
            "Have with equality",
            "Introduce an object equal to a given well-defined value",
        ),
        ("have_equal", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "帶等式的 have", "引入與給定良定值相等的物件")
        }
        ("have_equal", OutputLanguage::French) => (
            "Définition d'objet",
            "Introduction avec égalité",
            "Introduire un objet égal à une valeur donnée bien définie",
        ),
        ("have_equal", OutputLanguage::Russian) => (
            "Определение объекта",
            "Введение с равенством",
            "Ввести объект, равный заданному корректно определённому значению",
        ),
        ("have_equal", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Introducción con igualdad",
            "Introducir un objeto igual a un valor dado bien definido",
        ),
        ("have_equal", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "إدخال مع مساواة",
            "إدخال كائن يساوي قيمة معطاة حسنة التعريف",
        ),
        ("have_equal", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "等式を伴う have",
            "与えられた適切に定義された値に等しいオブジェクトを導入します",
        ),
        ("have_equal", OutputLanguage::Korean) => (
            "객체 정의",
            "등식을 포함한 have",
            "주어진 타당하게 정의된 값과 같은 객체를 도입합니다",
        ),
        ("have_equal", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "have với đẳng thức",
            "Đưa vào đối tượng bằng một giá trị xác định tốt đã cho",
        ),

        ("have_equal", OutputLanguage::Chinese) => {
            ("定义对象", "带等式的 have", "引入与给定良定值相等的对象")
        }
        ("have_by_exist", OutputLanguage::English) => (
            "define_obj",
            "Have by existence",
            "Introduce objects from a proved existential fact",
        ),
        ("have_by_exist", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "由存在性引入", "從已證明的存在命題引入物件")
        }
        ("have_by_exist", OutputLanguage::French) => (
            "Définition d'objet",
            "Introduction par existence",
            "Introduire des objets depuis une proposition existentielle prouvée",
        ),
        ("have_by_exist", OutputLanguage::Russian) => (
            "Определение объекта",
            "Введение по существованию",
            "Ввести объекты из доказанного утверждения существования",
        ),
        ("have_by_exist", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Introducción por existencia",
            "Introducir objetos de una proposición existencial demostrada",
        ),
        ("have_by_exist", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "إدخال بالوجود",
            "إدخال كائنات من قضية وجودية مثبتة",
        ),
        ("have_by_exist", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "存在による導入",
            "証明済みの存在命題からオブジェクトを導入します",
        ),
        ("have_by_exist", OutputLanguage::Korean) => (
            "객체 정의",
            "존재에 의한 도입",
            "증명된 존재 명제에서 객체를 도입합니다",
        ),
        ("have_by_exist", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Đưa vào theo sự tồn tại",
            "Đưa vào đối tượng từ mệnh đề tồn tại đã chứng minh",
        ),

        ("have_by_exist", OutputLanguage::Chinese) => {
            ("定义对象", "由存在性引入", "由已证明的存在事实引入对象")
        }
        ("obtain_exist", OutputLanguage::English) => (
            "define_obj",
            "Obtain from exist",
            "Obtain objects from a known existential fact",
        ),
        ("obtain_exist", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "從存在命題取出", "從已知存在命題取出物件")
        }
        ("obtain_exist", OutputLanguage::French) => (
            "Définition d'objet",
            "Extraction d'une proposition existentielle",
            "Obtenir des objets d'une proposition existentielle connue",
        ),
        ("obtain_exist", OutputLanguage::Russian) => (
            "Определение объекта",
            "Получение из утверждения существования",
            "Получить объекты из известного утверждения существования",
        ),
        ("obtain_exist", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Obtención de proposición existencial",
            "Obtener objetos de una proposición existencial conocida",
        ),
        ("obtain_exist", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "استخراج من قضية وجودية",
            "استخراج كائنات من قضية وجودية معلومة",
        ),
        ("obtain_exist", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "存在命題からの取得",
            "既知の存在命題からオブジェクトを取得します",
        ),
        ("obtain_exist", OutputLanguage::Korean) => (
            "객체 정의",
            "존재 명제에서 획득",
            "알려진 존재 명제에서 객체를 얻습니다",
        ),
        ("obtain_exist", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Lấy từ mệnh đề tồn tại",
            "Lấy đối tượng từ mệnh đề tồn tại đã biết",
        ),

        ("obtain_exist", OutputLanguage::Chinese) => {
            ("定义对象", "从存在事实取出", "从已知存在事实取出对象")
        }
        ("obtain_atomic", OutputLanguage::English) => (
            "define_obj",
            "Obtain from atomic",
            "Obtain an object from a known atomic fact",
        ),
        ("obtain_atomic", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "從原子命題取出", "從已知原子命題取出物件")
        }
        ("obtain_atomic", OutputLanguage::French) => (
            "Définition d'objet",
            "Extraction d'une proposition atomique",
            "Obtenir un objet d'une proposition atomique connue",
        ),
        ("obtain_atomic", OutputLanguage::Russian) => (
            "Определение объекта",
            "Получение из атомарного утверждения",
            "Получить объект из известного атомарного утверждения",
        ),
        ("obtain_atomic", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Obtención de proposición atómica",
            "Obtener un objeto de una proposición atómica conocida",
        ),
        ("obtain_atomic", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "استخراج من قضية ذرية",
            "استخراج كائن من قضية ذرية معلومة",
        ),
        ("obtain_atomic", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "原子命題からの取得",
            "既知の原子命題からオブジェクトを取得します",
        ),
        ("obtain_atomic", OutputLanguage::Korean) => (
            "객체 정의",
            "원자 명제에서 획득",
            "알려진 원자 명제에서 객체를 얻습니다",
        ),
        ("obtain_atomic", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Lấy từ mệnh đề nguyên tử",
            "Lấy đối tượng từ mệnh đề nguyên tử đã biết",
        ),

        ("obtain_atomic", OutputLanguage::Chinese) => {
            ("定义对象", "从原子事实取出", "从已知原子事实取出对象")
        }
        ("have_by_preimage", OutputLanguage::English) => (
            "define_obj",
            "Have by preimage",
            "Introduce a preimage object for a function value",
        ),
        ("have_by_preimage", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "由原像引入", "為函數值引入原像物件")
        }
        ("have_by_preimage", OutputLanguage::French) => (
            "Définition d'objet",
            "Introduction par antécédent",
            "Introduire un antécédent d'une valeur de fonction",
        ),
        ("have_by_preimage", OutputLanguage::Russian) => (
            "Определение объекта",
            "Введение через прообраз",
            "Ввести прообраз значения функции",
        ),
        ("have_by_preimage", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Introducción por preimagen",
            "Introducir una preimagen de un valor de función",
        ),
        ("have_by_preimage", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "إدخال بالصورة العكسية",
            "إدخال كائن صورة عكسية لقيمة دالة",
        ),
        ("have_by_preimage", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "逆像による導入",
            "関数値の逆像となるオブジェクトを導入します",
        ),
        ("have_by_preimage", OutputLanguage::Korean) => (
            "객체 정의",
            "원상에 의한 도입",
            "함숫값의 원상 객체를 도입합니다",
        ),
        ("have_by_preimage", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Đưa vào theo ảnh ngược",
            "Đưa vào đối tượng ảnh ngược của một giá trị hàm",
        ),

        ("have_by_preimage", OutputLanguage::Chinese) => {
            ("定义对象", "由原像引入", "为函数值引入原像对象")
        }
        ("have_by_replacement", OutputLanguage::English) => (
            "define_obj",
            "Have by replacement",
            "Introduce an image set via the axiom of replacement",
        ),
        ("have_by_replacement", OutputLanguage::ChineseTraditional) => {
            ("定義物件", "由替換公理引入", "以替換公理引入像集")
        }
        ("have_by_replacement", OutputLanguage::French) => (
            "Définition d'objet",
            "Introduction par remplacement",
            "Introduire un ensemble image par l'axiome de remplacement",
        ),
        ("have_by_replacement", OutputLanguage::Russian) => (
            "Определение объекта",
            "Введение по аксиоме замены",
            "Ввести образ множества по аксиоме замены",
        ),
        ("have_by_replacement", OutputLanguage::Spanish) => (
            "Definición de objeto",
            "Introducción por reemplazo",
            "Introducir un conjunto imagen mediante el axioma de reemplazo",
        ),
        ("have_by_replacement", OutputLanguage::Arabic) => (
            "تعريف كائن",
            "إدخال بالاستبدال",
            "إدخال مجموعة صورة باستخدام مسلمة الاستبدال",
        ),
        ("have_by_replacement", OutputLanguage::Japanese) => (
            "オブジェクト定義",
            "置換公理による導入",
            "置換公理によって像集合を導入します",
        ),
        ("have_by_replacement", OutputLanguage::Korean) => (
            "객체 정의",
            "치환 공리에 의한 도입",
            "치환 공리로 상 집합을 도입합니다",
        ),
        ("have_by_replacement", OutputLanguage::Vietnamese) => (
            "Định nghĩa đối tượng",
            "Đưa vào theo tiên đề thay thế",
            "Đưa vào tập ảnh bằng tiên đề thay thế",
        ),

        ("have_by_replacement", OutputLanguage::Chinese) => {
            ("定义对象", "由替换公理引入", "用替换公理引入像集")
        }

        // have fn
        ("have_fn_equal", OutputLanguage::English) => (
            "define_fn",
            "Have function equal",
            "Define a named function equal to an anonymous function",
        ),
        ("have_fn_equal", OutputLanguage::ChineseTraditional) => {
            ("定義函數", "以等式定義函數", "以匿名函數定義具名函數")
        }
        ("have_fn_equal", OutputLanguage::French) => (
            "Définition de fonction",
            "Définition de fonction par égalité",
            "Définir une fonction nommée égale à une fonction anonyme",
        ),
        ("have_fn_equal", OutputLanguage::Russian) => (
            "Определение функции",
            "Определение функции равенством",
            "Определить именованную функцию, равную анонимной",
        ),
        ("have_fn_equal", OutputLanguage::Spanish) => (
            "Definición de función",
            "Definición de función por igualdad",
            "Definir una función con nombre igual a una función anónima",
        ),
        ("have_fn_equal", OutputLanguage::Arabic) => (
            "تعريف دالة",
            "تعريف دالة بالمساواة",
            "تعريف دالة مسماة تساوي دالة مجهولة الاسم",
        ),
        ("have_fn_equal", OutputLanguage::Japanese) => (
            "関数定義",
            "等式による関数定義",
            "無名関数に等しい名前付き関数を定義します",
        ),
        ("have_fn_equal", OutputLanguage::Korean) => (
            "함수 정의",
            "등식에 의한 함수 정의",
            "익명 함수와 같은 이름 있는 함수를 정의합니다",
        ),
        ("have_fn_equal", OutputLanguage::Vietnamese) => (
            "Định nghĩa hàm",
            "Định nghĩa hàm bằng đẳng thức",
            "Định nghĩa hàm có tên bằng một hàm ẩn danh",
        ),

        ("have_fn_equal", OutputLanguage::Chinese) => {
            ("定义函数", "定义函数（等式）", "用匿名函数定义具名函数")
        }
        ("have_fn_cases", OutputLanguage::English) => (
            "define_fn",
            "Have function by cases",
            "Define a function by case-by-case equalities",
        ),
        ("have_fn_cases", OutputLanguage::ChineseTraditional) => {
            ("定義函數", "分情況定義函數", "以分情況等式定義函數")
        }
        ("have_fn_cases", OutputLanguage::French) => (
            "Définition de fonction",
            "Définition de fonction par cas",
            "Définir une fonction par des égalités selon les cas",
        ),
        ("have_fn_cases", OutputLanguage::Russian) => (
            "Определение функции",
            "Определение функции по случаям",
            "Определить функцию равенствами по отдельным случаям",
        ),
        ("have_fn_cases", OutputLanguage::Spanish) => (
            "Definición de función",
            "Definición de función por casos",
            "Definir una función mediante igualdades por casos",
        ),
        ("have_fn_cases", OutputLanguage::Arabic) => (
            "تعريف دالة",
            "تعريف دالة بالحالات",
            "تعريف دالة بمساواة لكل حالة",
        ),
        ("have_fn_cases", OutputLanguage::Japanese) => (
            "関数定義",
            "場合分けによる関数定義",
            "場合ごとの等式で関数を定義します",
        ),
        ("have_fn_cases", OutputLanguage::Korean) => (
            "함수 정의",
            "경우에 따른 함수 정의",
            "경우별 등식으로 함수를 정의합니다",
        ),
        ("have_fn_cases", OutputLanguage::Vietnamese) => (
            "Định nghĩa hàm",
            "Định nghĩa hàm theo trường hợp",
            "Định nghĩa hàm bằng đẳng thức cho từng trường hợp",
        ),

        ("have_fn_cases", OutputLanguage::Chinese) => {
            ("定义函数", "分情况定义函数", "用分情况等式定义函数")
        }
        ("have_fn_forall_exist_unique", OutputLanguage::English) => (
            "define_fn",
            "Have function by unique existence",
            "Define a function from a forall-exist!-unique property",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::ChineseTraditional) => (
            "定義函數",
            "由唯一存在性定義函數",
            "以 forall-exist! 唯一存在性定義函數",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::French) => (
            "Définition de fonction",
            "Définition de fonction par existence unique",
            "Définir une fonction à partir d'une propriété forall-exist! d'existence unique",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Russian) => (
            "Определение функции",
            "Определение функции по единственности существования",
            "Определить функцию из свойства forall-exist! единственного существования",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Spanish) => (
            "Definición de función",
            "Definición de función por existencia única",
            "Definir una función a partir de una propiedad forall-exist! de existencia única",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Arabic) => (
            "تعريف دالة",
            "تعريف دالة بالوجود الوحيد",
            "تعريف دالة من خاصية forall-exist! للوجود الوحيد",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Japanese) => (
            "関数定義",
            "一意な存在による関数定義",
            "forall-exist! の一意存在の性質から関数を定義します",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Korean) => (
            "함수 정의",
            "유일한 존재에 의한 함수 정의",
            "forall-exist! 유일 존재 성질로 함수를 정의합니다",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Vietnamese) => (
            "Định nghĩa hàm",
            "Định nghĩa hàm theo tồn tại duy nhất",
            "Định nghĩa hàm từ tính chất tồn tại duy nhất forall-exist!",
        ),

        ("have_fn_forall_exist_unique", OutputLanguage::Chinese) => (
            "定义函数",
            "由唯一存在定义函数",
            "由全称唯一存在性质定义函数",
        ),
        ("have_fn_induc", OutputLanguage::English) => (
            "define_fn",
            "Have function by induction",
            "Define a function by induction on naturals",
        ),
        ("have_fn_induc", OutputLanguage::ChineseTraditional) => {
            ("定義函數", "以歸納法定義函數", "以自然數歸納法定義函數")
        }
        ("have_fn_induc", OutputLanguage::French) => (
            "Définition de fonction",
            "Définition de fonction par induction",
            "Définir une fonction par induction sur les naturels",
        ),
        ("have_fn_induc", OutputLanguage::Russian) => (
            "Определение функции",
            "Определение функции индукцией",
            "Определить функцию индукцией по натуральным числам",
        ),
        ("have_fn_induc", OutputLanguage::Spanish) => (
            "Definición de función",
            "Definición de función por inducción",
            "Definir una función por inducción en los naturales",
        ),
        ("have_fn_induc", OutputLanguage::Arabic) => (
            "تعريف دالة",
            "تعريف دالة بالاستقراء",
            "تعريف دالة بالاستقراء على الأعداد الطبيعية",
        ),
        ("have_fn_induc", OutputLanguage::Japanese) => (
            "関数定義",
            "帰納法による関数定義",
            "自然数上の帰納法で関数を定義します",
        ),
        ("have_fn_induc", OutputLanguage::Korean) => (
            "함수 정의",
            "귀납법에 의한 함수 정의",
            "자연수에 대한 귀납법으로 함수를 정의합니다",
        ),
        ("have_fn_induc", OutputLanguage::Vietnamese) => (
            "Định nghĩa hàm",
            "Định nghĩa hàm bằng quy nạp",
            "Định nghĩa hàm bằng quy nạp trên số tự nhiên",
        ),

        ("have_fn_induc", OutputLanguage::Chinese) => {
            ("定义函数", "归纳定义函数", "对自然数归纳定义函数")
        }

        // definitions
        ("def_prop", OutputLanguage::English) => {
            ("definition", "Define prop", "Define a predicate")
        }
        ("def_prop", OutputLanguage::ChineseTraditional) => ("定義", "定義命題", "定義一個謂詞"),
        ("def_prop", OutputLanguage::French) => (
            "Définition",
            "Définition de prédicat",
            "Définir un prédicat",
        ),
        ("def_prop", OutputLanguage::Russian) => (
            "Определение",
            "Определение предиката",
            "Определить предикат",
        ),
        ("def_prop", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de predicado",
            "Definir un predicado",
        ),
        ("def_prop", OutputLanguage::Arabic) => ("تعريف", "تعريف محمول", "تعريف محمول"),
        ("def_prop", OutputLanguage::Japanese) => ("定義", "述語の定義", "述語を定義します"),
        ("def_prop", OutputLanguage::Korean) => ("정의", "술어 정의", "술어를 정의합니다"),
        ("def_prop", OutputLanguage::Vietnamese) => {
            ("Định nghĩa", "Định nghĩa vị từ", "Định nghĩa một vị từ")
        }

        ("def_prop", OutputLanguage::Chinese) => ("定义", "定义命题", "定义一个谓词"),
        ("def_abstract_prop", OutputLanguage::English) => (
            "definition",
            "Define abstract prop",
            "Declare an abstract predicate",
        ),
        ("def_abstract_prop", OutputLanguage::ChineseTraditional) => {
            ("定義", "定義抽象命題", "宣告抽象謂詞")
        }
        ("def_abstract_prop", OutputLanguage::French) => (
            "Définition",
            "Définition de prédicat abstrait",
            "Déclarer un prédicat abstrait",
        ),
        ("def_abstract_prop", OutputLanguage::Russian) => (
            "Определение",
            "Определение абстрактного предиката",
            "Объявить абстрактный предикат",
        ),
        ("def_abstract_prop", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de predicado abstracto",
            "Declarar un predicado abstracto",
        ),
        ("def_abstract_prop", OutputLanguage::Arabic) => {
            ("تعريف", "تعريف محمول مجرد", "إعلان محمول مجرد")
        }
        ("def_abstract_prop", OutputLanguage::Japanese) => {
            ("定義", "抽象述語の定義", "抽象述語を宣言します")
        }
        ("def_abstract_prop", OutputLanguage::Korean) => {
            ("정의", "추상 술어 정의", "추상 술어를 선언합니다")
        }
        ("def_abstract_prop", OutputLanguage::Vietnamese) => (
            "Định nghĩa",
            "Định nghĩa vị từ trừu tượng",
            "Khai báo vị từ trừu tượng",
        ),

        ("def_abstract_prop", OutputLanguage::Chinese) => {
            ("定义", "定义抽象命题", "声明一个抽象谓词")
        }
        ("def_struct", OutputLanguage::English) => {
            ("definition", "Define struct", "Define a structure type")
        }
        ("def_struct", OutputLanguage::ChineseTraditional) => ("定義", "定義結構", "定義結構類型"),
        ("def_struct", OutputLanguage::French) => (
            "Définition",
            "Définition de structure",
            "Définir un type de structure",
        ),
        ("def_struct", OutputLanguage::Russian) => (
            "Определение",
            "Определение структуры",
            "Определить структурный тип",
        ),
        ("def_struct", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de estructura",
            "Definir un tipo de estructura",
        ),
        ("def_struct", OutputLanguage::Arabic) => ("تعريف", "تعريف بنية", "تعريف نوع بنية"),
        ("def_struct", OutputLanguage::Japanese) => ("定義", "構造の定義", "構造型を定義します"),
        ("def_struct", OutputLanguage::Korean) => ("정의", "구조 정의", "구조 유형을 정의합니다"),
        ("def_struct", OutputLanguage::Vietnamese) => (
            "Định nghĩa",
            "Định nghĩa cấu trúc",
            "Định nghĩa một kiểu cấu trúc",
        ),

        ("def_struct", OutputLanguage::Chinese) => ("定义", "定义结构", "定义一个结构类型"),
        ("def_template", OutputLanguage::English) => (
            "definition",
            "Define template",
            "Define a reusable template",
        ),
        ("def_template", OutputLanguage::ChineseTraditional) => {
            ("定義", "定義範本", "定義可重用範本")
        }
        ("def_template", OutputLanguage::French) => (
            "Définition",
            "Définition de modèle",
            "Définir un modèle réutilisable",
        ),
        ("def_template", OutputLanguage::Russian) => (
            "Определение",
            "Определение шаблона",
            "Определить повторно используемый шаблон",
        ),
        ("def_template", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de plantilla",
            "Definir una plantilla reutilizable",
        ),
        ("def_template", OutputLanguage::Arabic) => {
            ("تعريف", "تعريف قالب", "تعريف قالب قابل لإعادة الاستخدام")
        }
        ("def_template", OutputLanguage::Japanese) => (
            "定義",
            "テンプレートの定義",
            "再利用可能なテンプレートを定義します",
        ),
        ("def_template", OutputLanguage::Korean) => {
            ("정의", "템플릿 정의", "재사용 가능한 템플릿을 정의합니다")
        }
        ("def_template", OutputLanguage::Vietnamese) => (
            "Định nghĩa",
            "Định nghĩa mẫu",
            "Định nghĩa mẫu có thể tái sử dụng",
        ),

        ("def_template", OutputLanguage::Chinese) => ("定义", "定义模板", "定义可复用模板"),
        ("def_algo_cases", OutputLanguage::English) => (
            "definition",
            "Define algo by cases",
            "Define an algorithm by cases",
        ),
        ("def_algo_cases", OutputLanguage::ChineseTraditional) => {
            ("定義", "分情況定義演算法", "以分情況方式定義演算法")
        }
        ("def_algo_cases", OutputLanguage::French) => (
            "Définition",
            "Définition d'algorithme par cas",
            "Définir un algorithme par cas",
        ),
        ("def_algo_cases", OutputLanguage::Russian) => (
            "Определение",
            "Определение алгоритма по случаям",
            "Определить алгоритм по случаям",
        ),
        ("def_algo_cases", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de algoritmo por casos",
            "Definir un algoritmo por casos",
        ),
        ("def_algo_cases", OutputLanguage::Arabic) => {
            ("تعريف", "تعريف خوارزمية بالحالات", "تعريف خوارزمية بالحالات")
        }
        ("def_algo_cases", OutputLanguage::Japanese) => (
            "定義",
            "場合分けによるアルゴリズム定義",
            "場合分けでアルゴリズムを定義します",
        ),
        ("def_algo_cases", OutputLanguage::Korean) => (
            "정의",
            "경우에 따른 알고리즘 정의",
            "경우에 따라 알고리즘을 정의합니다",
        ),
        ("def_algo_cases", OutputLanguage::Vietnamese) => (
            "Định nghĩa",
            "Định nghĩa thuật toán theo trường hợp",
            "Định nghĩa thuật toán theo từng trường hợp",
        ),

        ("def_algo_cases", OutputLanguage::Chinese) => {
            ("定义", "分情况定义算法", "用分情况定义算法")
        }
        ("def_algo_induc", OutputLanguage::English) => (
            "definition",
            "Define algo by induction",
            "Define an algorithm by induction",
        ),
        ("def_algo_induc", OutputLanguage::ChineseTraditional) => {
            ("定義", "歸納定義演算法", "以歸納法定義演算法")
        }
        ("def_algo_induc", OutputLanguage::French) => (
            "Définition",
            "Définition d'algorithme par induction",
            "Définir un algorithme par induction",
        ),
        ("def_algo_induc", OutputLanguage::Russian) => (
            "Определение",
            "Определение алгоритма индукцией",
            "Определить алгоритм индукцией",
        ),
        ("def_algo_induc", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de algoritmo por inducción",
            "Definir un algoritmo por inducción",
        ),
        ("def_algo_induc", OutputLanguage::Arabic) => (
            "تعريف",
            "تعريف خوارزمية بالاستقراء",
            "تعريف خوارزمية بالاستقراء",
        ),
        ("def_algo_induc", OutputLanguage::Japanese) => (
            "定義",
            "帰納法によるアルゴリズム定義",
            "帰納法でアルゴリズムを定義します",
        ),
        ("def_algo_induc", OutputLanguage::Korean) => (
            "정의",
            "귀납법에 의한 알고리즘 정의",
            "귀납법으로 알고리즘을 정의합니다",
        ),
        ("def_algo_induc", OutputLanguage::Vietnamese) => (
            "Định nghĩa",
            "Định nghĩa thuật toán bằng quy nạp",
            "Định nghĩa thuật toán bằng quy nạp",
        ),

        ("def_algo_induc", OutputLanguage::Chinese) => ("定义", "归纳定义算法", "用归纳定义算法"),
        ("def_thm", OutputLanguage::English) => {
            ("definition", "Define theorem", "Record a theorem")
        }
        ("def_thm", OutputLanguage::ChineseTraditional) => ("定義", "定義定理", "記錄定理"),
        ("def_thm", OutputLanguage::French) => (
            "Définition",
            "Définition de théorème",
            "Enregistrer un théorème",
        ),
        ("def_thm", OutputLanguage::Russian) => {
            ("Определение", "Определение теоремы", "Записать теорему")
        }
        ("def_thm", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de teorema",
            "Registrar un teorema",
        ),
        ("def_thm", OutputLanguage::Arabic) => ("تعريف", "تعريف مبرهنة", "تسجيل مبرهنة"),
        ("def_thm", OutputLanguage::Japanese) => ("定義", "定理の定義", "定理を記録します"),
        ("def_thm", OutputLanguage::Korean) => ("정의", "정리 정의", "정리를 기록합니다"),
        ("def_thm", OutputLanguage::Vietnamese) => {
            ("Định nghĩa", "Định nghĩa định lý", "Ghi lại định lý")
        }

        ("def_thm", OutputLanguage::Chinese) => ("定义", "定义定理", "记录一个定理"),
        ("axiom", OutputLanguage::English) => ("definition", "Axiom", "Assume an axiom"),
        ("axiom", OutputLanguage::ChineseTraditional) => ("定義", "公理", "假定公理"),
        ("axiom", OutputLanguage::French) => ("Définition", "Axiome", "Admettre un axiome"),
        ("axiom", OutputLanguage::Russian) => ("Определение", "Аксиома", "Принять аксиому"),
        ("axiom", OutputLanguage::Spanish) => ("Definición", "Axioma", "Asumir un axioma"),
        ("axiom", OutputLanguage::Arabic) => ("تعريف", "مسلمة", "افتراض مسلمة"),
        ("axiom", OutputLanguage::Japanese) => ("定義", "公理", "公理を仮定します"),
        ("axiom", OutputLanguage::Korean) => ("정의", "공리", "공리를 가정합니다"),
        ("axiom", OutputLanguage::Vietnamese) => ("Định nghĩa", "Tiên đề", "Giả định một tiên đề"),

        ("axiom", OutputLanguage::Chinese) => ("定义", "公理", "假定一条公理"),
        ("def_strategy", OutputLanguage::English) => {
            ("definition", "Define strategy", "Define a proof strategy")
        }
        ("def_strategy", OutputLanguage::ChineseTraditional) => {
            ("定義", "定義策略", "定義證明策略")
        }
        ("def_strategy", OutputLanguage::French) => (
            "Définition",
            "Définition de stratégie",
            "Définir une stratégie de preuve",
        ),
        ("def_strategy", OutputLanguage::Russian) => (
            "Определение",
            "Определение стратегии",
            "Определить стратегию доказательства",
        ),
        ("def_strategy", OutputLanguage::Spanish) => (
            "Definición",
            "Definición de estrategia",
            "Definir una estrategia de prueba",
        ),
        ("def_strategy", OutputLanguage::Arabic) => {
            ("تعريف", "تعريف استراتيجية", "تعريف استراتيجية برهان")
        }
        ("def_strategy", OutputLanguage::Japanese) => {
            ("定義", "戦略の定義", "証明戦略を定義します")
        }
        ("def_strategy", OutputLanguage::Korean) => ("정의", "전략 정의", "증명 전략을 정의합니다"),
        ("def_strategy", OutputLanguage::Vietnamese) => (
            "Định nghĩa",
            "Định nghĩa chiến lược",
            "Định nghĩa chiến lược chứng minh",
        ),

        ("def_strategy", OutputLanguage::Chinese) => ("定义", "定义策略", "定义一个证明策略"),

        // witness / trust
        ("witness_exist", OutputLanguage::English) => {
            ("witness", "Witness exist", "Witness an existential fact")
        }
        ("witness_exist", OutputLanguage::ChineseTraditional) => {
            ("見證", "見證存在", "為存在命題提供見證")
        }
        ("witness_exist", OutputLanguage::French) => (
            "Témoin",
            "Témoin d'existence",
            "Fournir un témoin d'une proposition existentielle",
        ),
        ("witness_exist", OutputLanguage::Russian) => (
            "Свидетель",
            "Свидетель существования",
            "Предъявить свидетель для утверждения существования",
        ),
        ("witness_exist", OutputLanguage::Spanish) => (
            "Testigo",
            "Testigo de existencia",
            "Proporcionar un testigo de una proposición existencial",
        ),
        ("witness_exist", OutputLanguage::Arabic) => {
            ("شاهد", "شاهد وجود", "تقديم شاهد لقضية وجودية")
        }
        ("witness_exist", OutputLanguage::Japanese) => {
            ("証人", "存在の証人", "存在命題の証人を与えます")
        }
        ("witness_exist", OutputLanguage::Korean) => {
            ("증인", "존재 증인", "존재 명제의 증인을 제공합니다")
        }
        ("witness_exist", OutputLanguage::Vietnamese) => (
            "Nhân chứng",
            "Nhân chứng tồn tại",
            "Cung cấp nhân chứng cho mệnh đề tồn tại",
        ),

        ("witness_exist", OutputLanguage::Chinese) => ("见证", "见证存在", "为存在事实提供见证"),
        ("witness_atomic", OutputLanguage::English) => {
            ("witness", "Witness atomic", "Witness an atomic fact")
        }
        ("witness_atomic", OutputLanguage::ChineseTraditional) => {
            ("見證", "見證原子命題", "為原子命題提供見證")
        }
        ("witness_atomic", OutputLanguage::French) => (
            "Témoin",
            "Témoin de proposition atomique",
            "Fournir un témoin d'une proposition atomique",
        ),
        ("witness_atomic", OutputLanguage::Russian) => (
            "Свидетель",
            "Свидетель атомарного утверждения",
            "Предъявить свидетель для атомарного утверждения",
        ),
        ("witness_atomic", OutputLanguage::Spanish) => (
            "Testigo",
            "Testigo de proposición atómica",
            "Proporcionar un testigo de una proposición atómica",
        ),
        ("witness_atomic", OutputLanguage::Arabic) => {
            ("شاهد", "شاهد قضية ذرية", "تقديم شاهد لقضية ذرية")
        }
        ("witness_atomic", OutputLanguage::Japanese) => {
            ("証人", "原子命題の証人", "原子命題の証人を与えます")
        }
        ("witness_atomic", OutputLanguage::Korean) => {
            ("증인", "원자 명제의 증인", "원자 명제의 증인을 제공합니다")
        }
        ("witness_atomic", OutputLanguage::Vietnamese) => (
            "Nhân chứng",
            "Nhân chứng mệnh đề nguyên tử",
            "Cung cấp nhân chứng cho mệnh đề nguyên tử",
        ),

        ("witness_atomic", OutputLanguage::Chinese) => {
            ("见证", "见证原子事实", "为原子事实提供见证")
        }
        ("witness_nonempty", OutputLanguage::English) => (
            "witness",
            "Witness nonempty",
            "Witness that a set is nonempty",
        ),
        ("witness_nonempty", OutputLanguage::ChineseTraditional) => {
            ("見證", "見證非空", "見證集合非空")
        }
        ("witness_nonempty", OutputLanguage::French) => (
            "Témoin",
            "Témoin de non-vacuité",
            "Fournir un témoin qu'un ensemble est non vide",
        ),
        ("witness_nonempty", OutputLanguage::Russian) => (
            "Свидетель",
            "Свидетель непустоты",
            "Предъявить свидетель непустоты множества",
        ),
        ("witness_nonempty", OutputLanguage::Spanish) => (
            "Testigo",
            "Testigo de no vacuidad",
            "Proporcionar un testigo de que un conjunto no está vacío",
        ),
        ("witness_nonempty", OutputLanguage::Arabic) => (
            "شاهد",
            "شاهد عدم الخلو",
            "تقديم شاهد على أن مجموعة غير خالية",
        ),
        ("witness_nonempty", OutputLanguage::Japanese) => (
            "証人",
            "空でないことの証人",
            "集合が空でないことの証人を与えます",
        ),
        ("witness_nonempty", OutputLanguage::Korean) => (
            "증인",
            "공집합이 아님을 보이는 증인",
            "집합이 공집합이 아님을 보이는 증인을 제공합니다",
        ),
        ("witness_nonempty", OutputLanguage::Vietnamese) => (
            "Nhân chứng",
            "Nhân chứng không rỗng",
            "Cung cấp nhân chứng rằng tập không rỗng",
        ),

        ("witness_nonempty", OutputLanguage::Chinese) => ("见证", "见证非空", "见证一个集合非空"),
        ("trust", OutputLanguage::English) => {
            ("trust", "Trust facts", "Trust-store facts without proof")
        }
        ("trust", OutputLanguage::ChineseTraditional) => ("信任", "信任命題", "不加證明地儲存命題"),
        ("trust", OutputLanguage::French) => (
            "Admission sans preuve",
            "Propositions admises",
            "Stocker des propositions admises sans preuve",
        ),
        ("trust", OutputLanguage::Russian) => (
            "Принятие без доказательства",
            "Принятые утверждения",
            "Сохранить утверждения без доказательства",
        ),
        ("trust", OutputLanguage::Spanish) => (
            "Admisión sin prueba",
            "Proposiciones admitidas",
            "Almacenar proposiciones admitidas sin prueba",
        ),
        ("trust", OutputLanguage::Arabic) => (
            "افتراض دون برهان",
            "قضايا مفترضة",
            "تخزين قضايا مفترضة دون برهان",
        ),
        ("trust", OutputLanguage::Japanese) => (
            "証明なしの仮定",
            "命題の仮定",
            "証明なしで命題を仮定して保存します",
        ),
        ("trust", OutputLanguage::Korean) => (
            "증명 없는 신뢰",
            "명제 신뢰",
            "증명 없이 명제를 신뢰하여 저장합니다",
        ),
        ("trust", OutputLanguage::Vietnamese) => (
            "Tin cậy không chứng minh",
            "Tin cậy mệnh đề",
            "Lưu mệnh đề được tin cậy mà không chứng minh",
        ),

        ("trust", OutputLanguage::Chinese) => ("信任", "信任事实", "不加证明地存入事实"),
        ("trust_have", OutputLanguage::English) => (
            "trust",
            "Trust have",
            "Trust-introduce objects and body facts",
        ),
        ("trust_have", OutputLanguage::ChineseTraditional) => {
            ("信任", "信任 have", "信任地引入物件與主體命題")
        }
        ("trust_have", OutputLanguage::French) => (
            "Admission sans preuve",
            "Introduction have admise",
            "Introduire sans preuve des objets et les propositions du corps",
        ),
        ("trust_have", OutputLanguage::Russian) => (
            "Принятие без доказательства",
            "Принятое введение have",
            "Ввести без доказательства объекты и утверждения тела",
        ),
        ("trust_have", OutputLanguage::Spanish) => (
            "Admisión sin prueba",
            "Introducción have admitida",
            "Introducir sin prueba objetos y proposiciones del cuerpo",
        ),
        ("trust_have", OutputLanguage::Arabic) => (
            "افتراض دون برهان",
            "إدخال have مفترض",
            "إدخال كائنات وقضايا المتن دون برهان",
        ),
        ("trust_have", OutputLanguage::Japanese) => (
            "証明なしの仮定",
            "仮定による have",
            "証明なしでオブジェクトと本体の命題を導入します",
        ),
        ("trust_have", OutputLanguage::Korean) => (
            "증명 없는 신뢰",
            "신뢰하는 have",
            "증명 없이 객체와 본문 명제를 신뢰하여 도입합니다",
        ),
        ("trust_have", OutputLanguage::Vietnamese) => (
            "Tin cậy không chứng minh",
            "have được tin cậy",
            "Đưa vào đối tượng và mệnh đề trong thân mà không chứng minh",
        ),

        ("trust_have", OutputLanguage::Chinese) => {
            ("信任", "信任 have", "信任地引入对象与主体事实")
        }

        // by
        ("by_cases", OutputLanguage::English) => ("by", "By cases", "Prove by case analysis"),
        ("by_cases", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "分情況證明", "以分情況分析證明")
        }
        ("by_cases", OutputLanguage::French) => {
            ("Méthode de preuve", "Par cas", "Prouver par analyse de cas")
        }
        ("by_cases", OutputLanguage::Russian) => (
            "Метод доказательства",
            "По случаям",
            "Доказать разбором случаев",
        ),
        ("by_cases", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por casos",
            "Demostrar por análisis de casos",
        ),
        ("by_cases", OutputLanguage::Arabic) => ("طريقة البرهان", "بالحالات", "إثبات بتحليل الحالات"),
        ("by_cases", OutputLanguage::Japanese) => {
            ("証明方法", "場合分けによる証明", "場合分けで証明します")
        }
        ("by_cases", OutputLanguage::Korean) => {
            ("증명 방법", "경우에 따른 증명", "경우 분석으로 증명합니다")
        }
        ("by_cases", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Theo trường hợp",
            "Chứng minh bằng phân tích trường hợp",
        ),

        ("by_cases", OutputLanguage::Chinese) => ("证明方式", "分情况证明", "用分情况分析证明"),
        ("by_contra", OutputLanguage::English) => {
            ("by", "By contradiction", "Prove by contradiction")
        }
        ("by_contra", OutputLanguage::ChineseTraditional) => ("證明方式", "反證法", "以反證法證明"),
        ("by_contra", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par contradiction",
            "Prouver par contradiction",
        ),
        ("by_contra", OutputLanguage::Russian) => (
            "Метод доказательства",
            "От противного",
            "Доказать от противного",
        ),
        ("by_contra", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por contradicción",
            "Demostrar por contradicción",
        ),
        ("by_contra", OutputLanguage::Arabic) => ("طريقة البرهان", "بالتناقض", "إثبات بالتناقض"),
        ("by_contra", OutputLanguage::Japanese) => ("証明方法", "背理法", "背理法で証明します"),
        ("by_contra", OutputLanguage::Korean) => ("증명 방법", "귀류법", "귀류법으로 증명합니다"),
        ("by_contra", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Bằng phản chứng",
            "Chứng minh bằng phản chứng",
        ),

        ("by_contra", OutputLanguage::Chinese) => ("证明方式", "反证法", "用反证法证明"),
        ("by_def", OutputLanguage::English) => {
            ("by", "By definition", "Prove by unfolding a definition")
        }
        ("by_def", OutputLanguage::ChineseTraditional) => ("證明方式", "按定義", "展開定義來證明"),
        ("by_def", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par définition",
            "Prouver en développant une définition",
        ),
        ("by_def", OutputLanguage::Russian) => (
            "Метод доказательства",
            "По определению",
            "Доказать раскрытием определения",
        ),
        ("by_def", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por definición",
            "Demostrar al desplegar una definición",
        ),
        ("by_def", OutputLanguage::Arabic) => ("طريقة البرهان", "بالتعريف", "إثبات بتوسيع تعريف"),
        ("by_def", OutputLanguage::Japanese) => {
            ("証明方法", "定義による証明", "定義を展開して証明します")
        }
        ("by_def", OutputLanguage::Korean) => {
            ("증명 방법", "정의에 의한 증명", "정의를 펼쳐 증명합니다")
        }
        ("by_def", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Theo định nghĩa",
            "Chứng minh bằng khai triển định nghĩa",
        ),

        ("by_def", OutputLanguage::Chinese) => ("证明方式", "按定义", "展开定义来证明"),
        ("by_extension", OutputLanguage::English) => {
            ("by", "By set extension", "Prove set equality by extension")
        }
        ("by_extension", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "集合外延性", "以外延性證明集合相等")
        }
        ("by_extension", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par extensionnalité des ensembles",
            "Prouver l'égalité d'ensembles par extensionnalité",
        ),
        ("by_extension", OutputLanguage::Russian) => (
            "Метод доказательства",
            "По экстенсиональности множеств",
            "Доказать равенство множеств по экстенсиональности",
        ),
        ("by_extension", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por extensionalidad de conjuntos",
            "Demostrar igualdad de conjuntos por extensionalidad",
        ),
        ("by_extension", OutputLanguage::Arabic) => (
            "طريقة البرهان",
            "بامتدادية المجموعات",
            "إثبات تساوي مجموعتين بالامتدادية",
        ),
        ("by_extension", OutputLanguage::Japanese) => (
            "証明方法",
            "集合の外延性",
            "外延性により集合の等しさを証明します",
        ),
        ("by_extension", OutputLanguage::Korean) => (
            "증명 방법",
            "집합 외연성",
            "외연성으로 집합의 같음을 증명합니다",
        ),
        ("by_extension", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Theo tính ngoại diên của tập hợp",
            "Chứng minh hai tập bằng nhau bằng tính ngoại diên",
        ),

        ("by_extension", OutputLanguage::Chinese) => ("证明方式", "外延性", "用外延性证明集合相等"),
        ("by_fn_extension", OutputLanguage::English) => (
            "by",
            "By function extension",
            "Prove function equality by extension",
        ),
        ("by_fn_extension", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "函數外延性", "以外延性證明函數相等")
        }
        ("by_fn_extension", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par extensionnalité des fonctions",
            "Prouver l'égalité de fonctions par extensionnalité",
        ),
        ("by_fn_extension", OutputLanguage::Russian) => (
            "Метод доказательства",
            "По экстенсиональности функций",
            "Доказать равенство функций по экстенсиональности",
        ),
        ("by_fn_extension", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por extensionalidad de funciones",
            "Demostrar igualdad de funciones por extensionalidad",
        ),
        ("by_fn_extension", OutputLanguage::Arabic) => (
            "طريقة البرهان",
            "بامتدادية الدوال",
            "إثبات تساوي دالتين بالامتدادية",
        ),
        ("by_fn_extension", OutputLanguage::Japanese) => (
            "証明方法",
            "関数の外延性",
            "外延性により関数の等しさを証明します",
        ),
        ("by_fn_extension", OutputLanguage::Korean) => (
            "증명 방법",
            "함수 외연성",
            "외연성으로 함수의 같음을 증명합니다",
        ),
        ("by_fn_extension", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Theo tính ngoại diên của hàm",
            "Chứng minh hai hàm bằng nhau bằng tính ngoại diên",
        ),

        ("by_fn_extension", OutputLanguage::Chinese) => {
            ("证明方式", "函数外延性", "用函数外延性证明相等")
        }
        ("by_enumerate", OutputLanguage::English) => (
            "by",
            "By finite enumeration",
            "Prove by enumerating a finite set",
        ),
        ("by_enumerate", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "有限列舉", "列舉有限集合來證明")
        }
        ("by_enumerate", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par énumération finie",
            "Prouver en énumérant un ensemble fini",
        ),
        ("by_enumerate", OutputLanguage::Russian) => (
            "Метод доказательства",
            "Конечным перебором",
            "Доказать перебором конечного множества",
        ),
        ("by_enumerate", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por enumeración finita",
            "Demostrar enumerando un conjunto finito",
        ),
        ("by_enumerate", OutputLanguage::Arabic) => (
            "طريقة البرهان",
            "بالتعداد المنتهي",
            "إثبات بتعداد مجموعة منتهية",
        ),
        ("by_enumerate", OutputLanguage::Japanese) => {
            ("証明方法", "有限列挙", "有限集合を列挙して証明します")
        }
        ("by_enumerate", OutputLanguage::Korean) => {
            ("증명 방법", "유한 열거", "유한 집합을 열거하여 증명합니다")
        }
        ("by_enumerate", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Bằng liệt kê hữu hạn",
            "Chứng minh bằng liệt kê tập hữu hạn",
        ),

        ("by_enumerate", OutputLanguage::Chinese) => ("证明方式", "有限枚举", "枚举有限集来证明"),
        ("by_for", OutputLanguage::English) => ("by", "By for", "Prove inside a for-block"),
        ("by_for", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "for 區塊", "在 for 區塊中證明")
        }
        ("by_for", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par bloc for",
            "Prouver dans un bloc for",
        ),
        ("by_for", OutputLanguage::Russian) => (
            "Метод доказательства",
            "В блоке for",
            "Доказать внутри блока for",
        ),
        ("by_for", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por bloque for",
            "Demostrar dentro de un bloque for",
        ),
        ("by_for", OutputLanguage::Arabic) => ("طريقة البرهان", "بكتلة for", "إثبات داخل كتلة for"),
        ("by_for", OutputLanguage::Japanese) => {
            ("証明方法", "for ブロック", "for ブロック内で証明します")
        }
        ("by_for", OutputLanguage::Korean) => {
            ("증명 방법", "for 블록", "for 블록 안에서 증명합니다")
        }
        ("by_for", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Bằng khối for",
            "Chứng minh trong khối for",
        ),

        ("by_for", OutputLanguage::Chinese) => ("证明方式", "for 块", "在 for 块中证明"),
        ("by_thm", OutputLanguage::English) => ("by", "By theorem", "Apply a recorded theorem"),
        ("by_thm", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "用定理", "套用已記錄的定理")
        }
        ("by_thm", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par théorème",
            "Appliquer un théorème enregistré",
        ),
        ("by_thm", OutputLanguage::Russian) => (
            "Метод доказательства",
            "По теореме",
            "Применить записанную теорему",
        ),
        ("by_thm", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por teorema",
            "Aplicar un teorema registrado",
        ),
        ("by_thm", OutputLanguage::Arabic) => ("طريقة البرهان", "بمبرهنة", "تطبيق مبرهنة مسجلة"),
        ("by_thm", OutputLanguage::Japanese) => {
            ("証明方法", "定理による証明", "記録済みの定理を適用します")
        }
        ("by_thm", OutputLanguage::Korean) => {
            ("증명 방법", "정리에 의한 증명", "기록된 정리를 적용합니다")
        }
        ("by_thm", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Theo định lý",
            "Áp dụng định lý đã ghi",
        ),

        ("by_thm", OutputLanguage::Chinese) => ("证明方式", "用定理", "应用已记录的定理"),
        ("by_induc", OutputLanguage::English) => ("by", "By induction", "Prove by induction"),
        ("by_induc", OutputLanguage::ChineseTraditional) => ("證明方式", "歸納法", "以歸納法證明"),
        ("by_induc", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par induction",
            "Prouver par induction",
        ),
        ("by_induc", OutputLanguage::Russian) => {
            ("Метод доказательства", "По индукции", "Доказать индукцией")
        }
        ("by_induc", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por inducción",
            "Demostrar por inducción",
        ),
        ("by_induc", OutputLanguage::Arabic) => ("طريقة البرهان", "بالاستقراء", "إثبات بالاستقراء"),
        ("by_induc", OutputLanguage::Japanese) => ("証明方法", "帰納法", "帰納法で証明します"),
        ("by_induc", OutputLanguage::Korean) => ("증명 방법", "귀납법", "귀납법으로 증명합니다"),
        ("by_induc", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Bằng quy nạp",
            "Chứng minh bằng quy nạp",
        ),

        ("by_induc", OutputLanguage::Chinese) => ("证明方式", "归纳法", "用归纳法证明"),
        ("by_strong_induc", OutputLanguage::English) => {
            ("by", "By strong induction", "Prove by strong induction")
        }
        ("by_strong_induc", OutputLanguage::ChineseTraditional) => {
            ("證明方式", "強歸納法", "以強歸納法證明")
        }
        ("by_strong_induc", OutputLanguage::French) => (
            "Méthode de preuve",
            "Par induction forte",
            "Prouver par induction forte",
        ),
        ("by_strong_induc", OutputLanguage::Russian) => (
            "Метод доказательства",
            "По сильной индукции",
            "Доказать сильной индукцией",
        ),
        ("by_strong_induc", OutputLanguage::Spanish) => (
            "Método de demostración",
            "Por inducción fuerte",
            "Demostrar por inducción fuerte",
        ),
        ("by_strong_induc", OutputLanguage::Arabic) => {
            ("طريقة البرهان", "بالاستقراء القوي", "إثبات بالاستقراء القوي")
        }
        ("by_strong_induc", OutputLanguage::Japanese) => {
            ("証明方法", "強い帰納法", "強い帰納法で証明します")
        }
        ("by_strong_induc", OutputLanguage::Korean) => {
            ("증명 방법", "강한 귀납법", "강한 귀납법으로 증명합니다")
        }
        ("by_strong_induc", OutputLanguage::Vietnamese) => (
            "Phương pháp chứng minh",
            "Bằng quy nạp mạnh",
            "Chứng minh bằng quy nạp mạnh",
        ),

        ("by_strong_induc", OutputLanguage::Chinese) => ("证明方式", "强归纳", "用强归纳法证明"),

        // register / release / proof block / command
        ("register_reflexive", OutputLanguage::English) => (
            "register",
            "Register reflexive",
            "Register a reflexive property",
        ),
        ("register_reflexive", OutputLanguage::ChineseTraditional) => {
            ("註冊", "註冊自反性", "註冊自反性質")
        }
        ("register_reflexive", OutputLanguage::French) => (
            "Enregistrement",
            "Enregistrement de réflexivité",
            "Enregistrer une propriété réflexive",
        ),
        ("register_reflexive", OutputLanguage::Russian) => (
            "Регистрация",
            "Регистрация рефлексивности",
            "Зарегистрировать рефлексивное свойство",
        ),
        ("register_reflexive", OutputLanguage::Spanish) => (
            "Registro",
            "Registro de reflexividad",
            "Registrar una propiedad reflexiva",
        ),
        ("register_reflexive", OutputLanguage::Arabic) => {
            ("تسجيل", "تسجيل الانعكاسية", "تسجيل خاصية انعكاسية")
        }
        ("register_reflexive", OutputLanguage::Japanese) => {
            ("登録", "反射性の登録", "反射的な性質を登録します")
        }
        ("register_reflexive", OutputLanguage::Korean) => {
            ("등록", "반사성 등록", "반사 성질을 등록합니다")
        }
        ("register_reflexive", OutputLanguage::Vietnamese) => (
            "Đăng ký",
            "Đăng ký tính phản xạ",
            "Đăng ký một tính chất phản xạ",
        ),

        ("register_reflexive", OutputLanguage::Chinese) => ("注册", "注册自反", "注册自反性质"),
        ("register_symmetric", OutputLanguage::English) => (
            "register",
            "Register symmetric",
            "Register a symmetric property",
        ),
        ("register_symmetric", OutputLanguage::ChineseTraditional) => {
            ("註冊", "註冊對稱性", "註冊對稱性質")
        }
        ("register_symmetric", OutputLanguage::French) => (
            "Enregistrement",
            "Enregistrement de symétrie",
            "Enregistrer une propriété symétrique",
        ),
        ("register_symmetric", OutputLanguage::Russian) => (
            "Регистрация",
            "Регистрация симметричности",
            "Зарегистрировать симметричное свойство",
        ),
        ("register_symmetric", OutputLanguage::Spanish) => (
            "Registro",
            "Registro de simetría",
            "Registrar una propiedad simétrica",
        ),
        ("register_symmetric", OutputLanguage::Arabic) => {
            ("تسجيل", "تسجيل التناظر", "تسجيل خاصية متناظرة")
        }
        ("register_symmetric", OutputLanguage::Japanese) => {
            ("登録", "対称性の登録", "対称的な性質を登録します")
        }
        ("register_symmetric", OutputLanguage::Korean) => {
            ("등록", "대칭성 등록", "대칭 성질을 등록합니다")
        }
        ("register_symmetric", OutputLanguage::Vietnamese) => (
            "Đăng ký",
            "Đăng ký tính đối xứng",
            "Đăng ký một tính chất đối xứng",
        ),

        ("register_symmetric", OutputLanguage::Chinese) => ("注册", "注册对称", "注册对称性质"),
        ("register_transitive", OutputLanguage::English) => (
            "register",
            "Register transitive",
            "Register a transitive property",
        ),
        ("register_transitive", OutputLanguage::ChineseTraditional) => {
            ("註冊", "註冊遞移性", "註冊遞移性質")
        }
        ("register_transitive", OutputLanguage::French) => (
            "Enregistrement",
            "Enregistrement de transitivité",
            "Enregistrer une propriété transitive",
        ),
        ("register_transitive", OutputLanguage::Russian) => (
            "Регистрация",
            "Регистрация транзитивности",
            "Зарегистрировать транзитивное свойство",
        ),
        ("register_transitive", OutputLanguage::Spanish) => (
            "Registro",
            "Registro de transitividad",
            "Registrar una propiedad transitiva",
        ),
        ("register_transitive", OutputLanguage::Arabic) => {
            ("تسجيل", "تسجيل التعدي", "تسجيل خاصية متعدية")
        }
        ("register_transitive", OutputLanguage::Japanese) => {
            ("登録", "推移性の登録", "推移的な性質を登録します")
        }
        ("register_transitive", OutputLanguage::Korean) => {
            ("등록", "추이성 등록", "추이 성질을 등록합니다")
        }
        ("register_transitive", OutputLanguage::Vietnamese) => (
            "Đăng ký",
            "Đăng ký tính bắc cầu",
            "Đăng ký một tính chất bắc cầu",
        ),

        ("register_transitive", OutputLanguage::Chinese) => ("注册", "注册传递", "注册传递性质"),
        ("release_thm", OutputLanguage::English) => (
            "release",
            "Release theorem",
            "Release a theorem into the environment",
        ),
        ("release_thm", OutputLanguage::ChineseTraditional) => {
            ("釋放", "釋放定理", "將定理釋放到環境")
        }
        ("release_thm", OutputLanguage::French) => (
            "Libération",
            "Libération de théorème",
            "Libérer un théorème dans l'environnement",
        ),
        ("release_thm", OutputLanguage::Russian) => (
            "Освобождение",
            "Освобождение теоремы",
            "Освободить теорему в окружении",
        ),
        ("release_thm", OutputLanguage::Spanish) => (
            "Liberación",
            "Liberación de teorema",
            "Liberar un teorema en el entorno",
        ),
        ("release_thm", OutputLanguage::Arabic) => {
            ("إتاحة", "إتاحة مبرهنة", "إتاحة مبرهنة في البيئة")
        }
        ("release_thm", OutputLanguage::Japanese) => {
            ("解放", "定理の解放", "定理を環境に解放します")
        }
        ("release_thm", OutputLanguage::Korean) => {
            ("해제", "정리 해제", "정리를 환경에 해제합니다")
        }
        ("release_thm", OutputLanguage::Vietnamese) => (
            "Giải phóng",
            "Giải phóng định lý",
            "Giải phóng định lý vào môi trường",
        ),

        ("release_thm", OutputLanguage::Chinese) => ("释放", "释放定理", "把定理释放到环境中"),
        ("release_struct", OutputLanguage::English) => {
            ("release", "Release struct", "Release a struct definition")
        }
        ("release_struct", OutputLanguage::ChineseTraditional) => {
            ("釋放", "釋放結構", "釋放結構定義")
        }
        ("release_struct", OutputLanguage::French) => (
            "Libération",
            "Libération de structure",
            "Libérer une définition de structure",
        ),
        ("release_struct", OutputLanguage::Russian) => (
            "Освобождение",
            "Освобождение структуры",
            "Освободить определение структуры",
        ),
        ("release_struct", OutputLanguage::Spanish) => (
            "Liberación",
            "Liberación de estructura",
            "Liberar una definición de estructura",
        ),
        ("release_struct", OutputLanguage::Arabic) => ("إتاحة", "إتاحة بنية", "إتاحة تعريف بنية"),
        ("release_struct", OutputLanguage::Japanese) => {
            ("解放", "構造の解放", "構造定義を解放します")
        }
        ("release_struct", OutputLanguage::Korean) => {
            ("해제", "구조 해제", "구조 정의를 해제합니다")
        }
        ("release_struct", OutputLanguage::Vietnamese) => (
            "Giải phóng",
            "Giải phóng cấu trúc",
            "Giải phóng định nghĩa cấu trúc",
        ),

        ("release_struct", OutputLanguage::Chinese) => ("释放", "释放结构", "释放结构定义"),
        ("release_obj" | "release_cart_def", OutputLanguage::English) => (
            "release",
            "Release object def",
            "Release an object definition",
        ),
        ("release_obj" | "release_cart_def", OutputLanguage::ChineseTraditional) => {
            ("釋放", "釋放物件定義", "釋放物件定義")
        }
        ("release_obj" | "release_cart_def", OutputLanguage::French) => (
            "Libération",
            "Libération de définition d'objet",
            "Libérer une définition d'objet",
        ),
        ("release_obj" | "release_cart_def", OutputLanguage::Russian) => (
            "Освобождение",
            "Освобождение определения объекта",
            "Освободить определение объекта",
        ),
        ("release_obj" | "release_cart_def", OutputLanguage::Spanish) => (
            "Liberación",
            "Liberación de definición de objeto",
            "Liberar una definición de objeto",
        ),
        ("release_obj" | "release_cart_def", OutputLanguage::Arabic) => {
            ("إتاحة", "إتاحة تعريف كائن", "إتاحة تعريف كائن")
        }
        ("release_obj" | "release_cart_def", OutputLanguage::Japanese) => (
            "解放",
            "オブジェクト定義の解放",
            "オブジェクト定義を解放します",
        ),
        ("release_obj" | "release_cart_def", OutputLanguage::Korean) => {
            ("해제", "객체 정의 해제", "객체 정의를 해제합니다")
        }
        ("release_obj" | "release_cart_def", OutputLanguage::Vietnamese) => (
            "Giải phóng",
            "Giải phóng định nghĩa đối tượng",
            "Giải phóng định nghĩa đối tượng",
        ),

        ("release_obj" | "release_cart_def", OutputLanguage::Chinese) => ("释放", "释放对象定义", "释放对象定义"),
        ("expand_range", OutputLanguage::English) => (
            "release",
            "Expand range",
            "Expand a function range obligation",
        ),
        ("expand_range", OutputLanguage::ChineseTraditional) => {
            ("釋放", "展開值域", "展開函數值域義務")
        }
        ("expand_range", OutputLanguage::French) => (
            "Libération",
            "Développement de l'image",
            "Développer une obligation sur l'image d'une fonction",
        ),
        ("expand_range", OutputLanguage::Russian) => (
            "Освобождение",
            "Раскрытие области значений",
            "Раскрыть обязательство об области значений функции",
        ),
        ("expand_range", OutputLanguage::Spanish) => (
            "Liberación",
            "Despliegue del rango",
            "Desplegar una obligación sobre el rango de una función",
        ),
        ("expand_range", OutputLanguage::Arabic) => {
            ("إتاحة", "توسيع المدى", "توسيع التزام مدى دالة")
        }
        ("expand_range", OutputLanguage::Japanese) => (
            "解放",
            "値域の展開",
            "関数の値域に関する証明義務を展開します",
        ),
        ("expand_range", OutputLanguage::Korean) => {
            ("해제", "치역 펼치기", "함수 치역의 증명 의무를 펼칩니다")
        }
        ("expand_range", OutputLanguage::Vietnamese) => (
            "Giải phóng",
            "Khai triển miền giá trị",
            "Khai triển nghĩa vụ chứng minh miền giá trị của hàm",
        ),

        ("expand_range", OutputLanguage::Chinese) => ("释放", "展开值域", "展开函数值域义务"),
        ("release_zorn", OutputLanguage::English) => {
            ("release", "Zorn lemma", "Release Zorn's lemma")
        }
        ("release_zorn", OutputLanguage::ChineseTraditional) => {
            ("釋放", "Zorn 引理", "釋放 Zorn 引理")
        }
        ("release_zorn", OutputLanguage::French) => {
            ("Libération", "Lemme de Zorn", "Libérer le lemme de Zorn")
        }
        ("release_zorn", OutputLanguage::Russian) => {
            ("Освобождение", "Лемма Цорна", "Освободить лемму Цорна")
        }
        ("release_zorn", OutputLanguage::Spanish) => {
            ("Liberación", "Lema de Zorn", "Liberar el lema de Zorn")
        }
        ("release_zorn", OutputLanguage::Arabic) => ("إتاحة", "لمّة زورن", "إتاحة لمّة زورن"),
        ("release_zorn", OutputLanguage::Japanese) => {
            ("解放", "ツォルンの補題", "ツォルンの補題を解放します")
        }
        ("release_zorn", OutputLanguage::Korean) => {
            ("해제", "초른 보조정리", "초른 보조정리를 해제합니다")
        }
        ("release_zorn", OutputLanguage::Vietnamese) => {
            ("Giải phóng", "Bổ đề Zorn", "Giải phóng bổ đề Zorn")
        }

        ("release_zorn", OutputLanguage::Chinese) => ("释放", "Zorn 引理", "释放 Zorn 引理"),
        ("release_choice", OutputLanguage::English) => {
            ("release", "Axiom of choice", "Release the axiom of choice")
        }
        ("release_choice", OutputLanguage::ChineseTraditional) => {
            ("釋放", "選擇公理", "釋放選擇公理")
        }
        ("release_choice", OutputLanguage::French) => {
            ("Libération", "Axiome du choix", "Libérer l'axiome du choix")
        }
        ("release_choice", OutputLanguage::Russian) => (
            "Освобождение",
            "Аксиома выбора",
            "Освободить аксиому выбора",
        ),
        ("release_choice", OutputLanguage::Spanish) => (
            "Liberación",
            "Axioma de elección",
            "Liberar el axioma de elección",
        ),
        ("release_choice", OutputLanguage::Arabic) => {
            ("إتاحة", "مسلمة الاختيار", "إتاحة مسلمة الاختيار")
        }
        ("release_choice", OutputLanguage::Japanese) => {
            ("解放", "選択公理", "選択公理を解放します")
        }
        ("release_choice", OutputLanguage::Korean) => {
            ("해제", "선택 공리", "선택 공리를 해제합니다")
        }
        ("release_choice", OutputLanguage::Vietnamese) => {
            ("Giải phóng", "Tiên đề chọn", "Giải phóng tiên đề chọn")
        }

        ("release_choice", OutputLanguage::Chinese) => ("释放", "选择公理", "释放选择公理"),
        ("release_regularity", OutputLanguage::English) => (
            "release",
            "Regularity axiom",
            "Release the regularity axiom",
        ),
        ("release_regularity", OutputLanguage::ChineseTraditional) => {
            ("釋放", "正則公理", "釋放正則公理")
        }
        ("release_regularity", OutputLanguage::French) => (
            "Libération",
            "Axiome de fondation",
            "Libérer l'axiome de fondation",
        ),
        ("release_regularity", OutputLanguage::Russian) => (
            "Освобождение",
            "Аксиома регулярности",
            "Освободить аксиому регулярности",
        ),
        ("release_regularity", OutputLanguage::Spanish) => (
            "Liberación",
            "Axioma de regularidad",
            "Liberar el axioma de regularidad",
        ),
        ("release_regularity", OutputLanguage::Arabic) => {
            ("إتاحة", "مسلمة الانتظام", "إتاحة مسلمة الانتظام")
        }
        ("release_regularity", OutputLanguage::Japanese) => {
            ("解放", "正則性公理", "正則性公理を解放します")
        }
        ("release_regularity", OutputLanguage::Korean) => {
            ("해제", "정칙성 공리", "정칙성 공리를 해제합니다")
        }
        ("release_regularity", OutputLanguage::Vietnamese) => (
            "Giải phóng",
            "Tiên đề chính quy",
            "Giải phóng tiên đề chính quy",
        ),

        ("release_regularity", OutputLanguage::Chinese) => ("释放", "正则公理", "释放正则公理"),
        ("claim", OutputLanguage::English) => (
            "proof_block",
            "Claim",
            "Prove a claim block and store its conclusions",
        ),
        ("claim", OutputLanguage::ChineseTraditional) => {
            ("證明區塊", "claim 區塊", "證明 claim 區塊並儲存結論")
        }
        ("claim", OutputLanguage::French) => (
            "Bloc de preuve",
            "Assertion",
            "Prouver un bloc claim et stocker ses conclusions",
        ),
        ("claim", OutputLanguage::Russian) => (
            "Блок доказательства",
            "Утверждение",
            "Доказать блок claim и сохранить его заключения",
        ),
        ("claim", OutputLanguage::Spanish) => (
            "Bloque de prueba",
            "Afirmación",
            "Demostrar un bloque claim y almacenar sus conclusiones",
        ),
        ("claim", OutputLanguage::Arabic) => {
            ("كتلة برهان", "ادعاء", "إثبات كتلة claim وتخزين نتائجها")
        }
        ("claim", OutputLanguage::Japanese) => (
            "証明ブロック",
            "claim ブロック",
            "claim ブロックを証明し、その結論を保存します",
        ),
        ("claim", OutputLanguage::Korean) => (
            "증명 블록",
            "claim 블록",
            "claim 블록을 증명하고 결론을 저장합니다",
        ),
        ("claim", OutputLanguage::Vietnamese) => (
            "Khối chứng minh",
            "Khối claim",
            "Chứng minh khối claim và lưu các kết luận",
        ),

        ("claim", OutputLanguage::Chinese) => ("证明块", "claim 块", "证明 claim 块并存储结论"),
        ("sketch", OutputLanguage::English) => {
            ("proof_block", "Sketch", "Run a sketch proof block")
        }
        ("sketch", OutputLanguage::ChineseTraditional) => {
            ("證明區塊", "sketch 區塊", "執行 sketch 證明區塊")
        }
        ("sketch", OutputLanguage::French) => (
            "Bloc de preuve",
            "Esquisse",
            "Exécuter un bloc de preuve sketch",
        ),
        ("sketch", OutputLanguage::Russian) => (
            "Блок доказательства",
            "Набросок",
            "Выполнить блок доказательства sketch",
        ),
        ("sketch", OutputLanguage::Spanish) => (
            "Bloque de prueba",
            "Esbozo",
            "Ejecutar un bloque de prueba sketch",
        ),
        ("sketch", OutputLanguage::Arabic) => {
            ("كتلة برهان", "مخطط برهان", "تنفيذ كتلة برهان sketch")
        }
        ("sketch", OutputLanguage::Japanese) => (
            "証明ブロック",
            "sketch ブロック",
            "sketch 証明ブロックを実行します",
        ),
        ("sketch", OutputLanguage::Korean) => {
            ("증명 블록", "sketch 블록", "sketch 증명 블록을 실행합니다")
        }
        ("sketch", OutputLanguage::Vietnamese) => (
            "Khối chứng minh",
            "Khối sketch",
            "Chạy khối chứng minh sketch",
        ),

        ("sketch", OutputLanguage::Chinese) => ("证明块", "sketch 块", "运行 sketch 证明块"),
        ("eval", OutputLanguage::English) => (
            "command",
            "Eval",
            "Evaluate an exact expression and store its result equality",
        ),
        ("eval", OutputLanguage::ChineseTraditional) => {
            ("命令", "求值", "精確求值並儲存原運算式與結果的等式")
        }
        ("eval", OutputLanguage::French) => (
            "Commande",
            "Évaluation",
            "Évaluer exactement une expression et enregistrer son égalité au résultat",
        ),
        ("eval", OutputLanguage::Russian) => (
            "Команда",
            "Вычисление",
            "Точно вычислить выражение и сохранить равенство с результатом",
        ),
        ("eval", OutputLanguage::Spanish) => (
            "Comando",
            "Evaluación",
            "Evaluar exactamente una expresión y guardar su igualdad con el resultado",
        ),
        ("eval", OutputLanguage::Arabic) => (
            "أمر",
            "تقييم",
            "تقييم التعبير بدقة وحفظ مساواته بالنتيجة",
        ),
        ("eval", OutputLanguage::Japanese) => (
            "コマンド",
            "評価",
            "式を正確に評価し、結果との等式を保存します",
        ),
        ("eval", OutputLanguage::Korean) => (
            "명령",
            "평가",
            "식을 정확히 평가하고 결과와의 등식을 저장합니다",
        ),
        ("eval", OutputLanguage::Vietnamese) => (
            "Lệnh",
            "Tính giá trị",
            "Tính chính xác biểu thức và lưu đẳng thức với kết quả",
        ),

        ("eval", OutputLanguage::Chinese) => {
            ("命令", "求值", "精确求值并存储原表达式与结果的等式")
        }

        (_, OutputLanguage::English) => ("stmt", kind, "Statement completed"),
        (_, OutputLanguage::ChineseTraditional) => ("語句", kind, "語句執行完成"),
        (_, OutputLanguage::French) => ("Instruction", kind, "Instruction terminée"),
        (_, OutputLanguage::Russian) => ("Инструкция", kind, "Инструкция выполнена"),
        (_, OutputLanguage::Spanish) => ("Instrucción", kind, "Instrucción completada"),
        (_, OutputLanguage::Arabic) => ("تعليمة", kind, "اكتملت التعليمة"),
        (_, OutputLanguage::Japanese) => ("文", kind, "文の実行が完了しました"),
        (_, OutputLanguage::Korean) => ("문장", kind, "문장 실행 완료"),
        (_, OutputLanguage::Vietnamese) => ("Câu lệnh", kind, "Câu lệnh đã hoàn tất"),

        (_, OutputLanguage::Chinese) => ("语句", kind, "语句已完成"),
    };
    StmtWhyText {
        type_tag,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}

pub fn explain_compound_fact_why(kind: &str, lang: OutputLanguage) -> StmtWhyText {
    let (rule_name, message) = match (kind, lang) {
        ("and", OutputLanguage::English) => (
            "Conjunction",
            "Verified as a compound and-fact (details omitted in Normal)",
        ),
        ("and", OutputLanguage::ChineseTraditional) => {
            ("合取", "已驗證合取命題（Normal 省略細節）")
        }
        ("and", OutputLanguage::French) => (
            "Conjonction",
            "Vérifié comme conjonction composée (détails omis en Normal)",
        ),
        ("and", OutputLanguage::Russian) => (
            "Конъюнкция",
            "Проверено как составная конъюнкция (подробности опущены в Normal)",
        ),
        ("and", OutputLanguage::Spanish) => (
            "Conjunción",
            "Verificado como conjunción compuesta (detalles omitidos en Normal)",
        ),
        ("and", OutputLanguage::Arabic) => (
            "اقتران",
            "تم التحقق كقضية اقتران مركبة (التفاصيل محذوفة في Normal)",
        ),
        ("and", OutputLanguage::Japanese) => (
            "連言",
            "複合した連言命題として検証しました（Normal では詳細を省略）",
        ),
        ("and", OutputLanguage::Korean) => (
            "논리곱",
            "복합 논리곱 명제로 검증했습니다(Normal에서 상세 생략)",
        ),
        ("and", OutputLanguage::Vietnamese) => (
            "Hội",
            "Đã kiểm chứng mệnh đề hội phức hợp (bỏ chi tiết trong Normal)",
        ),

        ("and", OutputLanguage::Chinese) => ("合取", "作为合取事实验证（Normal 省略细节）"),
        ("or", OutputLanguage::English) => (
            "Disjunction",
            "Verified as a compound or-fact (details omitted in Normal)",
        ),
        ("or", OutputLanguage::ChineseTraditional) => ("析取", "已驗證析取命題（Normal 省略細節）"),
        ("or", OutputLanguage::French) => (
            "Disjonction",
            "Vérifié comme disjonction composée (détails omis en Normal)",
        ),
        ("or", OutputLanguage::Russian) => (
            "Дизъюнкция",
            "Проверено как составная дизъюнкция (подробности опущены в Normal)",
        ),
        ("or", OutputLanguage::Spanish) => (
            "Disyunción",
            "Verificado como disyunción compuesta (detalles omitidos en Normal)",
        ),
        ("or", OutputLanguage::Arabic) => (
            "فصل",
            "تم التحقق كقضية فصل مركبة (التفاصيل محذوفة في Normal)",
        ),
        ("or", OutputLanguage::Japanese) => (
            "選言",
            "複合した選言命題として検証しました（Normal では詳細を省略）",
        ),
        ("or", OutputLanguage::Korean) => (
            "논리합",
            "복합 논리합 명제로 검증했습니다(Normal에서 상세 생략)",
        ),
        ("or", OutputLanguage::Vietnamese) => (
            "Tuyển",
            "Đã kiểm chứng mệnh đề tuyển phức hợp (bỏ chi tiết trong Normal)",
        ),

        ("or", OutputLanguage::Chinese) => ("析取", "作为析取事实验证（Normal 省略细节）"),
        ("forall", OutputLanguage::English) => (
            "Universal",
            "Verified as a forall fact (details omitted in Normal)",
        ),
        ("forall", OutputLanguage::ChineseTraditional) => {
            ("全稱", "已驗證全稱命題（Normal 省略細節）")
        }
        ("forall", OutputLanguage::French) => (
            "Universelle",
            "Vérifié comme proposition universelle (détails omis en Normal)",
        ),
        ("forall", OutputLanguage::Russian) => (
            "Всеобщее утверждение",
            "Проверено как всеобщее утверждение (подробности опущены в Normal)",
        ),
        ("forall", OutputLanguage::Spanish) => (
            "Universal",
            "Verificado como proposición universal (detalles omitidos en Normal)",
        ),
        ("forall", OutputLanguage::Arabic) => {
            ("كلية", "تم التحقق كقضية كلية (التفاصيل محذوفة في Normal)")
        }
        ("forall", OutputLanguage::Japanese) => (
            "全称",
            "全称命題として検証しました（Normal では詳細を省略）",
        ),
        ("forall", OutputLanguage::Korean) => {
            ("전칭", "전칭 명제로 검증했습니다(Normal에서 상세 생략)")
        }
        ("forall", OutputLanguage::Vietnamese) => (
            "Phổ quát",
            "Đã kiểm chứng mệnh đề phổ quát (bỏ chi tiết trong Normal)",
        ),

        ("forall", OutputLanguage::Chinese) => ("全称", "作为全称事实验证（Normal 省略细节）"),
        ("exist", OutputLanguage::English) => (
            "Existential",
            "Verified as an exist fact (details omitted in Normal)",
        ),
        ("exist", OutputLanguage::ChineseTraditional) => {
            ("存在", "已驗證存在命題（Normal 省略細節）")
        }
        ("exist", OutputLanguage::French) => (
            "Existentielle",
            "Vérifié comme proposition existentielle (détails omis en Normal)",
        ),
        ("exist", OutputLanguage::Russian) => (
            "Утверждение существования",
            "Проверено как утверждение существования (подробности опущены в Normal)",
        ),
        ("exist", OutputLanguage::Spanish) => (
            "Existencial",
            "Verificado como proposición existencial (detalles omitidos en Normal)",
        ),
        ("exist", OutputLanguage::Arabic) => (
            "وجودية",
            "تم التحقق كقضية وجودية (التفاصيل محذوفة في Normal)",
        ),
        ("exist", OutputLanguage::Japanese) => (
            "存在",
            "存在命題として検証しました（Normal では詳細を省略）",
        ),
        ("exist", OutputLanguage::Korean) => {
            ("존재", "존재 명제로 검증했습니다(Normal에서 상세 생략)")
        }
        ("exist", OutputLanguage::Vietnamese) => (
            "Tồn tại",
            "Đã kiểm chứng mệnh đề tồn tại (bỏ chi tiết trong Normal)",
        ),

        ("exist", OutputLanguage::Chinese) => ("存在", "作为存在事实验证（Normal 省略细节）"),
        ("chain", OutputLanguage::English) => (
            "Chain",
            "Verified as a chain fact (details omitted in Normal)",
        ),
        ("chain", OutputLanguage::ChineseTraditional) => {
            ("鏈式命題", "已驗證鏈式命題（Normal 省略細節）")
        }
        ("chain", OutputLanguage::French) => (
            "Chaîne",
            "Vérifié comme proposition en chaîne (détails omis en Normal)",
        ),
        ("chain", OutputLanguage::Russian) => (
            "Цепочка",
            "Проверено как цепное утверждение (подробности опущены в Normal)",
        ),
        ("chain", OutputLanguage::Spanish) => (
            "Cadena",
            "Verificado como proposición en cadena (detalles omitidos en Normal)",
        ),
        ("chain", OutputLanguage::Arabic) => {
            ("سلسلة", "تم التحقق كقضية سلسلة (التفاصيل محذوفة في Normal)")
        }
        ("chain", OutputLanguage::Japanese) => (
            "連鎖命題",
            "連鎖命題として検証しました（Normal では詳細を省略）",
        ),
        ("chain", OutputLanguage::Korean) => (
            "연쇄 명제",
            "연쇄 명제로 검증했습니다(Normal에서 상세 생략)",
        ),
        ("chain", OutputLanguage::Vietnamese) => (
            "Chuỗi",
            "Đã kiểm chứng mệnh đề chuỗi (bỏ chi tiết trong Normal)",
        ),

        ("chain", OutputLanguage::Chinese) => ("链式", "作为链式事实验证（Normal 省略细节）"),
        (_, OutputLanguage::English) => (
            "Compound fact",
            "Verified as a compound fact (details omitted in Normal)",
        ),
        (_, OutputLanguage::ChineseTraditional) => {
            ("複合命題", "已驗證複合命題（Normal 省略細節）")
        }
        (_, OutputLanguage::French) => (
            "Proposition composée",
            "Vérifié comme proposition composée (détails omis en Normal)",
        ),
        (_, OutputLanguage::Russian) => (
            "Составное утверждение",
            "Проверено как составное утверждение (подробности опущены в Normal)",
        ),
        (_, OutputLanguage::Spanish) => (
            "Proposición compuesta",
            "Verificado como proposición compuesta (detalles omitidos en Normal)",
        ),
        (_, OutputLanguage::Arabic) => (
            "قضية مركبة",
            "تم التحقق كقضية مركبة (التفاصيل محذوفة في Normal)",
        ),
        (_, OutputLanguage::Japanese) => (
            "複合命題",
            "複合命題として検証しました（Normal では詳細を省略）",
        ),
        (_, OutputLanguage::Korean) => (
            "복합 명제",
            "복합 명제로 검증했습니다(Normal에서 상세 생략)",
        ),
        (_, OutputLanguage::Vietnamese) => (
            "Mệnh đề phức hợp",
            "Đã kiểm chứng mệnh đề phức hợp (bỏ chi tiết trong Normal)",
        ),

        (_, OutputLanguage::Chinese) => ("复合事实", "作为复合事实验证（Normal 省略细节）"),
    };
    let type_tag = match lang {
        OutputLanguage::English => "compound_fact",
        OutputLanguage::ChineseTraditional => "複合命題",
        OutputLanguage::French => "Proposition composée",
        OutputLanguage::Russian => "Составное утверждение",
        OutputLanguage::Spanish => "Proposición compuesta",
        OutputLanguage::Arabic => "قضية مركبة",
        OutputLanguage::Japanese => "複合命題",
        OutputLanguage::Korean => "복합 명제",
        OutputLanguage::Vietnamese => "Mệnh đề phức hợp",

        OutputLanguage::Chinese => "复合事实",
    };
    StmtWhyText {
        type_tag,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
