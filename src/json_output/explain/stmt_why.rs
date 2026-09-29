//! Localized why-text for statement kinds and compound facts.
//! All Chinese/English stmt copy lives here (not in execute/).

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
        ("let", OutputLanguage::Chinese) => ("define_obj", "赋值定义", "把名字绑定到一个良定的值"),
        ("have_in_nonempty", OutputLanguage::English) => (
            "define_obj",
            "Have from nonempty set",
            "Introduce an object from a nonempty carrier / parameter type",
        ),
        ("have_in_nonempty", OutputLanguage::Chinese) => {
            ("define_obj", "从非空集合引入", "从非空载体或参数类型引入对象")
        }
        ("have_equal", OutputLanguage::English) => (
            "define_obj",
            "Have with equality",
            "Introduce an object equal to a given well-defined value",
        ),
        ("have_equal", OutputLanguage::Chinese) => {
            ("define_obj", "带等式的 have", "引入与给定良定值相等的对象")
        }
        ("have_by_exist", OutputLanguage::English) => (
            "define_obj",
            "Have by existence",
            "Introduce objects from a proved existential fact",
        ),
        ("have_by_exist", OutputLanguage::Chinese) => {
            ("define_obj", "由存在性引入", "由已证明的存在事实引入对象")
        }
        ("obtain_exist", OutputLanguage::English) => (
            "define_obj",
            "Obtain from exist",
            "Obtain objects from a known existential fact",
        ),
        ("obtain_exist", OutputLanguage::Chinese) => {
            ("define_obj", "从存在事实取出", "从已知存在事实取出对象")
        }
        ("obtain_atomic", OutputLanguage::English) => (
            "define_obj",
            "Obtain from atomic",
            "Obtain an object from a known atomic fact",
        ),
        ("obtain_atomic", OutputLanguage::Chinese) => {
            ("define_obj", "从原子事实取出", "从已知原子事实取出对象")
        }
        ("have_by_preimage", OutputLanguage::English) => (
            "define_obj",
            "Have by preimage",
            "Introduce a preimage object for a function value",
        ),
        ("have_by_preimage", OutputLanguage::Chinese) => {
            ("define_obj", "由原像引入", "为函数值引入原像对象")
        }
        ("have_by_replacement", OutputLanguage::English) => (
            "define_obj",
            "Have by replacement",
            "Introduce an image set via the axiom of replacement",
        ),
        ("have_by_replacement", OutputLanguage::Chinese) => {
            ("define_obj", "由替换公理引入", "用替换公理引入像集")
        }

        // have fn
        ("have_fn_equal", OutputLanguage::English) => (
            "define_fn",
            "Have function equal",
            "Define a named function equal to an anonymous function",
        ),
        ("have_fn_equal", OutputLanguage::Chinese) => {
            ("define_fn", "定义函数（等式）", "用匿名函数定义具名函数")
        }
        ("have_fn_cases", OutputLanguage::English) => (
            "define_fn",
            "Have function by cases",
            "Define a function by case-by-case equalities",
        ),
        ("have_fn_cases", OutputLanguage::Chinese) => {
            ("define_fn", "分情况定义函数", "用分情况等式定义函数")
        }
        ("have_fn_forall_exist_unique", OutputLanguage::English) => (
            "define_fn",
            "Have function by unique existence",
            "Define a function from a forall-exist!-unique property",
        ),
        ("have_fn_forall_exist_unique", OutputLanguage::Chinese) => {
            ("define_fn", "由唯一存在定义函数", "由全称唯一存在性质定义函数")
        }
        ("have_fn_induc", OutputLanguage::English) => (
            "define_fn",
            "Have function by induction",
            "Define a function by induction on naturals",
        ),
        ("have_fn_induc", OutputLanguage::Chinese) => {
            ("define_fn", "归纳定义函数", "对自然数归纳定义函数")
        }

        // definitions
        ("def_prop", OutputLanguage::English) => ("definition", "Define prop", "Define a predicate"),
        ("def_prop", OutputLanguage::Chinese) => ("definition", "定义命题", "定义一个谓词"),
        ("def_abstract_prop", OutputLanguage::English) => {
            ("definition", "Define abstract prop", "Declare an abstract predicate")
        }
        ("def_abstract_prop", OutputLanguage::Chinese) => {
            ("definition", "定义抽象命题", "声明一个抽象谓词")
        }
        ("def_struct", OutputLanguage::English) => {
            ("definition", "Define struct", "Define a structure type")
        }
        ("def_struct", OutputLanguage::Chinese) => ("definition", "定义结构", "定义一个结构类型"),
        ("def_template", OutputLanguage::English) => {
            ("definition", "Define template", "Define a reusable template")
        }
        ("def_template", OutputLanguage::Chinese) => {
            ("definition", "定义模板", "定义可复用模板")
        }
        ("def_algo_cases", OutputLanguage::English) => {
            ("definition", "Define algo by cases", "Define an algorithm by cases")
        }
        ("def_algo_cases", OutputLanguage::Chinese) => {
            ("definition", "分情况定义算法", "用分情况定义算法")
        }
        ("def_algo_induc", OutputLanguage::English) => {
            ("definition", "Define algo by induction", "Define an algorithm by induction")
        }
        ("def_algo_induc", OutputLanguage::Chinese) => {
            ("definition", "归纳定义算法", "用归纳定义算法")
        }
        ("def_thm", OutputLanguage::English) => ("definition", "Define theorem", "Record a theorem"),
        ("def_thm", OutputLanguage::Chinese) => ("definition", "定义定理", "记录一个定理"),
        ("axiom", OutputLanguage::English) => ("definition", "Axiom", "Assume an axiom"),
        ("axiom", OutputLanguage::Chinese) => ("definition", "公理", "假定一条公理"),
        ("def_strategy", OutputLanguage::English) => {
            ("definition", "Define strategy", "Define a proof strategy")
        }
        ("def_strategy", OutputLanguage::Chinese) => {
            ("definition", "定义策略", "定义一个证明策略")
        }

        // witness / trust
        ("witness_exist", OutputLanguage::English) => {
            ("witness", "Witness exist", "Witness an existential fact")
        }
        ("witness_exist", OutputLanguage::Chinese) => ("witness", "见证存在", "为存在事实提供见证"),
        ("witness_atomic", OutputLanguage::English) => {
            ("witness", "Witness atomic", "Witness an atomic fact")
        }
        ("witness_atomic", OutputLanguage::Chinese) => {
            ("witness", "见证原子事实", "为原子事实提供见证")
        }
        ("witness_nonempty", OutputLanguage::English) => {
            ("witness", "Witness nonempty", "Witness that a set is nonempty")
        }
        ("witness_nonempty", OutputLanguage::Chinese) => {
            ("witness", "见证非空", "见证一个集合非空")
        }
        ("trust", OutputLanguage::English) => {
            ("trust", "Trust facts", "Trust-store facts without proof")
        }
        ("trust", OutputLanguage::Chinese) => ("trust", "信任事实", "不加证明地存入事实"),
        ("trust_have", OutputLanguage::English) => {
            ("trust", "Trust have", "Trust-introduce objects and body facts")
        }
        ("trust_have", OutputLanguage::Chinese) => {
            ("trust", "信任 have", "信任地引入对象与主体事实")
        }

        // by
        ("by_cases", OutputLanguage::English) => ("by", "By cases", "Prove by case analysis"),
        ("by_cases", OutputLanguage::Chinese) => ("by", "分情况证明", "用分情况分析证明"),
        ("by_contra", OutputLanguage::English) => {
            ("by", "By contradiction", "Prove by contradiction")
        }
        ("by_contra", OutputLanguage::Chinese) => ("by", "反证法", "用反证法证明"),
        ("by_def", OutputLanguage::English) => ("by", "By definition", "Prove by unfolding a definition"),
        ("by_def", OutputLanguage::Chinese) => ("by", "按定义", "展开定义来证明"),
        ("by_extension", OutputLanguage::English) => {
            ("by", "By set extension", "Prove set equality by extension")
        }
        ("by_extension", OutputLanguage::Chinese) => {
            ("by", "外延性", "用外延性证明集合相等")
        }
        ("by_fn_extension", OutputLanguage::English) => {
            ("by", "By function extension", "Prove function equality by extension")
        }
        ("by_fn_extension", OutputLanguage::Chinese) => {
            ("by", "函数外延性", "用函数外延性证明相等")
        }
        ("by_enumerate", OutputLanguage::English) => {
            ("by", "By finite enumeration", "Prove by enumerating a finite set")
        }
        ("by_enumerate", OutputLanguage::Chinese) => {
            ("by", "有限枚举", "枚举有限集来证明")
        }
        ("by_for", OutputLanguage::English) => ("by", "By for", "Prove inside a for-block"),
        ("by_for", OutputLanguage::Chinese) => ("by", "for 块", "在 for 块中证明"),
        ("by_thm", OutputLanguage::English) => ("by", "By theorem", "Apply a recorded theorem"),
        ("by_thm", OutputLanguage::Chinese) => ("by", "用定理", "应用已记录的定理"),
        ("by_induc", OutputLanguage::English) => ("by", "By induction", "Prove by induction"),
        ("by_induc", OutputLanguage::Chinese) => ("by", "归纳法", "用归纳法证明"),
        ("by_strong_induc", OutputLanguage::English) => {
            ("by", "By strong induction", "Prove by strong induction")
        }
        ("by_strong_induc", OutputLanguage::Chinese) => {
            ("by", "强归纳", "用强归纳法证明")
        }

        // register / release / proof block / command
        ("register_reflexive", OutputLanguage::English) => {
            ("register", "Register reflexive", "Register a reflexive property")
        }
        ("register_reflexive", OutputLanguage::Chinese) => {
            ("register", "注册自反", "注册自反性质")
        }
        ("register_symmetric", OutputLanguage::English) => {
            ("register", "Register symmetric", "Register a symmetric property")
        }
        ("register_symmetric", OutputLanguage::Chinese) => {
            ("register", "注册对称", "注册对称性质")
        }
        ("register_transitive", OutputLanguage::English) => {
            ("register", "Register transitive", "Register a transitive property")
        }
        ("register_transitive", OutputLanguage::Chinese) => {
            ("register", "注册传递", "注册传递性质")
        }
        ("release_thm", OutputLanguage::English) => {
            ("release", "Release theorem", "Release a theorem into the environment")
        }
        ("release_thm", OutputLanguage::Chinese) => ("release", "释放定理", "把定理释放到环境中"),
        ("release_struct", OutputLanguage::English) => {
            ("release", "Release struct", "Release a struct definition")
        }
        ("release_struct", OutputLanguage::Chinese) => {
            ("release", "释放结构", "释放结构定义")
        }
        ("release_obj", OutputLanguage::English) => {
            ("release", "Release object def", "Release an object definition")
        }
        ("release_obj", OutputLanguage::Chinese) => {
            ("release", "释放对象定义", "释放对象定义")
        }
        ("expand_range", OutputLanguage::English) => {
            ("release", "Expand range", "Expand a function range obligation")
        }
        ("expand_range", OutputLanguage::Chinese) => {
            ("release", "展开值域", "展开函数值域义务")
        }
        ("release_zorn", OutputLanguage::English) => {
            ("release", "Zorn lemma", "Release Zorn's lemma")
        }
        ("release_zorn", OutputLanguage::Chinese) => ("release", "Zorn 引理", "释放 Zorn 引理"),
        ("release_choice", OutputLanguage::English) => {
            ("release", "Axiom of choice", "Release the axiom of choice")
        }
        ("release_choice", OutputLanguage::Chinese) => {
            ("release", "选择公理", "释放选择公理")
        }
        ("release_regularity", OutputLanguage::English) => {
            ("release", "Regularity axiom", "Release the regularity axiom")
        }
        ("release_regularity", OutputLanguage::Chinese) => {
            ("release", "正则公理", "释放正则公理")
        }
        ("claim", OutputLanguage::English) => {
            ("proof_block", "Claim", "Prove a claim block and store its conclusions")
        }
        ("claim", OutputLanguage::Chinese) => {
            ("proof_block", "claim 块", "证明 claim 块并存储结论")
        }
        ("sketch", OutputLanguage::English) => {
            ("proof_block", "Sketch", "Run a sketch proof block")
        }
        ("sketch", OutputLanguage::Chinese) => ("proof_block", "sketch 块", "运行 sketch 证明块"),
        ("eval", OutputLanguage::English) => {
            ("command", "Eval", "Evaluate a closed numeric / algo expression")
        }
        ("eval", OutputLanguage::Chinese) => {
            ("command", "求值", "对封闭数值或算法表达式求值")
        }

        (_, OutputLanguage::English) => ("stmt", kind, "Statement completed"),
        (_, OutputLanguage::Chinese) => ("stmt", kind, "语句已完成"),
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
        ("and", OutputLanguage::Chinese) => ("合取", "作为合取事实验证（Normal 省略细节）"),
        ("or", OutputLanguage::English) => (
            "Disjunction",
            "Verified as a compound or-fact (details omitted in Normal)",
        ),
        ("or", OutputLanguage::Chinese) => ("析取", "作为析取事实验证（Normal 省略细节）"),
        ("forall", OutputLanguage::English) => (
            "Universal",
            "Verified as a forall fact (details omitted in Normal)",
        ),
        ("forall", OutputLanguage::Chinese) => ("全称", "作为全称事实验证（Normal 省略细节）"),
        ("exist", OutputLanguage::English) => (
            "Existential",
            "Verified as an exist fact (details omitted in Normal)",
        ),
        ("exist", OutputLanguage::Chinese) => ("存在", "作为存在事实验证（Normal 省略细节）"),
        ("chain", OutputLanguage::English) => (
            "Chain",
            "Verified as a chain fact (details omitted in Normal)",
        ),
        ("chain", OutputLanguage::Chinese) => ("链式", "作为链式事实验证（Normal 省略细节）"),
        (_, OutputLanguage::English) => (
            "Compound fact",
            "Verified as a compound fact (details omitted in Normal)",
        ),
        (_, OutputLanguage::Chinese) => ("复合事实", "作为复合事实验证（Normal 省略细节）"),
    };
    StmtWhyText {
        type_tag: "compound_fact",
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
